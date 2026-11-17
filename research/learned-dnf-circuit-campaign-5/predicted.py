"""Campaign 4: PREDICTED.json from the measures, by the rules of PREDICTION.md. No simulation is run.

  predicted.py instance ON_DIR OFF_DIR [SEED|none]        prints the prediction of one instance, for reading
  (the campaign's command, from the collected evidence of stages M and E, is in plan.py)

Everything is computed on the numbers written in PREDICTED.json: scores as integers in units of 1e-5 of the FIRE level
(theta = 100 000), dates as rationals in time units, rounded to 0.0001 unit (fractions.Fraction), never on floats
after rounding. The Lean file of the kernel gate (gate4.py) is written from the same numbers.

Amendment 3 (commit 41cf88b): every number that becomes an integer is computed in exact rationals. A measure is taken
at its exact value (`exact`: a float at its binary value, a Decimal read from a file at its decimal value); the
guarded tuple is the exact solution of the normal equations; rounding to the nearest is ties to even (`round` on a
Fraction); the noise terms are rounded up exactly (`ceil_sum_sqrt`). Floats remain in the geometric fit and M5 only.

Open points of the implementation, named here so that an amendment can change them in one place (reported to the
owner before any freeze): DURATION_C (c's read duration in the kernel's SlotTiming), RAIL, the per-cell budgets
(the largest per-read budget over a cell's training or test reads), EMPTY_IN_EPSILON.
"""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c4                                               # noqa: E402
from c4 import dnf                                      # noqa: E402

UNITS = 100000
THETA = UNITS
RAIL = 10 * THETA
DURATION_A, DURATION_C = 22, 19
SKEW_A, DEADLINE_A = F(1, 50), F(11, 10)
SKEW_C, DEADLINE_C = F(11, 10), F(11, 5)
ALLOWANCE_MV = F("0.030")
EMPTY_IN_EPSILON = True
GUARDED_READS_1 = ("empty", "port 1", "port 2", "both")      # the empty read identifies the help
GUARDED_READS_2 = ("empty", "port 1", "port 2")
READS = ("empty", "port 1", "port 2", "both")
SKEWED = "both, second 0.3 late"
LAYER1, LAYER2 = ("a", "b"), ("c",)
TARGET = dict(a=("A", "B"), b=("C", "D"))
PORT_OF = {n: p for n, (c, p) in dnf.INPUTS.items()}


def exact(x):
    """A measure as an exact rational: a float at its binary value, a Decimal at its decimal value (amendment 3, 1)."""
    if isinstance(x, (int, F)):
        return F(x)
    from decimal import Decimal
    if isinstance(x, (float, Decimal)):
        return F(x)
    raise TypeError(f"not a measure: {x!r}")


def q(x):
    """A date or latency rounded to 0.0001 unit, to the nearest, ties to even."""
    return F(round(exact(x) * 10000), 10000)


def zint(qpeak):
    """A score in integer units (Z times 100 000), to the nearest, ties to even."""
    return round(exact(qpeak) * UNITS)


def solve(rows, rhs):
    """The exact rational least-squares solution: the normal equations A^T A x = A^T b, by Gauss-Jordan elimination."""
    n = len(rows[0])
    a = [[sum(F(r[i]) * r[j] for r in rows) for j in range(n)] + [sum(F(r[i]) * y for r, y in zip(rows, rhs))] for i in range(n)]
    for c in range(n):
        piv = next(i for i in range(c, n) if a[i][c] != 0)
        a[c], a[piv] = a[piv], a[c]
        a[c] = [v / a[c][c] for v in a[c]]
        for i in range(n):
            if i != c and a[i][c] != 0:
                f = a[i][c]
                a[i] = [v - f * w for v, w in zip(a[i], a[c])]
    return [a[i][n] for i in range(n)]


def ceil_sum_sqrt(squares):
    """The least integer m >= 0 with m >= sqrt(X_1) + ... (one or two terms), decided on the exact rational squares
    (amendment 3, 2.5): one term, m^2 >= X; two terms, m^2 >= X, m^2 + X - Y >= 0 and (m^2 + X - Y)^2 >= 4 m^2 X. The
    float below is only a starting point; the result is decided by the exact predicate."""
    sq = [F(v) for v in squares]
    assert 1 <= len(sq) <= 2 and all(v >= 0 for v in sq)

    def enough(m):
        if m < 0:
            return False
        if len(sq) == 1:
            return m * m >= sq[0]
        X, Y = sq
        u = m * m + X - Y
        return m * m >= X and u >= 0 and u * u >= 4 * m * m * X
    m = max(0, int(sum(math.sqrt(v) for v in sq)) - 2)
    while not enough(m):
        m += 1
    while m > 0 and enough(m - 1):
        m -= 1
    return m


def mask_read(ports):
    """Read name of a set of ports of one cell."""
    return {(): "empty", (1,): "port 1", (2,): "port 2", (1, 2): "both"}[tuple(sorted(ports))]


# ---------------------------------------------------------------------------------------------------- the measures

def table(on_rows, off_rows):
    """(cell, stage, read) -> Z (int), fire, latency, fire bit of the guard-off probe; and the joint doses in mV."""
    on = {(r["cell"], r["stage"], r["read"]): r for r in on_rows}
    off = {(r["cell"], r["stage"], r["read"]): r for r in off_rows}
    t, dose, bad = {}, {}, []
    for c in c4.CELLS:
        for k in range(c4.STAGES):
            for name in READS + ((SKEWED,) if c == "c" else ()):
                key = (c, k, name)
                if key not in on or key not in off:
                    bad.append(f"missing read {key}")
                    continue
                z = zint(off[key]["q_peak"])
                if on[key]["fire"] != (z >= THETA):
                    bad.append(f"FIRE bit {on[key]['fire']} and Z = {z} disagree at {key}")
                t[key] = dict(Z=z, fire=on[key]["fire"], latency=None if on[key]["latency"] is None else q(on[key]["latency"]))
                if c == "c":    # every FIRE crossing of c over the whole physical slot (amendment 1, point 1)
                    t[key]["slot_latencies"] = [q(x) for x in on[key]["slot_latencies"]]
            jd = on.get((c, k, "joint dose"))
            if jd is None:
                bad.append(f"missing joint dose {(c, k)}")
            else:
                for p in (1, 2):
                    dose[(c, p, k)] = exact(jd["ports"][str(p)]["move_mV"])
    return t, dose, bad


def needs(t):
    """a, b: the least stage whose pair read fires; each line of c: the least stage whose single read fires."""
    first = lambda c, read: next((k for k in range(c4.STAGES) if t[(c, k, read)]["fire"]), None)
    return dict(a=first("a", "both"), b=first("b", "both"), c1=first("c", "port 1"), c2=first("c", "port 2"))


# -------------------------------------------------------------------------------------------------------- the fits

def geometric(t, c, stages, reads):
    """Z(S, k) = h + sum_j g_j r_j^k: h on a grid, g_j and r_j by least squares in log on the singles, h chosen by
    least squares over every fitted read. Returns (h, {port: (g, r)}) in units of the FIRE level."""
    best = None
    for h in np.linspace(0.05, 0.2, 301):
        x = {}
        for p in (1, 2):
            y = np.array([t[(c, k, f"port {p}")]["Z"] / UNITS - h for k in stages])
            if (y <= 0).any():
                break
            lr, lg = np.polyfit(np.array(stages, float), np.log(y), 1)
            x[p] = (float(np.exp(lg)), float(np.exp(lr)))
        if len(x) < 2:
            continue
        sse = sum((t[(c, k, r)]["Z"] / UNITS - geo_value(h, x, k, ports(r))) ** 2 for k in stages for r in reads)
        if best is None or sse < best[0]:
            best = (sse, float(h), x)
    return best[1], best[2]


def ports(read):
    return {"empty": (), "port 1": (1,), "port 2": (2,), "both": (1, 2)}[read]


def geo_value(h, x, k, ps):
    return h + sum(x[p][0] * x[p][1] ** k for p in ps)


def guarded(t, cells, Q, reads):
    """The guarded tuple of a layer, linear in the writes, by least squares over stages 0..Q: per cell a help, per
    port an initial gain, one dose for the layer; rounded to integer units."""
    names = [f"h_{c}" for c in cells] + [f"g_{c}{p}" for c in cells for p in (1, 2)] + ["d"]
    rows, rhs = [], []
    for c in cells:
        for k in range(Q + 1):
            for r in reads:
                row = [0.0] * len(names)
                row[names.index(f"h_{c}")] = 1
                for p in ports(r):
                    row[names.index(f"g_{c}{p}")] = 1
                    row[-1] += k
                rows.append(row)
                rhs.append(t[(c, k, r)]["Z"])
    x = solve(rows, rhs)
    v = {n: round(val) for n, val in zip(names, x)}
    return dict(help={c: v[f"h_{c}"] for c in cells}, gain={(c, p): v[f"g_{c}{p}"] for c in cells for p in (1, 2)}, dose=v["d"])


def G(tup, c, k, ps, writes=None):
    """Guarded score of cell c on ports ps, every port at k writes (or at writes[p])."""
    return tup["help"][c] + sum(tup["gain"][(c, p)] + tup["dose"] * (k if writes is None else writes[p]) for p in ps)


# ----------------------------------------------------------------------------------------------------- the budgets

def sensitivity(tup, dose, c, p):
    """Score per mV of stored voltage: the guarded score step of one dose over the measured dose in mV."""
    mv = sum(exact(dose[(c, p, k)]) for k in range(c4.STAGES)) / c4.STAGES
    return F(tup["dose"]) / mv


def noise_square(s, n, const):
    """(3 sigma)^2 of one port, exactly: 9 s^2 (w^2 + b^2 + n d^2), the constants at their decimal values."""
    w, b, d = (F(str(const[k])) for k in ("within_mV", "between_mV", "per_dose_mV"))
    return 9 * F(s) ** 2 * (w * w + b * b + n * d * d)


def read_budget(eps, sens, writes, kind, const):
    """kind 0: the noise-free budget; kind 3: K = 3. sens and writes per active port; two ports added linearly."""
    if kind == 0:
        return eps + math.ceil(ALLOWANCE_MV * sum(F(s) for s in sens))
    return eps + ceil_sum_sqrt([noise_square(s, n, const) for s, n in zip(sens, writes)])


# ---------------------------------------------------------------------------------------------- one instance

def instance(seed, t, dose, bad, const):
    """The prediction of one measured instance (`bad` empty) or why it is not measured."""
    out = dict(seed=seed, measured=not bad, why_not_measured=bad)
    if bad:
        return out
    n = needs(t)
    out["needs"] = n
    if None in n.values():
        out.update(eligible=False, why_not_eligible=["no firing stage up to 7: " + ", ".join(k for k, v in n.items() if v is None)])
        return out
    Q1, Q2 = max(n["a"], n["b"]) + 2, max(n["c1"], n["c2"]) + 2
    out.update(Q1=Q1, Q2=Q2)
    if Q1 > 7 or Q2 > 7:
        out.update(eligible=False, why_not_eligible=[f"Q1 = {Q1}, Q2 = {Q2}: above 7"])
        return out
    even, odd = [0, 2, 4, 6], [1, 3, 5, 7]
    fits, m5 = {}, {}
    for c in c4.CELLS:
        reads = ("port 1", "port 2") + (("both",) if c != "c" else ())
        h, x = geometric(t, c, even, reads)
        fits[c] = dict(h=h, gains={str(p): x[p] for p in (1, 2)})
        m5[c] = max(abs(t[(c, k, r)]["Z"] / UNITS - geo_value(h, x, k, ports(r))) for k in odd for r in reads)
    t1 = guarded(t, LAYER1, Q1, GUARDED_READS_1)
    t2 = guarded(t, LAYER2, Q2, GUARDED_READS_2)
    tup = dict(help={**t1["help"], **t2["help"]}, gain={**t1["gain"], **t2["gain"]}, dose=dict(a=t1["dose"], b=t1["dose"], c=t2["dose"]))
    lay = lambda c: dict(help=tup["help"], gain=tup["gain"], dose=tup["dose"][c])
    eps = {}
    for c, Q in (("a", Q1), ("b", Q1), ("c", Q2)):
        reads = (("port 1", "port 2", "both") if c != "c" else ("port 1", "port 2")) + (("empty",) if EMPTY_IN_EPSILON else ())
        eps[c] = max(abs(t[(c, k, r)]["Z"] - G(lay(c), c, k, ports(r))) for k in range(Q + 1) for r in reads)
    sens = {(c, p): sensitivity(lay(c), dose, c, p) for c in c4.CELLS for p in (1, 2)}
    out.update(geometric_fits=fits, validation_residual_M5=m5, guarded=dict(help=tup["help"], gain={f"{c}{p}": v for (c, p), v in tup["gain"].items()},
               dose=tup["dose"]), epsilon=eps, sensitivity={f"{c}{p}": v for (c, p), v in sens.items()})
    budgets = {}
    for K in (0, 3):
        b = {}
        for c in LAYER1:
            need = n[c]
            tr = max(read_budget(eps[c], [sens[(c, 1)], sens[(c, 2)]], [k, k], K, const) for k in range(need + 1))
            te = read_budget(eps[c], [sens[(c, 1)], sens[(c, 2)]], [need, need], K, const)
            b[c] = dict(training=tr, testing=te)
        n1, n2 = n["c1"], n["c2"]
        tr = max(read_budget(eps["c"], [sens[("c", p)]], [k], K, const) for p, nn in ((1, n1), (2, n2)) for k in range(nn + 1))
        te = read_budget(eps["c"], [sens[("c", 1)], sens[("c", 2)]], [n1, n2], K, const)
        b["c"] = dict(training=tr, testing=te)
        budgets[f"K{K}"] = b
    out["budgets"] = budgets
    gains = [tup["gain"][(c, p)] + tup["dose"][c] * (n[c] if c != "c" else n[f"c{p}"]) for c in c4.CELLS for p in (1, 2)]
    out["largest_gain_over_rail"] = str(F(max(gains), RAIL))     # amendment 1, point 2
    out["room"] = {f"K{K}": room(t, n, lay, budgets[f"K{K}"]) for K in (0, 3)}
    ok0 = all(v["all"] for v in out["room"]["K0"].values())
    out["eligible"] = ok0
    out["why_not_eligible"] = [] if ok0 else [f"{c}: {', '.join(v['without_room'])}" for c, v in out["room"]["K0"].items() if not v["all"]]
    out["room_at_K3"] = {c: v["all"] for c, v in out["room"]["K3"].items()}
    out["counts_N_out"] = dict(a=out["room_at_K3"]["a"], b=out["room_at_K3"]["b"],
                               c=out["room_at_K3"]["a"] and out["room_at_K3"]["b"] and out["room_at_K3"]["c"])
    out["learning_ports"] = learning_ports(out["room"]["K3"])
    z = dnf.zero_error(n["a"], n["b"], n["c1"], n["c2"])
    out["zero_error"] = dict(words=z["words"], tests=z["tests"])
    out["observation"] = observation(t, n, Q1, Q2)
    return out


def room(t, n, lay, b):
    """Room of every relevant read of each output, under the per-cell budgets b (training, testing)."""
    res = {}
    for c in LAYER1:
        need, tr, te = n[c], b[c]["training"], b[c]["testing"]
        L = lay(c)
        rr = {}
        for k in range(need):
            rr[f"training pair stage {k}, silent"] = G(L, c, k, (1, 2)) + tr < THETA and abs(t[(c, k, "both")]["Z"] - G(L, c, k, (1, 2))) <= tr
        rr[f"training pair stage {need}, FIRE"] = THETA + tr <= G(L, c, need, (1, 2)) and abs(t[(c, need, "both")]["Z"] - G(L, c, need, (1, 2))) <= tr
        for r in ("empty", "port 1", "port 2"):
            rr[f"test {r} stage {need}, silent"] = G(L, c, need, ports(r)) + te < THETA and abs(t[(c, need, r)]["Z"] - G(L, c, need, ports(r))) <= te
        rr[f"test pair stage {need}, FIRE"] = THETA + te <= G(L, c, need, (1, 2)) and abs(t[(c, need, "both")]["Z"] - G(L, c, need, (1, 2))) <= te
        res[c] = rr
    L = lay("c")
    tr, te = b["c"]["training"], b["c"]["testing"]
    n1, n2 = n["c1"], n["c2"]
    rr = {}
    for p, nn in ((1, n1), (2, n2)):
        for k in range(nn):
            rr[f"teaching line {p} stage {k}, silent"] = G(L, "c", k, (p,)) + tr < THETA and abs(t[("c", k, f"port {p}")]["Z"] - G(L, "c", k, (p,))) <= tr
        rr[f"teaching line {p} stage {nn}, FIRE"] = THETA + tr <= G(L, "c", nn, (p,)) and abs(t[("c", nn, f"port {p}")]["Z"] - G(L, "c", nn, (p,))) <= tr
    hi, lo = max(n1, n2), min(n1, n2)
    rr[f"test empty stage {hi}, silent"] = L["help"]["c"] + te < THETA and abs(t[("c", hi, "empty")]["Z"] - L["help"]["c"]) <= te
    z = {}
    for p, nn in ((1, n1), (2, n2)):
        z[p] = t[("c", nn, f"port {p}")]["Z"]
        rr[f"test line {p} alone stage {nn}, FIRE"] = z[p] - te >= THETA and z[p] >= G(L, "c", nn, (p,)) - te
    pair = min(t[("c", lo, "both")]["Z"], t[("c", lo, SKEWED)]["Z"])
    rr[f"test both lines stage {lo}, FIRE"] = rr[f"test line 1 alone stage {n1}, FIRE"] and rr[f"test line 2 alone stage {n2}, FIRE"] and pair >= max(z[1], z[2]) + te
    rr["guarded empty mask silent (Disjunctions.check)"] = L["help"]["c"] + te < THETA
    for p in (1, 2):
        rr[f"guarded gain of line {p} below the rail"] = L["gain"][("c", p)] + L["dose"] * n[f"c{p}"] < RAIL
    res["c"] = rr
    for c in LAYER1:
        res[c][f"guarded gains below the rail"] = all(lay(c)["gain"][(c, p)] + lay(c)["dose"] * n[c] < RAIL for p in (1, 2))
    return {c: dict(reads=v, all=all(v.values()), without_room=[k for k, x in v.items() if not x]) for c, v in res.items()}


def learning_ports(r3):
    """Own room and room up to each learning port, under beta_3. Ports of a, b: own reads are the pair reads of the
    cell (training); lines of c: its single reads (teaching). Room up to a line of c: own room, own room of both
    ports of its upstream cell, and room of that cell's trained pair read (its test pair read at the same stage)."""
    out = {}
    for c in LAYER1:
        own = all(v for k, v in r3[c]["reads"].items() if k.startswith("training"))
        for p in (1, 2):
            out[f"{c}{p}"] = dict(own_room=own, room_up_to=own)
    for p, src in ((1, "a"), (2, "b")):
        own = all(v for k, v in r3["c"]["reads"].items() if k.startswith(f"teaching line {p}"))
        upstream = out[f"{src}1"]["own_room"] and out[f"{src}2"]["own_room"] and next(v for k, v in r3[src]["reads"].items() if k.startswith("test pair"))
        out[f"c{p}"] = dict(own_room=own, room_up_to=own and upstream)
    return out


# --------------------------------------------------------------------------------------- the predicted observation

def observation(t, n, Q1, Q2):
    """The predicted observation, in the order of the kernel's TraceTables: dates (rationals, units) from the
    calendar, the routing delay 3/2, one emission per predicted FIRE at its start plus the measured latency, scores
    from the calibration. Serialized as strings of rationals and integers."""
    Z = lambda c, k, r: t[(c, k, r)]["Z"]
    def lat(c, k, r):
        """The measured guard-on latency of a predicted FIRE; a predicted FIRE without one is an error."""
        v = t[(c, k, r)]["latency"]
        if v is None:
            raise ValueError(f"a predicted FIRE without a measured latency: {(c, k, r)}")
        return q(v)
    obs = dict(firstTrain=[], teach=[], secondTrain=[], firstTest={}, secondTest={}, scores={})

    def emc(k, r, start, fire):
        """The emissions of a read of c: every FIRE crossing of its calibration read over the whole physical slot
        (amendment 1, point 1), at the read's start plus its latency. A table without that record (phase 0's
        CALIBRATION.json, for the cases) gives the one in-window FIRE of a predicted FIRE."""
        sl = t[("c", k, r)].get("slot_latencies")
        if sl is None:
            return [start + lat("c", k, r)] if fire else []
        if fire:
            assert lat("c", k, r) in sl, (k, r)
        return [start + x for x in sl]

    def rd(start, arrivals, emissions, value):
        return dict(start=str(start), arrivals=[None if a is None else str(a) for a in arrivals], emissions=[str(e) for e in emissions], value=int(value))

    def arr1(start, active):
        return [start if x in active else None for x in "ABCD"]
    for r in range(Q1 + 1):
        start = F(c4.SLOT * r)
        row = []
        for c in LAYER1:
            k = min(r, n[c])
            fire = r >= n[c]
            row.append(rd(start, arr1(start, TARGET[c]), [start + lat(c, k, "both")] if fire else [], Z(c, k, "both")))
        obs["firstTrain"].append(row)
    t0 = c4.SLOT * (Q1 + 1)
    writes = {1: 0, 2: 0}
    for m in range(2 * (Q2 + 1)):
        line, p = ("a", 1) if m % 2 == 0 else ("b", 2)
        start = F(t0 + c4.SLOT * m)
        row, emission = [], None
        for c in LAYER1:
            if c == line:
                e = start + lat(c, n[c], "both")
                emission = e
                row.append(rd(start, arr1(start, TARGET[line]), [e], Z(c, n[c], "both")))
            else:
                row.append(rd(start, arr1(start, TARGET[line]), [], Z(c, n[c], "empty")))
        obs["teach"].append(row)
        arrive = emission + F(3, 2)
        k = writes[p]
        fire = k >= n[f"c{p}"]
        arrivals = [arrive if x == p else None for x in (1, 2)]
        obs["secondTrain"].append(rd(arrive, arrivals, emc(k, f"port {p}", arrive, fire), Z("c", k, f"port {p}")))
        if not fire:
            writes[p] += 1
    t1 = t0 + c4.SLOT * 2 * (Q2 + 1)
    n1, n2 = n["c1"], n["c2"]
    for i, x in enumerate(dnf.patterns()):
        key = "".join(sorted(x)) or "-"
        start = F(t1 + c4.SLOT * i)
        row, em = [], {}
        for c in LAYER1:
            mine = tuple(sorted(PORT_OF[v] for v in x if dnf.INPUTS[v][0] == c))
            read = mask_read(mine)
            fire = read == "both"
            e = [start + lat(c, n[c], "both")] if fire else []
            em[c] = e[0] if e else None
            row.append(rd(start, arr1(start, x), e, Z(c, n[c], read)))
        obs["firstTest"][key] = row
        scores = {"-": Z("c", max(n1, n2), "empty"), "1": Z("c", n1, "port 1"), "2": Z("c", n2, "port 2"),
                  "12": min(Z("c", min(n1, n2), "both"), Z("c", min(n1, n2), SKEWED))}
        obs["scores"][key] = scores
        arrivals = [None if em["a"] is None else em["a"] + F(3, 2), None if em["b"] is None else em["b"] + F(3, 2)]
        got = [a for a in arrivals if a is not None]
        mask = "".join(str(p) for p, a in zip((1, 2), arrivals) if a is not None) or "-"
        if not got:
            obs["secondTest"][key] = rd(start + F(3, 2), arrivals, emc(max(n1, n2), "empty", start + F(3, 2), False), scores["-"])
        else:
            first, last = min(got), max(got)
            if mask == "12":
                skewed = last - first > F(15, 100)
                e = emc(min(n1, n2), SKEWED if skewed else "both", first, True)
            else:
                pp = int(mask)
                e = emc(n[f"c{pp}"], f"port {pp}", first, True)
            obs["secondTest"][key] = rd(first, arrivals, e, scores[mask])
    return obs


def load(on_dir, off_dir):
    """The calibration reads of an instance from its two collected runs."""
    sys.path.insert(0, str(HERE.parent / "network-circuit"))
    import measure
    import reads4
    rows = {}
    for g, d in (("on", on_dir), ("off", off_dir)):
        d = Path(d)
        rec = json.loads((d / "record.json").read_text())
        result = json.loads((d / "evidence" / "result.json").read_text())
        tr = measure.Trace(d / "evidence" / "trace.raw")
        rows[g] = reads4.calibration_reads(tr, result, rec["reads"])
    return rows["on"], rows["off"]


# ------------------------------------------------------------------------------- the pipeline after stage M and E

def state_records(*dirs):
    """Every run record of the kit in the collected folders: id -> the record, with the folder of the run."""
    out = {}
    for d in dirs:
        for st in Path(d).rglob("STATE.json"):
            for r in json.loads(st.read_text())["records"]:
                out[r["id"]] = dict(r, folder=str(st.parent / r["id"]))
    return out


def counts(rec):
    """A run counts when the launcher recorded it complete and its own record says it reached its last date."""
    if rec is None or rec.get("status") != "complete":
        return False
    own = Path(rec["folder"]) / "record.json"
    return own.exists() and json.loads(own.read_text()).get("reached_its_last_date") is True


def before_m(repo=HERE):
    """The record before stage M: the JSON block of BEFORE_M.md, which plan.py writes."""
    import plan
    return plan.read_before_m(Path(repo) / "BEFORE_M.md")


def measures(before, dirs):
    """Per instance of BEFORE_M.md: its two calibration runs, whether it is measured (and why not), its needs."""
    recs = state_records(*dirs)
    out = []
    for seed in sorted((s for m in ("a", "b") for s in before["seeds"][m]), key=lambda s: -1 if s is None else s):
        mach = before.get("machine_of", {}).get(str(seed)) or c4.machine_of(seed, before["I"])   # machine_of: the rehearsal's nominal cell
        on, off = (recs.get(f"{mach}-{seed}-cal-{g}") for g in ("on", "off"))
        x = dict(seed=seed, machine=mach)
        if not (counts(on) and counts(off)):
            x.update(measured=False, why_not_measured=["a calibration run does not count"])
        else:
            t, dose, bad = table(*load(on["folder"], off["folder"]))
            x.update(measured=not bad, why_not_measured=bad, needs=needs(t) if not bad else None,
                     calibration=dict(on=on["folder"], off=off["folder"]))
        out.append(x)
    return out


def extraction_of(seed, mach, recs):
    """The merged extraction of an instance from its per-output runs (stage E), or why there is none."""
    import plan
    sys.path.insert(0, str(HERE / "noise"))
    import devnoise
    parts, missing = [], []
    for r in plan.extract_runs(seed, mach, False):
        rec = recs.get(r["id"])
        if not counts(rec):
            missing.append(r["id"])
            continue
        parts.append(json.loads((Path(rec["folder"]) / "part.json").read_text()))
    if missing:
        return None, missing
    section = "tt" if seed is None else c4.SECTION         # the nominal cell (rehearsal) has no mismatch, as run4.py runs it
    return devnoise.merge(parts, section, seed, list(c4.CELLS), list(noisemodel_states())), []


def noisemodel_states():
    import noisemodel
    return noisemodel.MODEL_STATES


def extraction_check(ex):
    """The rule for campaign 4 of the noise study's criteria (section 2): V2, V2b and the 1 uV isolation check, by
    the noise study's own compare.py (noise/compare.py, unchanged copy)."""
    sys.path.insert(0, str(HERE / "noise"))
    import compare
    v2, v2b = compare.v2(ex), compare.v2b(ex)
    return dict(V2=v2["all_pass"], V2b=v2b["all_pass"], isolation=v2["op_pass"] is True,
                failing_outputs=[r for r in v2["outputs"] if not r["pass"]], worst_V2b=v2b["worst"],
                passed=v2["all_pass"] and v2b["all_pass"] and v2["op_pass"] is True)


def control_instance(instances):
    """Among the eligible instances, the one whose layer-1 pair at stage 0 scores highest (the higher of a and b),
    the lowest seed on a tie."""
    el = [x for x in instances if x.get("eligible")]
    if not el:
        return None
    best = lambda x: max(int(x["observation"]["firstTrain"][0][i]["value"]) for i in (0, 1))
    return min(el, key=lambda x: (-best(x), x["seed"]))["seed"]


def predictions(before, measure_dirs, extraction_dirs=(), rehearsal=None, extraction_path=lambda seed: f"{c4.BASE}/extractions/EXTRACTION_{seed}.json"):
    """PREDICTED.json (as a dict) and the merged extractions to commit beside it (path -> dict)."""
    import plan
    const = {k: before["constants"][k] for k in c4.DECISION5}
    model = before["noise_model"]
    recs = state_records(*measure_dirs, *extraction_dirs)
    instances, files, extractions = [], {}, {}
    for m in measures(before, measure_dirs):
        if not m["measured"]:
            instances.append(dict(seed=m["seed"], machine=m["machine"], measured=False, why_not_measured=m["why_not_measured"]))
            continue
        t, dose, bad = table(*load(m["calibration"]["on"], m["calibration"]["off"]))
        x = dict(instance(m["seed"], t, dose, bad, const), machine=m["machine"])
        instances.append(x)
        if model == "device":
            ex, missing = extraction_of(m["seed"], m["machine"], recs)
            if ex is None:
                extractions[str(m["seed"])] = dict(passed=False, why="extraction runs that do not count: " + ", ".join(missing))
            else:
                path = extraction_path(m["seed"])
                text = json.dumps(ex, indent=1) + "\n"
                files[path] = text
                import hashlib
                extractions[str(m["seed"])] = dict(extraction_check(ex), path=path, sha256=hashlib.sha256(text.encode()).hexdigest())
    control = control_instance(instances)
    cost = plan.costs(before)
    runs = []
    for x in instances:
        if not x["measured"]:
            continue
        nd = plan.calendar_needs((x["needs"]["a"], x["needs"]["b"], x["needs"]["c1"], x["needs"]["c2"]))
        runs.append(plan.with_limits(plan.network_run(x["seed"], x["machine"], nd, "quiet", model), cost, model, rehearsal))
        if control is not None and x["seed"] == control:
            runs.append(plan.with_limits(plan.network_run(x["seed"], x["machine"], nd, "untrained", model), cost, model, rehearsal))
    for k in (1, 2, 3):
        for x in instances:
            if not x["measured"]:
                continue
            ex = extractions.get(str(x["seed"]))
            if model == "device" and not (ex and ex["passed"]):
                continue                 # no noisy runs: missing (PREDICTION.md, Noise-model extraction)
            nd = plan.calendar_needs((x["needs"]["a"], x["needs"]["b"], x["needs"]["c1"], x["needs"]["c2"]))
            r = plan.network_run(x["seed"], x["machine"], nd, f"n{k}", model, dict(path=ex["path"], sha256=ex["sha256"]) if model == "device" else None)
            runs.append(dict(plan.with_limits(r, cost, model, rehearsal), noise_seed=c4.noise_seed(x["seed"], k), position=c4.POSITIONS[f"n{k}"]))
    for r in runs:
        r.setdefault("position", c4.POSITIONS[r["scenario"]])
    return dict(what="the predictions of campaign 4 (PREDICTION.md, amendments 1 to 3), written by predicted.py; no network run exists when "
                     "this file is written", I=before["I"], noise_model=model, constants=const, before_m_sha256=before["sha256"],
                instances=instances, extractions=extractions, control_instance=control, network_runs=runs,
                missing_noisy_runs=[f"{x['machine']}-{x['seed']}-n{k}" for x in instances if x["measured"] and model == "device"
                                    and not extractions.get(str(x["seed"]), {}).get("passed") for k in (1, 2, 3)]), files


def main():
    if sys.argv[1] == "predictions":       # predicted.py predictions OUT_DIR MEASURES_DIR... [--extractions DIR...] [--rehearsal REHEARSAL.json]
        args = sys.argv[3:]
        reh = None
        if "--rehearsal" in args:
            i = args.index("--rehearsal")
            reh = json.loads(Path(args[i + 1]).read_text())["limits_basis"]
            args = args[:i] + args[i + 2:]
        ext = []
        if "--extractions" in args:
            i = args.index("--extractions")
            args, ext = args[:i], args[i + 1:]
        print(c4.require_pinned())
        out = Path(sys.argv[2])
        res, files = predictions(before_m(out / c4.BASE), args, ext, reh)
        for path, text in files.items():
            (out / path).parent.mkdir(parents=True, exist_ok=True)
            (out / path).write_text(text)
        (out / c4.BASE).mkdir(parents=True, exist_ok=True)
        (out / c4.BASE / "PREDICTED.json").write_text(json.dumps(res, indent=1, default=str) + "\n")
        return
    if sys.argv[1] == "instance":
        on, off = load(sys.argv[2], sys.argv[3])
        seed = None if len(sys.argv) < 5 or sys.argv[4] == "none" else int(sys.argv[4])
        t, dose, bad = table(on, off)
        r = instance(seed, t, dose, bad, c4.DECISION5)
        print(json.dumps({k: v for k, v in r.items() if k != "observation"}, indent=1, default=str))


if __name__ == "__main__":
    main()
