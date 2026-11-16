"""Campaign 4: PREDICTED.json from the measures, by the rules of PREDICTION.md. No simulation is run.

  predicted.py instance ON_DIR OFF_DIR [SEED|none]        prints the prediction of one instance, for reading
  (the campaign's command, from the collected evidence of stages M and E, is in plan.py)

Everything is computed on the numbers written in PREDICTED.json: scores as integers in units of 1e-5 of the FIRE level
(theta = 100 000), dates as rationals in time units, rounded to 0.0001 unit (fractions.Fraction), never on floats
after rounding. The Lean file of the kernel gate (gate4.py) is written from the same numbers.

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
ALLOWANCE_MV = 0.030
EMPTY_IN_EPSILON = True
GUARDED_READS_1 = ("empty", "port 1", "port 2", "both")      # the empty read identifies the help
GUARDED_READS_2 = ("empty", "port 1", "port 2")
READS = ("empty", "port 1", "port 2", "both")
SKEWED = "both, second 0.3 late"
LAYER1, LAYER2 = ("a", "b"), ("c",)
TARGET = dict(a=("A", "B"), b=("C", "D"))
PORT_OF = {n: p for n, (c, p) in dnf.INPUTS.items()}


def q(x):
    return F(round(x * 10000), 10000)


def zint(qpeak):
    return int(round(qpeak * UNITS))


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
                t[key] = dict(Z=z, fire=on[key]["fire"], latency=None if on[key]["latency"] is None else float(q(on[key]["latency"])))
            jd = on.get((c, k, "joint dose"))
            if jd is None:
                bad.append(f"missing joint dose {(c, k)}")
            else:
                for p in (1, 2):
                    dose[(c, p, k)] = jd["ports"][str(p)]["move_mV"]
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
    x, *_ = np.linalg.lstsq(np.array(rows), np.array(rhs, float), rcond=None)
    v = {n: int(round(val)) for n, val in zip(names, x)}
    return dict(help={c: v[f"h_{c}"] for c in cells}, gain={(c, p): v[f"g_{c}{p}"] for c in cells for p in (1, 2)}, dose=v["d"])


def G(tup, c, k, ps, writes=None):
    """Guarded score of cell c on ports ps, every port at k writes (or at writes[p])."""
    return tup["help"][c] + sum(tup["gain"][(c, p)] + tup["dose"] * (k if writes is None else writes[p]) for p in ps)


# ----------------------------------------------------------------------------------------------------- the budgets

def sensitivity(tup, dose, c, p):
    """Score per mV of stored voltage: the guarded score step of one dose over the measured dose in mV."""
    mv = np.mean([dose[(c, p, k)] for k in range(c4.STAGES)])
    return tup["dose"] / mv


def sigma_term(s, n, const):
    return s * math.sqrt(const["within_mV"] ** 2 + const["between_mV"] ** 2 + n * const["per_dose_mV"] ** 2)


def read_budget(eps, sens, writes, kind, const):
    """kind 0: the noise-free budget; kind 3: K = 3. sens and writes per active port; two ports added linearly."""
    if kind == 0:
        return eps + math.ceil(ALLOWANCE_MV * sum(sens))
    return eps + math.ceil(3 * sum(sigma_term(s, n, const) for s, n in zip(sens, writes)))


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
    lat = lambda c, k, r: q(t[(c, k, r)]["latency"]) if t[(c, k, r)]["latency"] is not None else F(1, 2)
    obs = dict(firstTrain=[], teach=[], secondTrain=[], firstTest={}, secondTest={}, scores={})

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
        obs["secondTrain"].append(rd(arrive, arrivals, [arrive + lat("c", k, f"port {p}")] if fire else [], Z("c", k, f"port {p}")))
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
            obs["secondTest"][key] = rd(start + F(3, 2), arrivals, [], scores["-"])
        else:
            first, last = min(got), max(got)
            if mask == "12":
                skewed = last - first > F(15, 100)
                e = first + lat("c", min(n1, n2), SKEWED if skewed else "both")
            else:
                pp = int(mask)
                e = first + lat("c", n[f"c{pp}"], f"port {pp}")
            obs["secondTest"][key] = rd(first, arrivals, [e], scores[mask])
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


def main():
    if sys.argv[1] == "instance":
        on, off = load(sys.argv[2], sys.argv[3])
        seed = None if len(sys.argv) < 5 or sys.argv[4] == "none" else int(sys.argv[4])
        t, dose, bad = table(on, off)
        r = instance(seed, t, dose, bad, c4.DECISION5)
        print(json.dumps({k: v for k, v in r.items() if k != "observation"}, indent=1, default=str))


if __name__ == "__main__":
    main()
