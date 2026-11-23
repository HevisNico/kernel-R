"""M3: the guarded fit, the budgets and the per-cell verdicts at K0 and K3, from an instrumented record. Development only.

Exact rationals throughout (Fractions), rounding to the nearest, ties to even, as campaign 5's predicted.py (P).
The family method is followed, adapted to one cell at a time:

1. **Scores.** The mapped Z of scores.py (anchors at the scanned crossing), for every mask of every fitted state.
2. **The guarded tuple of a cell** (P.guarded, per cell): help, the gain of each used port and one dose, by exact
   least squares over the cell's training states (rounds 0..need of each group) and the masks of its kind:
   both {}, {1}, {2}, {1,2}; copy {}, {1}; either {}, {1}, {2}. The writes of a state are Lean's
   `writesBefore` (silent rounds with an arrival on the port).
3. **ε** (P.instance): the largest |Z − G| over the fitted rows.
4. **Sensitivity** (P.sensitivity): the guarded dose over the port's measured dose D_p in mV.
5. **Budgets** (P.read_budget with c4.DECISION5): K = 0: ε + ⌈0.030 mV · Σ s⌉; K = 3: ε + ⌈3σ⌉ with
   σ² = s² (w² + b² + n d²) per port; per gate as CALIBRATION_PROPOSAL.md (c); then the added terms (DEVIATIONS).
6. **The Lean cell**: gate, initialGain = the fitted gains, help, threshold θ, dose, trainError, testError, maxWrites
   (rounds run − 1, least over the groups), rail 10 θ. Its `Cell.Valid` is mirrored clause by clause (the room).
7. **The calibration mirror**: every lesson read (AdditiveSlot with trainError at writesBefore) and every test and
   replay read (FiringSlot or AdditiveSlot with testError at settledWrites), with the exact decoder fired = (θ ≤ Z).
   The timing clauses are measure.py's, not repeated here.

DEVIATIONS of the M2 scans from campaign 6's scan6, and how each enters the budget (H_dev added to both errors):
  D1 tolerance 10 µV instead of 2 µV: the bracket is kept at the measured states, so s* and h do not depend on it.
     Term 0. Bound: every scan read's measured state is used, not its target (record `reads[].s`).
  D2 leak undershoot 4 % and step up to 1.5 mV: they change how a state is reached, not the state read. Term 0.
     Bound: the same as D1. What they can change is the stored voltage between the u window and the read, the
     drift: measured (D5).
  D3 no ascent from s = 0: the bracket starts from training reads made under network timing. Bound: a bracket must
     have a scan-native FIRE and a scan-native silence (reads of the scan itself). Otherwise the cell is
     NOT MEASURED. No widening, no re-scan.
  D4 parallel scans: H_D4 = ceil(k d |s*_par - s*_solo|) (k = 2 for a both cell), with the largest difference over
     the cell's groups from the run's own solo scans (lcal.py run ... solo=1), else the constant d4_stage of
     calibration.json; with neither, the cell is not measured.
  D5 drift between the u window (35 µs before T − 3 tu) and the read: H_drift = ⌈Σ_p d · max |Δu_p| / D_p⌉, with
     max |Δu_p| the largest change of the port's u over a read-only slot of the run (tests, and scan slots with
     a read and no tail leak). It is the same measure as campaign 5's u_before; it is added here because the scan
     brackets rest on it.
"""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import scores as scoremod  # noqa: E402
import spec as specmod  # noqa: E402

CAL = json.loads((HERE / "calibration.json").read_text())
THETA = scoremod.THETA
RAIL = 10 * THETA
ALLOWANCE_MV = F("0.030")
DECISION5 = dict(between_mV=F("0.111"), within_mV=F("0.094"), per_dose_mV=F("0.009"))   # c4.DECISION5, decimal values
MASKS = dict(both=[(), (1,), (2,), (1, 2)], copy=[(), (1,)], either=[(), (1,), (2,)])
PORTS_USED = dict(both=(1, 2), copy=(1,), either=(1, 2))


# ---------------------------------------------------------------------------------------------- P's arithmetic

def solve(rows, rhs):
    """Exact least squares by the normal equations (P.solve)."""
    n = len(rows[0])
    a = [[sum(F(r[i]) * F(r[j]) for r in rows) for j in range(n)] + [sum(F(r[i]) * F(y) for r, y in zip(rows, rhs))]
         for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if a[r][c] != 0)
        a[c], a[p] = a[p], a[c]
        a[c] = [v / a[c][c] for v in a[c]]
        for r in range(n):
            if r != c and a[r][c] != 0:
                a[r] = [x - a[r][c] * y for x, y in zip(a[r], a[c])]
    return [a[i][n] for i in range(n)]


def ceil_sum_sqrt(squares):
    """P.ceil_sum_sqrt: least integer m >= sqrt(X1) (+ sqrt(X2)), decided exactly."""
    sq = [F(v) for v in squares]

    def enough(m):
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


def read_budget(eps, sens, writes, K):
    """P.read_budget with c4.DECISION5."""
    if K == 0:
        return eps + math.ceil(ALLOWANCE_MV * sum(sens))
    w, b, d = DECISION5["within_mV"], DECISION5["between_mV"], DECISION5["per_dose_mV"]
    return eps + ceil_sum_sqrt([9 * s * s * (w * w + b * b + n * d * d) for s, n in zip(sens, writes)])


# ---------------------------------------------------------------------------------------------- the cell model (Lean)

def group_mask(gate, g):
    return specmod.GROUP_MASK[gate][g]


def model_score(p, writes, mask):
    """Cell.score: help + sum over the mask's ports of (initialGain + dose * writes)."""
    return p["help"] + sum(p["gain"][q] + p["dose"] * writes[q] for q in mask)


def group_writes(p, g, k):
    m = group_mask(p["gate"], g)
    return {q: (k if m[q - 1] else 0) for q in (1, 2)}


def stop(p, g):
    m = tuple(q for q in (1, 2) if group_mask(p["gate"], g)[q - 1])
    for k in range(p["maxWrites"] + 1):
        if THETA <= model_score(p, group_writes(p, g, k), m):
            return k
    return p["maxWrites"] + 1


def expected_writes(p):
    out = {1: 0, 2: 0}
    for g in range(specmod.GROUPS[p["gate"]]):
        for q, v in group_writes(p, g, stop(p, g)).items():
            out[q] += v
    return out


def cell_valid(p):
    """Cell.Valid (LayeredMonotoneTarget.lean), clause by clause, with each clause's slack (> 0 holds, as an int)."""
    clauses = [("dose > 0", p["dose"])]
    for g in range(specmod.GROUPS[p["gate"]]):
        m = tuple(q for q in (1, 2) if group_mask(p["gate"], g)[q - 1])
        st = stop(p, g)
        clauses.append((f"g{g}: 0 < stop ≤ maxWrites (stop {st}, maxWrites {p['maxWrites']})",
                        1 if 0 < st <= p["maxWrites"] else 0))
        for k in range(min(st, p["maxWrites"] + 1)):
            clauses.append((f"g{g}: early silence k={k}", THETA - (model_score(p, group_writes(p, g, k), m) + p["trainError"])))
        if st <= p["maxWrites"]:
            clauses.append((f"g{g}: stop margin", model_score(p, group_writes(p, g, st), m) - (THETA + p["trainError"]) + 1))
    ew = expected_writes(p)
    for q in (1, 2):
        clauses.append((f"rail port {q}", RAIL - (p["gain"][q] + p["dose"] * ew[q])))
    for x in ((), (1,), (2,), (1, 2)):
        if not specmod.evaluate(p["gate"], tuple(q in x for q in (1, 2))):
            clauses.append((f"silent mask {x}", THETA - (model_score(p, ew, x) + p["testError"])))
    for y in {"both": [(1, 2)], "copy": [(1,)], "either": [(1,), (2,)]}[p["gate"]]:
        clauses.append((f"anchor {y}", model_score(p, ew, y) - (THETA + p["testError"]) + 1))
    return all(v > 0 for _, v in clauses), clauses


# ---------------------------------------------------------------------------------------------- one cell

def cell_fit(s, rec, readout, c, layer, idx):
    n = s["layers"][layer - 1][idx]
    gate = n["gate"]
    scans = rec["scans"]
    an_info = readout["cells"][c]
    out = dict(cell=c, gate=gate, measured=True, why_not_measured=[])
    # D3: a scan-native FIRE and silence in each group's scan
    for r in scans["cells"].get(c) or []:
        if not r.get("ok"):
            out["why_not_measured"].append(f"scan group {r['group']}: {r.get('why')}")
            continue
        fired = [x for x in r["reads"] if x["fired"]]
        silent = [x for x in r["reads"] if not x["fired"]]
        if not fired or not silent:
            out["why_not_measured"].append(
                f"D3: scan group {r['group']} has no scan-native {'FIRE' if not fired else 'silence'} "
                f"(its bracket end comes from a training read under network timing)")
    if not an_info["anchors"]:
        out["why_not_measured"].append("no anchors (a scan missing)")
    for g, q in an_info["question_1"].items():
        if not q["agree"]:
            out["why_not_measured"].append(f"question 1, group {g}: ceil(s*) {q['ceil_s_star']} vs first FIRE {q['first_firing_round']}")
    if out["why_not_measured"]:
        out["measured"] = False
        return out
    an = dict(an_info["anchors"])
    an["g"] = {int(k): v for k, v in an["g"].items()}
    D = {q: F(scans["D"][f"{c}/{q}"]) for q in PORTS_USED[gate] if f"{c}/{q}" in scans["D"]}
    u0 = scans["u0"][c]
    slots = rec["slots"]

    def w_at(slot_idx):
        return {q: (F(u0[q - 1]) - F(slots[slot_idx]["u"][c][q - 1])) / D[q] for q in D}
    # the lessons of this cell, per group, in round order
    les = {}
    for x in rec["lessons"]:
        if x["layer"] == layer and x["cell"] == idx:
            les.setdefault(x["group"], []).append(x)
    rounds = {g: sorted(v, key=lambda x: x["round"]) for g, v in les.items()}
    maxw = min(len(v) for v in rounds.values()) - 1

    def read_of(x):
        return next(r for r in slots[x["slot"]]["reads"] if r["layer"] == layer and r["index"] == idx)

    def observed(g, upto):
        """groupObserved: silent rounds before `upto` with an arrival on each port."""
        cnt = {1: 0, 2: 0}
        for x in rounds[g][:upto]:
            r = read_of(x)
            if r["emission"] is None:
                for q in (1, 2):
                    if r["arrivals"][q - 1] is not None:
                        cnt[q] += 1
        return cnt

    def writes_before(g, r):
        base = observed(0, maxw + 1) if g == 1 else {1: 0, 2: 0}
        cur = observed(g, r)
        return {q: base[q] + cur[q] for q in (1, 2)}
    settled = {q: sum(observed(g, maxw + 1)[q] for g in rounds) for q in (1, 2)}
    need = {g: next((i for i, x in enumerate(rounds[g]) if read_of(x)["emission"] is not None), None) for g in rounds}
    # the guarded fit over states 0..need of each group
    used = PORTS_USED[gate]
    names = ["help"] + [f"g{q}" for q in used] + ["dose"]
    rows, rhs, fitted = [], [], []
    for g in sorted(rounds):
        for r in range(need[g] + 1):
            x = rounds[g][r]
            wr = writes_before(g, r)
            w = w_at(x["slot"])
            for mask in MASKS[gate]:
                Z = scoremod.score(an, w, list(mask))
                row = [1] + [1 if q in mask else 0 for q in used] + [sum(wr[q] for q in mask)]
                rows.append(row)
                rhs.append(Z)
                fitted.append((g, r, mask, Z, wr))
    sol = solve(rows, rhs)
    v = {nm: round(val) for nm, val in zip(names, sol)}
    p = dict(gate=gate, help=v["help"], gain={1: v.get("g1", 0), 2: v.get("g2", 0)}, dose=v["dose"],
             threshold=THETA, maxWrites=maxw, rail=RAIL)
    eps = max(abs(Z - model_score(p, wr, mask)) for g, r, mask, Z, wr in fitted)
    D_mV = {q: D[q] * 1000 for q in D}
    sens = {q: F(p["dose"]) / D_mV[q] for q in D}
    # D5: drift over read-only slots
    drift = {q: F(0) for q in D}
    for i in range(len(slots) - 1):
        a, b = slots[i], slots[i + 1]
        if a["kind"] == "test" or (a["kind"] == "scan" and a["actions"].get(c, ["read"])[0] == "read"
                                   and not a.get("tail", {}).get(c) and c in a["actions"]):
            for q in D:
                drift[q] = max(drift[q], abs(F(b["u"][c][q - 1]) - F(a["u"][c][q - 1])))
    H_drift = math.ceil(sum(an["d"] * drift[q] / D[q] for q in D))
    # D4: parallel against solo scans of the same cell. With the run's own solo scans, the largest |s*_par - s*_solo|
    # over the cell's groups; without them, the constant d4_stage of calibration.json (bounded from the development
    # comparisons); with neither, the cell is not measured (D4 cannot be bounded).
    solo = (scans.get("solo") or {}).get("cells", {}).get(c)
    if solo is not None:
        par = {r["group"]: F(r["s_star"]) for r in scans["cells"][c] if r.get("ok")}
        sol = {r["group"]: F(r["s_star"]) for r in solo if r.get("ok")}
        if set(par) != set(sol):
            out["measured"] = False
            out["why_not_measured"].append("D4: a solo scan failed")
            return out
        d4_stage, d4_source = max(abs(par[g] - sol[g]) for g in par), "this run's solo scans"
    elif CAL.get("d4_stage") is not None:
        d4_stage, d4_source = F(str(CAL["d4_stage"])), "calibration.json d4_stage"
    else:
        out["measured"] = False
        out["why_not_measured"].append("D4: no solo scan and no d4_stage bound")
        return out
    H_D4 = math.ceil((2 if gate == "both" else 1) * an["d"] * d4_stage)
    H = an["H"]
    budgets = {}
    for K in (0, 3):
        if gate == "both":
            nn = need[0]
            tr = max(read_budget(eps, [sens[1], sens[2]], [k, k], K) for k in range(nn + 1))
            te = read_budget(eps, [sens[1], sens[2]], [nn, nn], K)
        elif gate == "copy":
            nn = need[0]
            tr = max(read_budget(eps, [sens[1]], [k], K) for k in range(nn + 1))
            te = read_budget(eps, [sens[1]], [nn], K)
        else:
            n1, n2 = need[0], need[1]
            tr = max(read_budget(eps, [sens[q]], [k], K) for q, nq in ((1, n1), (2, n2)) for k in range(nq + 1))
            te = max(max(read_budget(eps, [sens[q]], [nq], K) for q, nq in ((1, n1), (2, n2))),
                     read_budget(eps, [sens[1], sens[2]], [n1, n2], K))
        budgets[f"K{K}"] = dict(train_base=tr, test_base=te, H=H, H_drift=H_drift, D1=0, D2=0, H_D4=H_D4,
                                D4_stage=str(d4_stage), D4_source=d4_source,
                                trainError=tr + H + H_drift + H_D4, testError=te + H + H_drift + H_D4)
    out.update(anchors=dict(d=an["d"], g=an["g"], H=H), D_mV={q: str(D_mV[q]) for q in D},
               need={str(g): v for g, v in need.items()}, maxWrites=maxw, settled_writes=settled,
               guarded=dict(help=p["help"], gain=p["gain"], dose=p["dose"]), epsilon=eps,
               sensitivity={q: str(sens[q]) for q in sens}, drift_V={q: str(drift[q]) for q in drift},
               budgets=budgets)
    # verdicts at K0 and K3
    verdicts = {}
    for K in ("K0", "K3"):
        pk = dict(p, trainError=budgets[K]["trainError"], testError=budgets[K]["testError"])
        valid, clauses = cell_valid(pk)
        trained_ok = all(stop(pk, g) == need[g] for g in rounds)
        # training calibration: every lesson read r <= maxWrites
        res_tr, dec_tr = [], []
        for g in sorted(rounds):
            for r in range(maxw + 1):
                x = rounds[g][r]
                rd = read_of(x)
                mask = tuple(q for q in (1, 2) if rd["arrivals"][q - 1] is not None)
                Z = scoremod.score(an, w_at(x["slot"]), list(mask))
                fired = rd["emission"] is not None
                dec_tr.append(fired == (THETA <= Z))
                res_tr.append(pk["trainError"] - abs(Z - model_score(pk, writes_before(g, r), mask)))
        # read calibration: test reads and replay reads of this cell (in later lessons)
        res_te, dec_te, sub_ok, anc = [], [], [], []
        for i, sl in enumerate(slots):
            if sl["kind"] == "lesson" and sl["info"]["layer"] == layer:
                continue                                    # its own lessons (training) or a sibling's
            if sl["kind"] not in ("lesson", "test"):
                continue
            rd = next((r for r in sl["reads"] if r["layer"] == layer and r["index"] == idx), None)
            if rd is None:
                continue
            mask = tuple(q for q in (1, 2) if rd["arrivals"][q - 1] is not None)
            w = w_at(i)
            Z = scoremod.score(an, w, list(mask))
            fired = rd["emission"] is not None
            dec_te.append(fired == (THETA <= Z))
            if specmod.evaluate(gate, tuple(q in mask for q in (1, 2))):
                for y in ((), (1,), (2,), (1, 2)):
                    if set(y) <= set(mask):
                        Zy = scoremod.score(an, w, list(y))
                        if THETA <= Zy:
                            sub_ok.append(Zy <= Z)
                for y in {"both": [(1, 2)], "copy": [(1,)], "either": [(1,), (2,)]}[gate]:
                    if set(y) <= set(mask):
                        anc.append(scoremod.score(an, w, list(y)) - (model_score(pk, settled, y) - pk["testError"]))
            else:
                res_te.append(pk["testError"] - abs(Z - model_score(pk, settled, mask)))
        verdicts[K] = dict(
            valid=valid, trained_word_matches_model=trained_ok,
            training_calibration=all(dec_tr) and all(v >= 0 for v in res_tr),
            read_calibration=all(dec_te) and all(v >= 0 for v in res_te) and all(sub_ok) and all(v >= 0 for v in anc),
            failing=[f"{nm} (slack {sl})" for nm, sl in clauses if sl <= 0],
            min_slack={nm: sl for nm, sl in clauses},
            training_residual_min_slack=min(res_tr) if res_tr else None, decoder_exact_training=all(dec_tr),
            test_residual_min_slack=min(res_te) if res_te else None, decoder_exact_reads=all(dec_te),
            anchor_min_slack=min(anc) if anc else None)
        verdicts[K]["ok"] = (valid and trained_ok and verdicts[K]["training_calibration"] and verdicts[K]["read_calibration"])
    out["verdicts"] = verdicts
    out["lean_cell"] = {K: dict(p, trainError=budgets[K]["trainError"], testError=budgets[K]["testError"]) for K in ("K0", "K3")}
    return out


def instance_fit(s, rec):
    readout = scoremod.readout(s, rec)
    cells = []
    for k, nodes in enumerate(s["layers"], start=1):
        for i, _ in enumerate(nodes):
            cells.append(cell_fit(s, rec, readout, f"c{k}_{i}", k, i))
    eligible = all(c["measured"] and c["verdicts"]["K0"]["ok"] for c in cells)
    room = all(c["measured"] and c["verdicts"]["K3"]["ok"] for c in cells)
    return dict(tag=s["tag"], seed=rec["seed"], measured=all(c["measured"] for c in cells), eligible_K0=eligible,
                room_K3=room, decoder_failures_outside_H=len(readout["decoder_failures"]), cells=cells)


def js(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {str(k): js(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [js(v) for v in x]
    return x


def main(spec_path, outdir):
    s = specmod.load(spec_path)
    import records
    rec = records.load(outdir)
    r = instance_fit(s, rec)
    (Path(outdir) / "fit.json").write_text(json.dumps(js(r), indent=1) + "\n")
    return r


if __name__ == "__main__":
    r = main(sys.argv[1], sys.argv[2])
    for c in r["cells"]:
        if not c["measured"]:
            print(c["cell"], c["gate"], "NOT MEASURED:", c["why_not_measured"])
            continue
        b = c["budgets"]
        print(c["cell"], c["gate"], "fit", c["guarded"], "eps", c["epsilon"], "K0", c["verdicts"]["K0"]["ok"],
              "K3", c["verdicts"]["K3"]["ok"], "train/test K0", b["K0"]["trainError"], b["K0"]["testError"],
              "K3", b["K3"]["trainError"], b["K3"]["testError"], "failing K3", c["verdicts"]["K3"]["failing"])
    print("eligible K0", r["eligible_K0"], "room K3", r["room_K3"])
