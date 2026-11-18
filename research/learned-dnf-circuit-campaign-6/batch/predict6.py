"""Campaign 6's development batch: the declared wrapper of BATCH_SPEC.md sections 3 and 4. New code; it imports
campaign 5's frozen `predicted.py` (P) and `gate4.py`, and edits neither.

For one instance, from its two calibration decks and its scans and one-sided sets:

1. the table: `P.load` and `P.table`, unchanged. In `table`'s `bad` list the entries that begin "FIRE bit" (campaign 5's
   test against the nominal theta) are replaced by the entries of section 3, point 6; every other entry is kept;
2. measured (section 3): the runs complete, the brackets consistent, the crossings below 8, every D_p > 0, question 1
   (ceil(s*) = the first firing stage of the guard-on deck, a need above 7 failing it), c's both-lines FIRE check
   fired at s = 0, the deck's both-lines reads all fire with Z(k) >= Z(0) (v9), the one-sided sets run at
   the recomputed bounds (exactly, as Fractions) and silent, every scan's u(0) within 20 uV of its own guard-on
   deck's, and every deck read against the cell's own trip levels;
3. per-cell units (section 4.1): theta_x = min L; every Z and L of cell x times 100 000 / theta_x, to the nearest
   integer, ties to even;
4. `P.instance` on the rescaled table, unchanged; then H_x + S_x added to every error (K = 0 and K = 3), and `P.room`,
   eligible, room_at_K3, counts_N_out and learning_ports recomputed from them as `P.instance` computes them;
5. the gate: `gate4.lean_file` on the measured instances, then campaign 5's `check.sh` on it (section 4: eligible =
   measured and the frozen gate holds under K = 0, Lean and the Python mirror agreeing).

Everything after the instrument is exact (Fractions), as in campaign 5.
"""
import copy
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
C5 = HERE.parent.parent / "learned-dnf-circuit-campaign-5"
sys.path.insert(0, str(C5))
import c4                                               # noqa: E402
import predicted as P                                   # noqa: E402

THETA = P.THETA
CROSSINGS = (("a", "pair"), ("b", "pair"), ("c", "line1"), ("c", "line2"))   # v9: c's both lines are no crossing read
NEEDS = dict(a=("a", "pair"), b=("b", "pair"), c1=("c", "line1"), c2=("c", "line2"))
DECK_READ = dict(pair="both", line1="port 1", line2="port 2")                   # the deck read of each scan kind
LEVEL_OF = {("a", "both"): "pair", ("b", "both"): "pair", ("c", "port 1"): "line1", ("c", "port 2"): "line2"}
BOTH = {("c", "both"), ("c", P.SKEWED)}                                          # predicted FIRE only (v9)
ALONE = {("a", "port 1"), ("a", "port 2"), ("b", "port 1"), ("b", "port 2")}


def scale(z, theta):
    """A score of the cell in per-cell units: z x 100 000 / theta_x, to the nearest integer, ties to even."""
    return round(F(z) * THETA / theta)


def doses_V(dose):
    """D_p: the mean of the eight joint-dose moves of each port in the guard-on deck (campaign 5's dose), in mV and V."""
    out = {}
    for c in c4.CELLS:
        for p in (1, 2):
            mv = sum(P.exact(dose[(c, p, k)]) for k in range(c4.STAGES)) / c4.STAGES
            out[(c, p)] = mv
    return out


U0_TOL_V = F(20, 10 ** 6)                                # a scan's u(0) against its own guard-on deck: 20 uV


def table(on_dir, off_dir):
    t, dose, bad = P.table(*P.load(on_dir, off_dir))
    return t, dose, [b for b in bad if not b.startswith("FIRE bit")]


def deck_u0(on_dir):
    """u of every port before the guard-on deck's first read (stage 0, `empty`), in V: the scans' u(0) is checked
    against it."""
    on_rows, _ = P.load(on_dir, on_dir)
    by = {(r["cell"], r["stage"], r["read"]): r for r in on_rows}
    return {(c, p): F(by[(c, 0, "empty")]["ports"][str(p)]["u_before_mV"]) / 1000 for c in c4.CELLS for p in (1, 2) if (c, 0, "empty") in by}


def steps(t2, c):
    """step_r: (Z_r(7) - Z_r(0)) / 7 in the rescaled guard-off deck, per deck read."""
    reads = ("port 1", "port 2") if c == "c" else ("port 1", "port 2", "both")
    return {r: F(t2[(c, 7, r)]["Z"] - t2[(c, 0, r)]["Z"], 7) for r in reads}


def one_sided_bounds(t2, c, H):
    """For a or b: per port, the least s in [0, 8] at which the rescaled score of the port alone, linear between the
    deck's stages (and on from stage 7 with the step from 6 to 7), reaches THETA + H_x; 8 if it never does."""
    out = {}
    for p in (1, 2):
        z = [F(t2[(c, k, f"port {p}")]["Z"]) for k in range(c4.STAGES)] + [None]
        z[8] = z[7] + (z[7] - z[6])
        goal, s = THETA + H, F(8)
        for k in range(8):
            if z[k] >= goal:
                s = F(k)
                break
            if z[k + 1] >= goal and z[k + 1] > z[k]:
                s = k + (goal - z[k]) / (z[k + 1] - z[k])
                break
        out[p] = s
    return out


def u0_check(runs, deck_u):
    """Every scan's and one-sided set's u(0) (its `u0_V`, both ports of its cell) within 20 uV of the guard-on deck's."""
    why = []
    for name, r in runs.items():
        c = name[0]
        for p in (1, 2):
            if "u0_V" not in r or (c, p) not in deck_u:
                why.append(f"{name}: u(0) of port {p} not recorded")
                continue
            d = F(r["u0_V"][str(p)]) - deck_u[(c, p)]
            if abs(d) > U0_TOL_V:
                why.append(f"{name}: u(0) of port {p} differs from the guard-on deck's by {float(d) * 1e6:.3f} uV (more than 20 uV)")
    return why


def measure_instance(seed, statuses, t, dose, bad, scans, onesided, deck_u=None, bothfire=None):
    """statuses: {run id: status}; scans: {(cell, kind): the scan's `result`}; onesided: {cell: result}.
    Returns (why_not_measured, per-cell data). The rescaled table is in data['t2']."""
    why = list(bad)
    why += [f"run {i} did not complete: {s}" for i, s in sorted(statuses.items()) if s != "complete"]
    D = doses_V(dose) if not any(b.startswith("missing joint dose") for b in bad) else {}
    why += [f"D_{c}{p} = {v} mV, not positive" for (c, p), v in sorted(D.items()) if v <= 0]
    for key in CROSSINGS:
        r = scans.get(key)
        if r is None:
            continue
        if not r.get("crossing"):
            why.append(f"scan {key}: no crossing below 8")
        elif not r.get("consistent"):
            why.append(f"scan {key}: bracket not consistent ({r.get('why', 'after the majority')})")
    if deck_u is not None:
        runs = {**{k: v for k, v in scans.items()}, **{(c, "onesided"): v for c, v in onesided.items()}}
        if bothfire is not None:
            runs[("c", "bothfire")] = bothfire
        why += u0_check(runs, deck_u)
    data = dict(D_mV={f"{c}{p}": str(v) for (c, p), v in D.items()})
    if why or any(k not in scans for k in CROSSINGS):
        why += [f"scan {k}: missing" for k in CROSSINGS if k not in scans]
        return why, data
    S = {k: F(scans[k]["s_star"]) for k in CROSSINGS}
    h = {k: F(scans[k]["half_bracket"]) for k in CROSSINGS}
    L = {k: int(scans[k]["L"]) for k in CROSSINGS}
    observed = P.needs(t)
    q1 = {}
    for need, key in NEEDS.items():
        pred, obs = math.ceil(S[key]), observed[need]
        q1[need] = dict(predicted=pred, observed=obs, agree=obs is not None and obs <= 7 and pred == obs)
        if not q1[need]["agree"]:
            why.append(f"question 1: need {need}: ceil(s*) = {pred}, first firing stage of the guard-on deck {obs}")
    data["question_1"] = q1
    theta = dict(a=L[("a", "pair")], b=L[("b", "pair")], c=min(L[k] for k in CROSSINGS if k[0] == "c"))
    t2 = {key: dict(v, Z=scale(v["Z"], theta[key[0]])) for key, v in t.items()}
    L2 = {k: scale(L[k], theta[k[0]]) for k in CROSSINGS}
    H, Sx = {}, {}
    for c in c4.CELLS:
        st = steps(t2, c)
        H[c] = max(math.ceil(h[k] * st[DECK_READ[k[1]]]) for k in CROSSINGS if k[0] == c)
        Sx[c] = max(L2[k] for k in CROSSINGS if k[0] == c) - min(L2[k] for k in CROSSINGS if k[0] == c)
    bounds = {c: one_sided_bounds(t2, c, H[c]) for c in ("a", "b")}
    if bothfire is None:
        why.append("the both-lines FIRE check of c: missing")
    elif not bothfire.get("fired"):
        why.append("the both-lines FIRE check of c: both lines did not fire at the preset (s = 0)")
    for c in ("a", "b"):
        o = onesided.get(c)
        if o is None:
            why.append(f"one-sided set of {c}: missing")
        elif {p: F(o["bounds"][str(p)]) for p in (1, 2)} != bounds[c]:
            why.append(f"one-sided set of {c}: its bounds {o['bounds']} are not the recomputed {bounds[c]}")
        elif not o.get("all_silent"):
            why.append(f"one-sided set of {c}: a port alone fired at or below its bound {o.get('bounds')}")
    for (c, k, r), v in sorted(t2.items()):
        if r == "empty":
            if v["fire"]:
                why.append(f"deck read {(c, k, r)}: an empty read fired")
            continue
        if (c, r) in BOTH:
            if not v["fire"]:
                why.append(f"deck read {(c, k, r)}: both lines did not fire (they are predicted to fire at every stage)")
            if v["Z"] < t2[(c, 0, r)]["Z"]:
                why.append(f"deck read {(c, k, r)}: Z = {v['Z']} below its stage-0 value {t2[(c, 0, r)]['Z']} (monotonicity)")
            continue
        if (c, r) in ALONE:
            if v["fire"] and v["Z"] < THETA + H[c]:
                why.append(f"deck read {(c, k, r)}: a port alone fired with Z = {v['Z']} below the one-sided bound {THETA + H[c]}")
            continue
        lev = L2[(c, LEVEL_OF[(c, r)])]
        if abs(v["Z"] - lev) <= H[c]:
            continue
        if v["fire"] != (v["Z"] >= lev):
            why.append(f"deck read {(c, k, r)}: FIRE bit {v['fire']} and Z = {v['Z']} disagree with the cell's own level L = {lev}")
    data.update(t2=t2, theta=theta, L={f"{c}-{k}": v for (c, k), v in L.items()}, L_rescaled={f"{c}-{k}": v for (c, k), v in L2.items()}, s_star={f"{c}-{k}": str(v) for (c, k), v in S.items()},
                half_bracket={f"{c}-{k}": str(v) for (c, k), v in h.items()}, H=H, S=Sx, one_sided_bounds={c: {str(p): str(s) for p, s in b.items()} for c, b in bounds.items()})
    return why, data


def lay_of(x):
    g = x["guarded"]
    gain = {(k[0], int(k[1])): v for k, v in g["gain"].items()}
    return lambda c: dict(help=g["help"], gain=gain, dose=g["dose"][c])


def augmented(x, H, S, t2):
    """H_x + S_x added to every error of x, K = 0 and K = 3; room and the verdicts recomputed as P.instance does."""
    if "budgets" not in x:
        return x
    x = copy.deepcopy(x)
    for K in ("K0", "K3"):
        for c in c4.CELLS:
            for side in ("training", "testing"):
                x["budgets"][K][c][side] = int(x["budgets"][K][c][side]) + H[c] + S[c]
    n = x["needs"]
    lay = lay_of(x)
    room = {K: P.room(t2, n, lay, x["budgets"][K]) for K in ("K0", "K3")}
    x["room"] = room
    ok0 = all(v["all"] for v in room["K0"].values())
    x["eligible"] = ok0
    x["why_not_eligible"] = [] if ok0 else [f"{c}: {', '.join(v['without_room'])}" for c, v in room["K0"].items() if not v["all"]]
    x["room_at_K3"] = {c: v["all"] for c, v in room["K3"].items()}
    x["counts_N_out"] = dict(a=x["room_at_K3"]["a"], b=x["room_at_K3"]["b"], c=x["room_at_K3"]["a"] and x["room_at_K3"]["b"] and x["room_at_K3"]["c"])
    x["learning_ports"] = P.learning_ports(room["K3"])
    x["errors_added"] = {c: dict(H=H[c], S=S[c]) for c in c4.CELLS}
    return x


def predict_instance(seed, machine, statuses, on_dir, off_dir, scans, onesided, bothfire=None):
    t, dose, bad = table(on_dir, off_dir)
    why, data = measure_instance(seed, statuses, t, dose, bad, scans, onesided, deck_u0(on_dir), bothfire)
    if why:
        return dict(seed=seed, machine=machine, measured=False, why_not_measured=why, eligible=False,
                    **{k: v for k, v in data.items() if k != "t2"})
    x = P.instance(seed, data["t2"], dose, [], c4.DECISION5)
    x = augmented(x, data["H"], data["S"], data["t2"])
    x.update(machine=machine, **{k: v for k, v in data.items() if k != "t2"})
    return x


def gate_file(instances, out):
    """The frozen gate on the measured instances that have an observation (gate4.lean_file), as campaign 5's rehearsal."""
    import gate4
    xs = [dict(x, tag=str(x["seed"])) for x in instances if x.get("measured") and "observation" in x]
    text = gate4.lean_file(xs, "the development batch's predictions (campaign 6)") if xs else (
        gate4.header("the development batch's predictions (campaign 6)") + "theorem no_instance_with_all_needs : True := trivial\n\n"
        "end LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4\n")
    Path(out).write_text(text)
    return xs


def questions(scans, dose, needs_observed):
    """Questions 2 and 5 of the design note (reported, deciding nothing). Q2: for each need's crossing, the margins
    s* - (n - 1) and n - s* in stages and in mV (times the largest D of its moving ports), and the largest of the
    three terms in mV: the half bracket, the dose-move variation max_k |sum_{j<k} m_j - k D_p| and the K = 3 noise
    3 sqrt(w^2 + b^2 + n d^2). Q5: each scan's bracket width in mV, whether it was contradictory, its repeats."""
    import scan6
    D = doses_V(dose)
    w, b, d = (F(str(c4.DECISION5[k])) for k in ("within_mV", "between_mV", "per_dose_mV"))
    q2, q5 = {}, {}
    for (c, kind), r in scans.items():
        moving = scan6.MOVING[kind]
        dmax = max(D[(c, p)] for p in moving)
        if r.get("consistent"):
            q5[f"{c}-{kind}"] = dict(width_mV=str(2 * F(r["half_bracket"]) * dmax), contradictory=r.get("contradictory"),
                                     repeats=4 if r.get("contradictory") else 0)
        else:
            q5[f"{c}-{kind}"] = dict(consistent=False, why=r.get("why"), contradictory=r.get("contradictory"))
    for need, (c, kind) in NEEDS.items():
        r = scans.get((c, kind))
        if not r or not r.get("consistent"):
            continue
        s, n = F(r["s_star"]), math.ceil(F(r["s_star"]))
        moving = scan6.MOVING[kind]
        dmax = max(D[(c, p)] for p in moving)
        var = max(abs(sum(P.exact(dose[(c, p, j)]) for j in range(k)) - k * D[(c, p)]) for p in moving for k in range(c4.STAGES + 1))
        noise2 = 9 * (w * w + b * b + n * d * d)
        terms = dict(half_bracket=F(r["half_bracket"]) * dmax, dose_variation=var)
        big = max(terms, key=lambda t: terms[t])
        noise_dominates = noise2 > terms[big] ** 2
        q2[need] = dict(n=n, below_stages=str(s - (n - 1)), above_stages=str(n - s), below_mV=str((s - (n - 1)) * dmax), above_mV=str((n - s) * dmax),
                        terms_mV={k: str(v) for k, v in terms.items()}, noise_mV_squared=str(noise2),
                        dominant="noise" if noise_dominates else big)
    return dict(question_2=q2, question_5=q5)


def collected(d):
    return json.loads((Path(d) / "record.json").read_text())


def predict_batch(batch_dir, out_dir, check=True):
    """Every instance of the batch from its collected runs (BATCH_DIR/<machine>/<run id>/ and BATCH_DIR/RUNS.json),
    then the gate, one Lean file per instance, each checked by its own call of campaign 5's check.sh. Writes
    PREDICTIONS.json, Gate6_<seed>.lean and check_<seed>.log."""
    import subprocess
    import gate4
    import batch6
    bd, od = Path(batch_dir), Path(out_dir)
    od.mkdir(parents=True, exist_ok=True)
    runs = json.loads((bd / "RUNS.json").read_text())
    status = {r["id"]: r["status"] for r in runs}
    xs = []
    for seed in batch6.SEEDS:
        m = batch6.MACHINE_OF[seed]
        mine = {i: s for i, s in status.items() if i.startswith(f"{seed}-")}
        on, off = bd / m / f"{seed}-cal-on", bd / m / f"{seed}-cal-off"
        if mine.get(f"{seed}-cal-on") != "complete" or mine.get(f"{seed}-cal-off") != "complete":
            xs.append(dict(seed=seed, machine=m, measured=False, eligible=False, why_not_measured=[f"run {i} did not complete: {s}" for i, s in sorted(mine.items()) if s != "complete"]))
            continue
        scans, ones = {}, {}
        for c, kind in CROSSINGS:
            i = f"{seed}-scan-{c}-{kind}"
            if mine.get(i) == "complete":
                rec = collected(bd / m / i)
                scans[(c, kind)] = dict(rec["result"], u0_V=rec["u0_V"])
        for c in ("a", "b"):
            i = f"{seed}-onesided-{c}"
            if mine.get(i) == "complete":
                rec = collected(bd / m / i)
                ones[c] = dict(rec["result"], u0_V=rec["u0_V"])
        bf = None
        if mine.get(f"{seed}-bothfire-c") == "complete":
            rec = collected(bd / m / f"{seed}-bothfire-c")
            bf = dict(rec["result"], u0_V=rec["u0_V"])
        x = predict_instance(seed, m, mine, on, off, scans, ones, bf)
        t, dose, _ = table(on, off)
        x.update(questions(scans, dose, P.needs(t)))
        xs.append(x)
    gate_each(xs, od, check)
    (od / "PREDICTIONS.json").write_text(json.dumps(dict(instances=xs), indent=1, default=str) + "\n")
    return xs


def gate_each(xs, od, check=True):
    """The frozen gate per instance: its own Lean file (gate4.lean_file on that instance alone) and its own check.sh
    call. An instance passes only if its own file passes, and the Python verdict (gate4.verdicts, K = 0) holds."""
    import subprocess
    import gate4
    for x in xs:
        x["gate_K0"] = False
        if not (x.get("measured") and "observation" in x):
            continue
        name = "nominal" if x["seed"] is None else str(x["seed"])
        lean = od / f"Gate6_{name}.lean"
        gate_file([x], lean)
        if check:
            p = subprocess.run(["bash", str(C5 / "check.sh"), str(lean)], capture_output=True, text=True)
            (od / f"check_{name}.log").write_text(p.stdout + p.stderr)
            x["check_sh_passed"] = p.returncode == 0 and "check.sh: passed" in p.stdout
        x["gate_K0"] = bool(x.get("check_sh_passed")) and gate4.verdicts(x)["K0"]


def predict_smoke(smoke_dir, on, off, out_dir, check=True):
    """The whole chain on the declared nominal smoke (seed None): the 1/4 instance's runs, the wrapper, its Lean
    file and check.sh. Its numbers enter no report of the batch."""
    sd, od = Path(smoke_dir), Path(out_dir)
    od.mkdir(parents=True, exist_ok=True)
    runs = json.loads((sd / "RUNS.json").read_text())
    status = {r["id"]: r["status"] for r in runs if not r["id"].startswith("none-h-")}
    scans, ones = {}, {}
    for c, kind in CROSSINGS:
        if status.get(f"none-q-scan-{c}-{kind}") == "complete":
            rec = collected(sd / f"none-q-scan-{c}-{kind}")
            scans[(c, kind)] = dict(rec["result"], u0_V=rec["u0_V"])
    for c in ("a", "b"):
        if status.get(f"none-onesided-{c}") == "complete":
            rec = collected(sd / f"none-onesided-{c}")
            ones[c] = dict(rec["result"], u0_V=rec["u0_V"])
    bf = None
    if status.get("none-bothfire-c") == "complete":
        rec = collected(sd / "none-bothfire-c")
        bf = dict(rec["result"], u0_V=rec["u0_V"])
    x = predict_instance(None, "a", status, on, off, scans, ones, bf)
    t, dose, _ = table(on, off)
    x.update(questions(scans, dose, P.needs(t)))
    gate_each([x], od, check)
    (od / "PREDICTIONS.json").write_text(json.dumps(dict(smoke=True, instances=[x]), indent=1, default=str) + "\n")
    return x


if __name__ == "__main__":
    import batch6
    batch6.require_debug()
    a = sys.argv[1:]
    print(c4.require_pinned())
    if a and a[0] == "predict":                             # predict6.py predict BATCH_DIR OUT_DIR
        xs = predict_batch(a[1], a[2])
    elif a and a[0] == "smoke":                             # predict6.py smoke SMOKE_DIR RC_CAL_ON RC_CAL_OFF OUT_DIR
        xs = [predict_smoke(a[1], a[2], a[3], a[4])]
    else:
        raise SystemExit("predict6.py predict BATCH_DIR OUT_DIR | smoke SMOKE_DIR RC_CAL_ON RC_CAL_OFF OUT_DIR")
    print(json.dumps(dict(measured=[x["seed"] for x in xs if x.get("measured")], eligible=[x["seed"] for x in xs if x.get("gate_K0")])))
