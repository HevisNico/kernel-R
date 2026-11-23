"""Development only: the prediction code of the step-1 family (TOPUP_RULES.md 3 and 3.5). No simulation is run.

For one instance and one member (X1, X2, F4, F2, F3; F1 as the regression anchor), from B2's measures and, for a
unary cell, the top-up's measures:

1. the unary port of each of a and b (TOPUP_RULES.md 1), from the top-up's unary scans and preset checks only;
2. the member's table, by cell kind and source (3.5.1); the anchors (3.5.2); the mapped Z (3.5.3);
3. the checks that make it "not measured" (3.5.4, 3.5.7);
4. the guarded tuple, epsilon and sensitivities (3.5.5); the budgets with H and S (3.5.6);
5. the observation (3.5.8) and the generator spec; the mirror's verdicts at K = 0 and K = 3 (3.2); the Lean file
   of the gate and the kernel's verdict by the generator's gencheck.sh (3.3, 3.5.9, 3.5.10 points 8 and 9).

Frozen code is imported and called by name, never edited: campaign 5's predicted.py (P), campaign 6's predict6.py,
the generator's spec.py, mirror.py and emit.py. Everything that becomes an integer is exact (Fractions), as P
requires.

  family_predict.py predict REPO GEN B2_DIR TOPUP_DIR OUT_DIR [--no-lean]   every (instance, member), PREDICTIONS.json
  family_predict.py ports TOPUP_DIR                                       the unary ports of section 1 only

REPO: research/learned-dnf-circuit-campaign-6-impl at ecfcd1c1. GEN: research/learned-dnf-generator at 4fca6256.
B2_DIR: B2's runs, <seed>-<run>/ and W1..W3/STATE.json. TOPUP_DIR: a top-up machine's RUNS folder (or several, with
os.pathsep). PYTHONPATH as topup.py's (FUP dev, PREP dev, this folder).
"""
from fractions import Fraction as F
import json
import math
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SEEDS = tuple(range(8301, 8311))
STEP1 = ("X1", "X2", "F4", "F2", "F3")
MEMBERS = {                                   # FAMILY_DESIGN.md 0.1; F1 as campaign 6 (0.3)
    "X1": dict(inputs=("A",), terms=dict(a=("A",))),
    "X2": dict(inputs=("A", "B"), terms=dict(a=("A", "B"))),
    "F4": dict(inputs=("A", "B"), terms=dict(a=("A",), b=("B",))),
    "F2": dict(inputs=("A", "B", "C"), terms=dict(a=("A", "B"), b=("A", "C"))),
    "F3": dict(inputs=("A", "B", "C"), terms=dict(a=("A",), b=("B", "C"))),
    "F1": dict(inputs=("A", "B", "C", "D"), terms=dict(a=("A", "B"), b=("C", "D"))),
}
LINE_PORT = dict(a=1, b=2)                    # c's port of each first-layer cell's line
UNARY_READ = {1: "port 1 at 1.0", 2: "port 2 at 1.0"}   # topup.UNARY
PAIR_READS = ("empty", "port 1", "port 2", "both")
GEN_NAMESPACE = "LearnedCoincidence.MonotoneDNF.PremiseCheck.FamilyTopup"


def paths(repo, gen):
    import dosedev2
    dosedev2.repo_paths(repo)
    sys.path.insert(0, str(Path(gen).resolve() / "research" / "learned-dnf-generator"))


def mods():
    import predict6
    import spec
    import mirror
    import emit
    return predict6, predict6.P, spec, mirror, emit


# ------------------------------------------------------------------------------------------------- the runs on disk

def statuses(*dirs):
    """{run id: status} from the W1..W3 STATE.json of each folder."""
    out = {}
    for d in dirs:
        for sub in ("W1", "W2", "W3"):
            p = Path(d) / sub / "STATE.json"
            if p.exists():
                out.update({k: v["status"] for k, v in json.loads(p.read_text())["runs"].items()})
    return out


def record(d):
    """A run's record.json, or None if the folder or its record is missing (3.5.10 point 6: not measured)."""
    p = Path(d) / "record.json"
    return json.loads(p.read_text()) if p.exists() else None


def result_of(status, folder, rid):
    """The run's `result` with its u0_V, if it completed and its record is on disk; else None."""
    if status.get(rid) != "complete":
        return None
    r = record(Path(folder) / rid)
    if r is None:
        return None
    return dict(r["result"], u0_V=r["u0_V"])


def find_run(dirs, rid):
    for d in dirs:
        if (Path(d) / rid).is_dir():
            return Path(d)
    return Path(dirs[0])


# --------------------------------------------------------------------------------------------- 1. the unary ports

def margin(s):
    """m_p = min(s - floor(s), ceil(s) - s), exactly (TOPUP_RULES.md 1.2)."""
    return min(s - math.floor(s), math.ceil(s) - s)


def unary_port(scans, preset):
    """TOPUP_RULES.md 1.3. scans: {1: scan result or None, 2: ...}; preset: the preset check's result or None.
    Returns (port, detail)."""
    elig, det = {}, {}
    for p in (1, 2):
        r = scans.get(p)
        why = []
        if r is None:
            why.append("unary scan not complete")
        elif not (r.get("crossing") and r.get("consistent")):
            why.append("unary scan without a consistent crossing below 8")
        if preset is None:
            why.append("preset check not complete")
        elif preset["silent"].get(str(p)) is not True:
            why.append("preset read of the port not silent")
        det[p] = dict(eligible=not why, why=why)
        if not why:
            s = F(r["s_star"])
            elig[p] = margin(s)
            det[p].update(s_star=str(s), margin=str(elig[p]))
    if len(elig) == 2:
        port = 1 if elig[1] >= elig[2] else 2           # the larger margin; on an exact tie, port 1
    elif len(elig) == 1:
        port = next(iter(elig))
    else:
        port = 1
    return port, dict(ports=det, chosen=port)


def unary_inputs(seed, tdirs, tstat):
    """The top-up's runs of one instance: for each of a, b, its scans of both ports and its preset check."""
    out = {}
    for c in ("a", "b"):
        sc = {}
        for p in (1, 2):
            rid = f"{seed}-unary-scan-{c}{p}"
            sc[p] = result_of(tstat, find_run(tdirs, rid), rid)
        rid = f"{seed}-preset-{c}"
        pre = result_of(tstat, find_run(tdirs, rid), rid)
        port, det = unary_port(sc, pre)
        out[c] = dict(scans=sc, preset=pre, port=port, detail=det)
    return out


# ---------------------------------------------------------------------------------------------- 2. the sources

def source(on_dir, off_dir, unary=False):
    """One deck pair: the frozen table (predict6.table), the doses, the deck's w and u(0); with unary=True also the
    UNARY reads of a and b (Z from the guard-off deck, FIRE and latency from the guard-on deck, as P.table does)."""
    predict6, P, *_ = mods()
    t, dose, bad = predict6.table(on_dir, off_dir)
    src = dict(t=dict(t), dose=dose, bad=list(bad), on=str(on_dir))
    if unary and not any(b.startswith("missing") for b in bad):
        on_rows, off_rows = P.load(on_dir, off_dir)
        on = {(r["cell"], r["stage"], r["read"]): r for r in on_rows}
        off = {(r["cell"], r["stage"], r["read"]): r for r in off_rows}
        for c in ("a", "b"):
            for p, name in UNARY_READ.items():
                for k in range(8):
                    key = (c, k, name)
                    if key not in on or key not in off:
                        src["bad"].append(f"missing read {key}")
                        continue
                    src["t"][key] = dict(Z=P.zint(off[key]["q_peak"]), fire=on[key]["fire"],
                                         latency=None if on[key]["latency"] is None else P.q(on[key]["latency"]))
    if not any(b.startswith("missing") for b in src["bad"]):
        src["D"] = predict6.doses_V(dose)
        src["w"] = predict6.deck_w(on_dir, src["D"])
        src["u"] = predict6.deck_u0(on_dir)
    return src


# ---------------------------------------------------------------------------------------------- the member

def kinds(member):
    """{cell: 'pair' | 'unary'} of the first layer."""
    return {c: "pair" if len(t) == 2 else "unary" for c, t in MEMBERS[member]["terms"].items()}


def wiring(member, uport):
    """{cell: {input: port}}: a pair term's inputs on ports 1 and 2 in order; a unary term's input on its chosen port
    (FAMILY_DESIGN.md 0.1; TOPUP_RULES.md 3.5.10 point 1)."""
    w = {}
    for c, ins in MEMBERS[member]["terms"].items():
        w[c] = {ins[0]: 1, ins[1]: 2} if len(ins) == 2 else {ins[0]: uport[c]}
    return w


def full_read(kind, port):
    return "both" if kind == "pair" else f"port {port}"


def cell_reads(kind, port):
    return PAIR_READS if kind == "pair" else ("empty", f"port {port}")


def c_reads(nlines, P):
    return ("empty", "port 1", "port 2", "both", P.SKEWED) if nlines == 2 else ("empty", "port 1")


def member_table(member, uport, b2, tu, P):
    """(t, w, dose) of the member: each cell's reads from its own source (3.5.1); a UNARY read renamed `port p`
    (3.5.3). Keys (cell, stage, read)."""
    t, w, dose = {}, {}, {}
    kd = kinds(member)
    for c, kind in kd.items():
        if kind == "pair":
            for k in range(8):
                for r in PAIR_READS:
                    t[(c, k, r)], w[(c, k, r)] = b2["t"][(c, k, r)], b2["w"][(c, k, r)]
                for p in (1, 2):
                    dose[(c, p, k)] = b2["dose"][(c, p, k)]
        else:
            p = uport[c]
            for k in range(8):
                t[(c, k, "empty")], w[(c, k, "empty")] = tu["t"][(c, k, "empty")], tu["w"][(c, k, "empty")]
                t[(c, k, f"port {p}")], w[(c, k, f"port {p}")] = tu["t"][(c, k, UNARY_READ[p])], tu["w"][(c, k, UNARY_READ[p])]
                dose[(c, p, k)] = tu["dose"][(c, p, k)]
    nl = len(kd)
    for k in range(8):
        for r in c_reads(nl, P):
            t[("c", k, r)], w[("c", k, r)] = b2["t"][("c", k, r)], b2["w"][("c", k, r)]
        for p in range(1, nl + 1):
            dose[("c", p, k)] = b2["dose"][("c", p, k)]
    return t, w, dose


# ---------------------------------------------------------------------------------------------- 3.5.2 the anchors

def anchors(member, uport, S, b2_pair_ok, THETA):
    """S: {('a', 'pair'), ('b', 'pair'), ('a', 'unary'), ..., ('c', 'line1'), ('c', 'line2')} -> s* (exact).
    b2_pair_ok: {a, b: B2's pair scan complete and consistent}."""
    kd = kinds(member)
    xs = [x for x in ("a", "b") if b2_pair_ok[x]]
    K = max(max(8 - S[(x, "pair")], S[(x, "pair")]) for x in xs) if xs else F(8)
    d = round(F(THETA) / (2 * K))
    gain, W = {}, {}
    for c, kind in kd.items():
        if kind == "pair":
            s = S[(c, "pair")]
            gain[(c, 1)] = gain[(c, 2)] = round(d * (K - s))
            W[c] = s + K
        else:
            p = uport[c]
            gain[(c, p)] = round(THETA - d * S[(c, "unary")])
    if len(kd) == 2:
        s1, s2 = S[("c", "line1")], S[("c", "line2")]
        dc = round(F(THETA) / (s1 + s2))
        gain[("c", 1)], gain[("c", 2)] = round(THETA - dc * s1), round(THETA - dc * s2)
        Kc = None
    else:
        s1 = S[("c", "line1")]
        Kc = max(8 - s1, s1)
        dc = round(F(THETA) / (2 * Kc))
        gain[("c", 1)] = round(THETA - dc * s1)
    assert all(g >= 0 for g in gain.values()) and d > 0 and dc > 0, "the kernel's fields are natural numbers"
    return dict(K=K, d=d, d_c=dc, K_c=Kc, W=W, gain=gain)


def mapped(t, w, an, predict6):
    """predict6.mapped's rule on the member's reads (help 0): Z = round(sum over the read's ports of (g + dose w))."""
    out = {}
    for (c, k, r), v in t.items():
        dose = an["d_c"] if c == "c" else an["d"]
        out[(c, k, r)] = dict(v, Z=round(sum(an["gain"][(c, p)] + dose * w[(c, k, r)][p] for p in predict6.PORTS_OF[r])))
    return out


# ---------------------------------------------------------------------------------------------- one (instance, member)

def predict(member, seed, b2, b2_runs, tu, tu_runs, unary, THETA=None):
    """b2, tu: sources (tu None if the member has no unary cell); b2_runs: {(cell, kind): result or None} for
    ('a'|'b', 'pair'|'onesided'), ('c', 'line1'|'line2'|'bothfire'); tu_runs: {(cell, 'unary'|'preset'): result};
    unary: {cell: port}. b2['status'], tu['status']: {run id: status} of the runs listed in b2['runs'], tu['runs'].
    Returns (x, why_not_measured)."""
    predict6, P, *_ = mods()
    THETA = P.THETA
    kd = kinds(member)
    nl = len(kd)
    lines = [f"line{p}" for p in range(1, nl + 1)]
    why = []
    # --- the runs the member uses, each complete (3.5.7)
    for rid, st in sorted(b2["status"].items()):
        if st != "complete":
            why.append(f"run {rid} did not complete: {st}")
    if tu is not None:
        for rid, st in sorted(tu["status"].items()):
            if st != "complete":
                why.append(f"run {rid} did not complete: {st}")
    why += [f"B2 deck: {b}" for b in b2["bad"]]
    if tu is not None:
        why += [f"top-up deck: {b}" for b in tu["bad"]]
    if why:
        return dict(member=member, seed=seed, measured=False), why
    uport = {c: unary[c] for c, k in kd.items() if k == "unary"}
    t, w, dose = member_table(member, uport, b2, tu, P)
    # --- doses of the ports used
    D = {}
    for c, kind in kd.items():
        src = b2 if kind == "pair" else tu
        for p in ((1, 2) if kind == "pair" else (uport[c],)):
            D[(c, p)] = src["D"][(c, p)]
    for p in range(1, nl + 1):
        D[("c", p)] = b2["D"][("c", p)]
    why += [f"D_{c}{p} = {v} mV, not positive" for (c, p), v in sorted(D.items()) if v <= 0]
    # --- the scans and checks used
    scans = {}
    for c, kind in kd.items():
        scans[(c, "pair" if kind == "pair" else "unary")] = b2_runs.get((c, "pair")) if kind == "pair" else tu_runs.get((c, "unary"))
    for ln in lines:
        scans[("c", ln)] = b2_runs.get(("c", ln))
    for key, r in sorted(scans.items()):
        if r is None:
            why.append(f"scan {key}: missing")
        elif not r.get("crossing"):
            why.append(f"scan {key}: no crossing below 8")
        elif not r.get("consistent"):
            why.append(f"scan {key}: bracket not consistent ({r.get('why', 'after the majority')})")
    # --- u(0) of every scan and check against its own source's guard-on deck (3.5.1)
    on_b2 = {k: v for k, v in scans.items() if k[1] != "unary" and v is not None}
    for c, kind in kd.items():
        if kind == "pair" and b2_runs.get((c, "onesided")) is not None:
            on_b2[(c, "onesided")] = b2_runs[(c, "onesided")]
    if nl == 2 and b2_runs.get(("c", "bothfire")) is not None:
        on_b2[("c", "bothfire")] = b2_runs[("c", "bothfire")]
    why += predict6.u0_check(on_b2, b2["u"])
    if tu is not None:
        on_tu = {k: v for k, v in scans.items() if k[1] == "unary" and v is not None}
        for c in uport:
            if tu_runs.get((c, "preset")) is not None:
                on_tu[(c, "preset")] = tu_runs[(c, "preset")]
        why += predict6.u0_check(on_tu, tu["u"])
    x = dict(member=member, seed=seed, kinds=kd, unary_ports=uport, D_mV={f"{c}{p}": str(v) for (c, p), v in D.items()})
    if why:
        return dict(x, measured=False), why
    S = {k: F(r["s_star"]) for k, r in scans.items()}
    h = {k: F(r["half_bracket"]) for k, r in scans.items()}
    b2_pair_ok = {}
    for c in ("a", "b"):
        r = b2_runs.get((c, "pair"))
        b2_pair_ok[c] = r is not None and bool(r.get("crossing")) and bool(r.get("consistent"))
        if b2_pair_ok[c]:
            S[(c, "pair")] = F(r["s_star"])
    # --- question 1 (3.5.4)
    fire1 = lambda c, r: next((k for k in range(8) if t[(c, k, r)]["fire"]), None)
    q1, need = {}, {}
    for c, kind in kd.items():
        key = (c, "pair" if kind == "pair" else "unary")
        pred, obs = math.ceil(S[key]), fire1(c, full_read(kind, uport.get(c)))
        q1[c] = dict(predicted=pred, observed=obs, agree=obs is not None and obs <= 7 and pred == obs)
        need[c] = obs
    for p in range(1, nl + 1):
        pred, obs = math.ceil(S[("c", f"line{p}")]), fire1("c", f"port {p}")
        q1[f"c{p}"] = dict(predicted=pred, observed=obs, agree=obs is not None and obs <= 7 and pred == obs)
        need[f"c{p}"] = obs
    for k, v in q1.items():
        if not v["agree"]:
            why.append(f"question 1: need {k}: ceil(s*) = {v['predicted']}, first firing stage of the guard-on deck {v['observed']}")
    x["question_1"] = q1
    an = anchors(member, uport, S, b2_pair_ok, THETA)
    t2 = mapped(t, w, an, predict6)
    H = {}
    for c, kind in kd.items():
        H[c] = math.ceil(h[(c, "pair")] * 2 * an["d"]) if kind == "pair" else math.ceil(h[(c, "unary")] * an["d"])
    H["c"] = max(math.ceil(h[("c", ln)] * an["d_c"]) for ln in lines)
    Sx = {c: 0 for c in H}
    # --- one-sided sets of the pair cells (bounds W_x + h_x, exactly) and the preset checks of the unary cells
    for c, kind in kd.items():
        if kind == "pair":
            o = b2_runs.get((c, "onesided"))
            bound = an["W"][c] + h[(c, "pair")]
            if o is None:
                why.append(f"one-sided set of {c}: missing")
            elif {p: F(o["bounds"][str(p)]) for p in (1, 2)} != {1: bound, 2: bound}:
                why.append(f"one-sided set of {c}: its bounds {o['bounds']} are not the recomputed {bound}")
            elif not o.get("all_silent"):
                why.append(f"one-sided set of {c}: a port alone fired at or below its bound {o.get('bounds')}")
        else:
            o = tu_runs.get((c, "preset"))
            if o is None:
                why.append(f"preset check of {c}: missing")
            elif o["silent"].get(str(uport[c])) is not True:
                why.append(f"preset check of {c}: port {uport[c]} at 1.0 not silent at s = 0")
    if nl == 2:
        bf = b2_runs.get(("c", "bothfire"))
        if bf is None:
            why.append("the both-lines FIRE check of c: missing")
        elif not bf.get("fired"):
            why.append("the both-lines FIRE check of c: both lines did not fire at the preset (s = 0)")
    # --- the decoder check, and c's both-lines reads (3.5.7)
    both = {"both", P.SKEWED} if nl == 2 else set()
    for (c, k, r), v in sorted(t2.items()):
        if abs(v["Z"] - THETA) > H[c] and v["fire"] != (v["Z"] >= THETA):
            why.append(f"deck read {(c, k, r)}: FIRE bit {v['fire']} and Z = {v['Z']} disagree (Z >= THETA)")
        if c == "c" and r in both:
            if not v["fire"]:
                why.append(f"deck read {(c, k, r)}: both lines did not fire (they are predicted to fire at every stage)")
            if v["Z"] < t2[(c, 0, r)]["Z"]:
                why.append(f"deck read {(c, k, r)}: Z = {v['Z']} below its stage-0 value {t2[(c, 0, r)]['Z']} (monotonicity)")
    x.update(s_star={f"{k[0]}-{k[1]}": str(v) for k, v in S.items()}, half_bracket={f"{k[0]}-{k[1]}": str(v) for k, v in h.items()},
             anchors=dict(K=str(an["K"]), d=an["d"], d_c=an["d_c"], K_c=None if an["K_c"] is None else str(an["K_c"]),
                          W={c: str(v) for c, v in an["W"].items()}, gain={f"{c}{p}": g for (c, p), g in an["gain"].items()}),
             H=H, S=Sx, needs=need)
    if why:
        return dict(x, measured=False), why
    x["measured"] = True
    x.update(budget_and_tuple(member, uport, t2, dose, need, H, Sx, P))
    if x.get("eligible_needs") is False:
        return x, []
    try:
        x["observation"] = observation(member, uport, t2, need, x["Q1"], x["Q2"], P)
    except ValueError as e:              # a predicted FIRE without a measured latency
        x.update(observation=None, why_no_observation=str(e))
    x["t2"] = t2
    return x, []


def guarded(t, cells, Q, reads, ports, P):
    """P.guarded generalised in one point (3.5.5): per cell its own ports (`ports[c]`) and fitted reads (`reads[c]`).
    With every cell on ports (1, 2) and reads P.GUARDED_READS_1 (or the line ports and GUARDED_READS_2) it builds the
    same rows in the same order as P.guarded."""
    names = [f"h_{c}" for c in cells] + [f"g_{c}{p}" for c in cells for p in ports[c]] + ["d"]
    rows, rhs = [], []
    for c in cells:
        for k in range(Q + 1):
            for r in reads[c]:
                row = [0] * len(names)
                row[names.index(f"h_{c}")] = 1
                for p in P.ports(r):
                    row[names.index(f"g_{c}{p}")] = 1
                    row[-1] += k
                rows.append(row)
                rhs.append(t[(c, k, r)]["Z"])
    xsol = P.solve(rows, rhs)
    v = {n: round(val) for n, val in zip(names, xsol)}
    return dict(help={c: v[f"h_{c}"] for c in cells}, gain={(c, p): v[f"g_{c}{p}"] for c in cells for p in ports[c]}, dose=v["d"])


def budget_and_tuple(member, uport, t, dose, n, H, Sx, P):
    """3.5.4 (Q1, Q2), 3.5.5 and 3.5.6."""
    import c4
    kd = kinds(member)
    nl = len(kd)
    L1 = tuple(kd)
    out = {}
    Q1 = max(n[c] for c in L1) + 2
    Q2 = max(n[f"c{p}"] for p in range(1, nl + 1)) + 2
    out.update(Q1=Q1, Q2=Q2)
    if Q1 > 7 or Q2 > 7:
        out.update(eligible_needs=False, why_not_eligible=[f"Q1 = {Q1}, Q2 = {Q2}: above 7"])
        return out
    port1 = {c: ((1, 2) if k == "pair" else (uport[c],)) for c, k in kd.items()}
    reads1 = {c: (P.GUARDED_READS_1 if k == "pair" else ("empty", f"port {uport[c]}")) for c, k in kd.items()}
    cports = tuple(range(1, nl + 1))
    reads2 = P.GUARDED_READS_2 if nl == 2 else ("empty", "port 1")
    g1 = guarded(t, L1, Q1, reads1, port1, P)
    g2 = guarded(t, ("c",), Q2, {"c": reads2}, {"c": cports}, P)
    tup = dict(help={**g1["help"], **g2["help"]}, gain={**g1["gain"], **g2["gain"]}, dose={**{c: g1["dose"] for c in L1}, "c": g2["dose"]})
    lay = lambda c: dict(help=tup["help"], gain=tup["gain"], dose=tup["dose"][c])
    eps = {}
    for c in L1:
        eps[c] = max(abs(t[(c, k, r)]["Z"] - P.G(lay(c), c, k, P.ports(r))) for k in range(Q1 + 1) for r in reads1[c])
    eps["c"] = max(abs(t[("c", k, r)]["Z"] - P.G(lay("c"), "c", k, P.ports(r))) for k in range(Q2 + 1) for r in reads2)
    sens = {(c, p): P.sensitivity(lay(c), dose, c, p) for c in L1 for p in port1[c]}
    sens.update({("c", p): P.sensitivity(lay("c"), dose, "c", p) for p in cports})
    budgets = {}
    for K in (0, 3):
        b = {}
        for c in L1:
            ss = [sens[(c, p)] for p in port1[c]]
            m = len(ss)
            tr = max(P.read_budget(eps[c], ss, [k] * m, K, c4.DECISION5) for k in range(n[c] + 1))
            te = P.read_budget(eps[c], ss, [n[c]] * m, K, c4.DECISION5)
            b[c] = dict(training=tr + H[c] + Sx[c], testing=te + H[c] + Sx[c])
        tr = max(P.read_budget(eps["c"], [sens[("c", p)]], [k], K, c4.DECISION5) for p in cports for k in range(n[f"c{p}"] + 1))
        te1 = max(P.read_budget(eps["c"], [sens[("c", p)]], [n[f"c{p}"]], K, c4.DECISION5) + H["c"] + Sx["c"] for p in cports)
        b["c"] = dict(training=tr + H["c"] + Sx["c"], testing=te1)
        if nl == 2:
            te2 = P.read_budget(eps["c"], [sens[("c", 1)], sens[("c", 2)]], [n["c1"], n["c2"]], K, c4.DECISION5) + H["c"] + Sx["c"]
            b["c"]["testing_two_ports_both_lines"] = te2       # reported only: the kernel's both-lines check has no error
        budgets[f"K{K}"] = b
    out.update(guarded=dict(help=tup["help"], gain={f"{c}{p}": v for (c, p), v in tup["gain"].items()}, dose=tup["dose"]),
               epsilon=eps, sensitivity={f"{c}{p}": str(v) for (c, p), v in sens.items()}, budgets=budgets)
    return out


# ---------------------------------------------------------------------------------------------- 3.5.8 the observation

def patterns(inputs):
    """The test patterns in dnf.patterns' order generalised: binary order with the first input least significant."""
    return [frozenset(n for i, n in enumerate(inputs) if m >> i & 1) for m in range(2 ** len(inputs))]


def observation(member, uport, t, n, Q1, Q2, P):
    """P.observation generalised by the member's wiring (3.5.8), in the same form (dates as strings of rationals)."""
    import c4
    spec_m = MEMBERS[member]
    inputs = spec_m["inputs"]
    kd = kinds(member)
    L1 = tuple(kd)
    nl = len(L1)
    wire = wiring(member, uport)
    target = {c: frozenset(spec_m["terms"][c]) for c in L1}
    Z = lambda c, k, r: t[(c, k, r)]["Z"]

    def lat(c, k, r):
        v = t[(c, k, r)]["latency"]
        if v is None:
            raise ValueError(f"a predicted FIRE without a measured latency: {(c, k, r)}")
        return P.q(v)

    def emc(k, r, start, fire):
        sl = t[("c", k, r)].get("slot_latencies")
        if sl is None:
            return [start + lat("c", k, r)] if fire else []
        if fire:
            assert lat("c", k, r) in sl, (k, r)
        return [start + x for x in sl]

    def rd(start, arrivals, emissions, value):
        return dict(start=str(start), arrivals=[None if a is None else str(a) for a in arrivals], emissions=[str(e) for e in emissions], value=int(value))

    def arr1(start, active):
        return [start if x in active else None for x in inputs]

    def read_of(c, active):
        return P.mask_read(tuple(sorted(p for i, p in wire[c].items() if i in active)))

    full = {c: full_read(kd[c], uport.get(c)) for c in L1}
    obs = dict(firstTrain=[], teach=[], secondTrain=[], firstTest={}, secondTest={}, scores={})
    for r in range(Q1 + 1):
        start = F(c4.SLOT * r)
        row = []
        for c in L1:
            k = min(r, n[c])
            fire = r >= n[c]
            row.append(rd(start, arr1(start, target[c]), [start + lat(c, k, full[c])] if fire else [], Z(c, k, full[c])))
        obs["firstTrain"].append(row)
    t0 = c4.SLOT * (Q1 + 1)
    writes = {a: 0 for a in range(nl)}
    lessons = [a for _ in range(Q2 + 1) for a in range(nl)]          # spec.lessons for one output cell
    for m, a in enumerate(lessons):
        line = L1[a]
        start = F(t0 + c4.SLOT * m)
        row, emission = [], None
        for c in L1:
            if c == line:
                e = start + lat(c, n[c], full[c])
                emission = e
                row.append(rd(start, arr1(start, target[line]), [e], Z(c, n[c], full[c])))
            else:
                row.append(rd(start, arr1(start, target[line]), [], Z(c, n[c], read_of(c, target[line]))))
        obs["teach"].append(row)
        arrive = emission + F(3, 2)
        cp = LINE_PORT[line]
        k = writes[a]
        fire = k >= n[f"c{cp}"]
        obs["secondTrain"].append(rd(arrive, [arrive if b == a else None for b in range(nl)], emc(k, f"port {cp}", arrive, fire), Z("c", k, f"port {cp}")))
        if not fire:
            writes[a] += 1
    t1 = t0 + c4.SLOT * len(lessons)
    nc = [n[f"c{LINE_PORT[c]}"] for c in L1]
    for i, x in enumerate(patterns(inputs)):
        key = "".join(sorted(x)) or "-"
        start = F(t1 + c4.SLOT * i)
        row, em = [], {}
        for c in L1:
            read = read_of(c, x)
            fire = read == full[c]
            e = [start + lat(c, n[c], full[c])] if fire else []
            em[c] = e[0] if e else None
            row.append(rd(start, arr1(start, x), e, Z(c, n[c], read)))
        obs["firstTest"][key] = row
        if nl == 2:
            n1, n2 = nc
            scores = {"-": Z("c", max(n1, n2), "empty"), "1": Z("c", n1, "port 1"), "2": Z("c", n2, "port 2"),
                      "12": min(Z("c", min(n1, n2), "both"), Z("c", min(n1, n2), P.SKEWED))}
        else:
            scores = {"-": Z("c", nc[0], "empty"), "1": Z("c", nc[0], "port 1")}
        obs["scores"][key] = scores
        arrivals = [None if em[c] is None else em[c] + F(3, 2) for c in L1]
        got = [a for a in arrivals if a is not None]
        mask = "".join(str(LINE_PORT[c]) for c, a in zip(L1, arrivals) if a is not None) or "-"
        if not got:
            obs["secondTest"][key] = rd(start + F(3, 2), arrivals, emc(max(nc), "empty", start + F(3, 2), False), scores["-"])
        else:
            first, last = min(got), max(got)
            if mask == "12":
                skewed = last - first > F(15, 100)
                e = emc(min(nc), P.SKEWED if skewed else "both", first, True)
            else:
                pp = int(mask)
                e = emc(n[f"c{pp}"], f"port {pp}", first, True)
            obs["secondTest"][key] = rd(first, arrivals, e, scores[mask])
    return obs


# ---------------------------------------------------------------------------------------------- 3.5.9 the gate

def raw_spec(x, tag, source):
    """The generator spec (spec.load input) of a predicted (instance, member)."""
    predict6, P, spec, *_ = mods()
    member = x["member"]
    m = MEMBERS[member]
    inputs = m["inputs"]
    L1 = tuple(kinds(member))
    A, M = len(L1), len(inputs)
    wire = wiring(member, x["unary_ports"])
    g, h, d = x["guarded"]["gain"], x["guarded"]["help"], x["guarded"]["dose"]
    o = x["observation"]
    budgets = {K: dict(first=dict(training=[x["budgets"][K][c]["training"] for c in L1], testing=[x["budgets"][K][c]["testing"] for c in L1]),
                       second=dict(training=[x["budgets"][K]["c"]["training"]], testing=[x["budgets"][K]["c"]["testing"]])) for K in ("K0", "K3")}
    key = lambda xs: "".join(sorted(xs)) or "-"
    lkey = lambda ys: "".join(str(LINE_PORT[L1[a]]) for a in sorted(ys)) or "-"
    tstr = lambda q: {k: str(v) for k, v in q.items()}
    return dict(
        tag=tag, shape=dict(A=A, B=1, M=M), inputs=list(inputs),
        first=dict(cells=list(L1), terms=[sorted(inputs.index(i) for i in m["terms"][c]) for c in L1],
                   initialGain=[[g[f"{c}{wire[c][i]}"] if i in wire[c] else 0 for i in inputs] for c in L1],
                   help=[h[c] for c in L1], threshold=[P.THETA] * A, dose=d[L1[0]], maxWrites=x["Q1"], rail=P.RAIL),
        second=dict(cells=["c"], lines=[list(range(A))], alwaysFire=[False], initialGain=[[g[f"c{LINE_PORT[c]}"] for c in L1]],
                    help=[h["c"]], threshold=[P.THETA], dose=d["c"], maxWrites=x["Q2"], rail=P.RAIL),
        delay=[["3/2"] * A], heldOut=[],
        timing=dict(left=tstr(dict(skew=P.SKEW_A, deadline=P.DEADLINE_A, duration=P.DURATION_A)),
                    right=tstr(dict(skew=P.SKEW_C, deadline=P.DEADLINE_C, duration=P.DURATION_C))),
        budgets=budgets,
        observation=dict(
            firstTrain=o["firstTrain"], teach=o["teach"], secondTrain=o["secondTrain"],
            firstTest=[o["firstTest"][key({inputs[j] for j in spec.mask_of(wi, M)})] for wi in range(2 ** M)],
            secondTest=[[o["secondTest"][key({inputs[j] for j in spec.mask_of(wi, M)})]] for wi in range(2 ** M)],
            scores=[[[o["scores"][key({inputs[j] for j in spec.mask_of(wi, M)})][lkey(spec.mask_of(y, A))] for y in range(2 ** A)]] for wi in range(2 ** M)]),
        lean=dict(style="generic", namespace=GEN_NAMESPACE, source=source, derive=True))


def mirror_verdicts(s):
    _, _, _, mirror, _ = mods()
    v = mirror.verdicts(s)
    return {K: dict(checks=c, per_checker=pc, failing=[list(f) for f in fl]) for K, (c, pc, fl) in v.items()}


def lean_gate(s, mv, out_dir, gen, lean, build):
    """The Lean file with the mirror's values asserted, checked by the generator's gencheck.sh (C5/check.sh steps 1
    and 3). If it fails, the other three (K0, K3) combinations of `checks` are tried, without per-checker theorems;
    the one that passes is the kernel's verdict. Returns dict(kernel={K0, K3} or None, files, logs)."""
    _, _, _, _, emit = mods()
    gdir = Path(gen).resolve() / "research" / "learned-dnf-generator"
    env = dict(os.environ, LEAN=str(lean), GENCHECK_BUILD=str(build), PYTHON=sys.executable)
    tag = s["tag"]
    tries = [((mv["K0"]["checks"], mv["K3"]["checks"]), True)]
    tries += [((a, b), False) for a in (True, False) for b in (True, False) if (a, b) != tries[0][0]]
    res = dict(kernel=None, attempts=[])
    for n, ((v0, v3), per) in enumerate(tries):
        name = f"Family_{tag}" + ("" if n == 0 else f"_try{n}")
        f = Path(out_dir) / f"{name}.lean"
        pc = {(tag, K): mv[K]["per_checker"] for K in ("K0", "K3")} if per else None
        f.write_text(emit.lean_file([s], {(tag, "K0"): v0, (tag, "K3"): v3}, s["lean"]["source"], pc))
        p = subprocess.run(["bash", str(gdir / "gencheck.sh"), str(f)], capture_output=True, text=True, env=env)
        (Path(out_dir) / f"{name}.log").write_text(p.stdout + p.stderr)
        res["attempts"].append(dict(file=f.name, asserted=dict(K0=v0, K3=v3), per_checker=per, passed=p.returncode == 0))
        if p.returncode == 0:
            res["kernel"] = dict(K0=v0, K3=v3)
            res["kernel_agrees_with_mirror"] = n == 0
            break
    return res


# ---------------------------------------------------------------------------------------------- the batch

def b2_inputs(seed, b2_dir, b2_stat):
    """B2's runs of one instance: {(cell, kind): result or None}, and the source's statuses."""
    runs = {}
    for c in ("a", "b"):
        runs[(c, "pair")] = result_of(b2_stat, b2_dir, f"{seed}-scan-{c}-pair")
        runs[(c, "onesided")] = result_of(b2_stat, b2_dir, f"{seed}-onesided-{c}")
    for ln in ("line1", "line2"):
        runs[("c", ln)] = result_of(b2_stat, b2_dir, f"{seed}-scan-c-{ln}")
    runs[("c", "bothfire")] = result_of(b2_stat, b2_dir, f"{seed}-bothfire-c")
    return runs


def b2_run_ids(seed, member):
    kd = kinds(member)
    ids = [f"{seed}-cal-on", f"{seed}-cal-off"]
    for c, k in kd.items():
        if k == "pair":
            ids += [f"{seed}-scan-{c}-pair", f"{seed}-onesided-{c}"]
    ids += [f"{seed}-scan-c-line{p}" for p in range(1, len(kd) + 1)]
    if len(kd) == 2:
        ids.append(f"{seed}-bothfire-c")
    return ids


def tu_run_ids(seed, member, uport):
    kd = kinds(member)
    if "unary" not in kd.values():
        return []
    ids = [f"{seed}-cal-on-unary", f"{seed}-cal-off-unary"]
    for c, k in kd.items():
        if k == "unary":
            ids += [f"{seed}-unary-scan-{c}{uport[c]}", f"{seed}-preset-{c}"]
    return ids


def one_seed(seed, members, b2_dir, tdirs, b2_stat, tstat, b2src=None, tusrc=None):
    """Every member of one instance. b2src, tusrc: sources already read (tests), else read from disk."""
    b2_runs = b2_inputs(seed, b2_dir, b2_stat)
    un = unary_inputs(seed, tdirs, tstat) if tdirs else None
    out = dict(seed=seed, unary=None if un is None else {c: v["detail"] for c, v in un.items()}, members={})
    b2 = None
    tu = None
    for member in members:
        kd = kinds(member)
        needs_tu = "unary" in kd.values()
        if needs_tu and un is None:
            out["members"][member] = dict(member=member, seed=seed, measured=False, why_not_measured=["no top-up measures given"])
            continue
        uport = {c: un[c]["port"] for c, k in kd.items() if k == "unary"} if needs_tu else {}
        ids_b2 = b2_run_ids(seed, member)
        st_b2 = {i: b2_stat.get(i, "missing") for i in ids_b2}
        for i in ids_b2:
            if st_b2[i] == "complete" and not (Path(b2_dir) / i / "record.json").exists():
                st_b2[i] = "listed complete but missing on disk"
        ids_tu = tu_run_ids(seed, member, uport)
        st_tu = {i: tstat.get(i, "missing") for i in ids_tu}
        for i in ids_tu:
            if st_tu[i] == "complete" and not (find_run(tdirs, i) / i / "record.json").exists():
                st_tu[i] = "listed complete but missing on disk"
        if any(v != "complete" for v in st_b2.values()) or any(v != "complete" for v in st_tu.values()):
            bad = [f"run {i} did not complete: {s}" for i, s in sorted({**st_b2, **st_tu}.items()) if s != "complete"]
            out["members"][member] = dict(member=member, seed=seed, measured=False, why_not_measured=bad)
            continue
        if b2 is None:
            b2 = b2src or source(Path(b2_dir) / f"{seed}-cal-on", Path(b2_dir) / f"{seed}-cal-off")
        if needs_tu and tu is None:
            d = find_run(tdirs, f"{seed}-cal-on-unary")
            tu = tusrc or source(d / f"{seed}-cal-on-unary", d / f"{seed}-cal-off-unary", unary=True)
        tu_runs = {}
        if un is not None:
            for c in ("a", "b"):
                tu_runs[(c, "unary")] = un[c]["scans"][un[c]["port"]]
                tu_runs[(c, "preset")] = un[c]["preset"]
        x, why = predict(member, seed, dict(b2, status=st_b2), b2_runs, dict(tu, status=st_tu) if needs_tu else None, tu_runs, uport)
        x["why_not_measured"] = why
        out["members"][member] = x
    return out


def gate_all(rows, out_dir, gen, lean, build, do_lean=True):
    """The spec, the mirror and (do_lean) the kernel for every measured (instance, member) with an observation."""
    _, _, spec, *_ = mods()
    for row in rows:
        for member, x in row["members"].items():
            x["room_K3"] = False
            if not x.get("measured") or x.get("eligible_needs") is False or not x.get("observation"):
                continue
            tag = f"{member}_{row['seed']}"
            try:
                s = spec.load(raw_spec(x, tag, f"family_predict.py, member {member}, instance {row['seed']}"))
            except spec.SpecError as e:
                x["spec_refused"] = str(e)
                continue
            x["two_port"] = s["physical"]
            mv = mirror_verdicts(s)
            x["mirror"] = mv
            if do_lean:
                x["gate"] = lean_gate(s, mv, out_dir, gen, lean, build)
                k = x["gate"]["kernel"]
                x["room_K3"] = bool(k and k["K3"])
                x["gate_K0"] = bool(k and k["K0"])
            else:
                x["room_K3_mirror_only"] = mv["K3"]["checks"]


def summary(rows, members):
    """r_m per member (TOPUP_RULES.md 2), with the removal and the size rule."""
    r = {m: [row["seed"] for row in rows if row["members"].get(m, {}).get("room_K3")] for m in members}
    kept = [m for m in members if len(r[m]) > 1]
    size = None
    if len(kept) >= 3:
        I = math.ceil(F(30, min(len(r[m]) for m in kept)))
        size = I + (-I) % len(kept)
    return dict(r_m={m: len(v) for m, v in r.items()}, with_room=r, removed=[m for m in members if m not in kept],
                kept=kept, campaign=size is not None, I=size)


def strip(x):
    return {k: v for k, v in x.items() if k not in ("t2",)}


def main():
    a = sys.argv[1:]
    assert __debug__, "refused: not with python -O, the guards are asserts"
    if a and a[0] == "ports":
        tdirs = a[1].split(os.pathsep)
        tstat = statuses(*tdirs)
        print(json.dumps({str(s): {c: v["detail"] for c, v in unary_inputs(s, tdirs, tstat).items()} for s in SEEDS}, indent=1, default=str))
        return
    if a and a[0] == "predict":
        repo, gen, b2_dir, tdir, out = a[1], a[2], Path(a[3]), a[4], Path(a[5])
        do_lean = "--no-lean" not in a
        paths(repo, gen)
        tdirs = tdir.split(os.pathsep)
        out.mkdir(parents=True, exist_ok=True)
        b2_stat, tstat = statuses(b2_dir), statuses(*tdirs)
        rows = [one_seed(s, STEP1, b2_dir, tdirs, b2_stat, tstat) for s in SEEDS]
        lean = os.environ.get("LEAN", "lean")
        gate_all(rows, out, gen, lean, out / "build", do_lean)
        res = dict(summary=summary(rows, STEP1), instances=[dict(r, members={m: strip(x) for m, x in r["members"].items()}) for r in rows])
        (out / "PREDICTIONS.json").write_text(json.dumps(res, indent=1, default=str) + "\n")
        print(json.dumps(res["summary"], indent=1))
        return
    raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
