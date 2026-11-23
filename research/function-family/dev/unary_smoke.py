"""Development only: a smoke of the UNARY first-layer cell on instance 8303, at twice the dose and reltol 1e-5.
A first-layer cell (a or b) read on ONE port at the line amplitude 1.0, the realisation (ii) of FAMILY_DESIGN.md 2.5.
Measures only, no network run. Not campaign code, not preregistered, and it counts nothing.

It edits no file of the repository and writes nothing inside it. The frozen functions are called unchanged:
batch6.cal for the deck, scan6.main for the scans and the preset checks. For the time of each call these are wrapped,
and nothing else:
  - as batch2x.py does: net.deck (vhi=0.7, reltol=1e-5, by dosedev2.window and dosedev_tol.tolerance) and
    batch6.guard_seed (batch2x.guard_seed, narrowed here to 8303 alone);
  - for the deck: plans4.calibration, replaced by `calibration` below. It is the frozen plan with ONE added read per
    stage, `UNARY` ("port 1 at 1.0"), in which a and b each get one pulse on port 1 at 1.0 and c gets none, gated
    read-only like every other read. The other slots are the frozen plan's, in the frozen order;
  - for the scans and the preset checks: scan6.amp and scan6.kinds_of, so that the scanned cell (a or b) is pulsed at
    1.0 and may be scanned as "line1" (port 1 alone, moving port 1 alone). c is never scanned here.

  unary_smoke.py cal    REPO OUT NGSPICE PDK            the guard-on deck of 8303 with the UNARY reads
  unary_smoke.py scan   REPO OUT CELL D1_V D2_V NGSPICE PDK     the unary scan of CELL (a or b): scan6 "line1", delta 1/2
  unary_smoke.py preset REPO OUT CELL D1_V D2_V NGSPICE PDK     the preset check of CELL: scan6 "onesided" at s = 0 for
                                                                both ports, each alone, at 1.0 (port 1's read decides)
  unary_smoke.py plan   REPO RUNS NGSPICE PDK            prints the runs and their limits; runs nothing
  unary_smoke.py run    REPO RUNS NGSPICE PDK            W1 (the deck), then, only if W1 is complete and its doses
                                                         usable, W2 (two scans, two preset checks); each run once
  unary_smoke.py report RUNS                             what the runs say; decides nothing

The stop condition: a run that fails (a deck or scan that does not converge exits non-zero) or is cut at its limit
(twice its expected time) stops the smoke: W2 is not started if W1 is not complete, and nothing is ever started twice.
"""
import contextlib
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
SEED = 8303
UNARY = "port 1 at 1.0"
CELLS_UNARY = ("a", "b")
SCAN_DELTA = "1/2"                                       # as batch2x's line scans of c
# Expected wall times (s): B2's own runs of 8303 [BATCH2X_REPORT.json wall_times]: cal-on 1 638 s, times 7/6 for the
# added read slot per stage (7 slots against 6); c's line scans 648 and 574 s; c's both-lines check 56 s (one read at
# s = 0), so 80 s for the preset check's two reads at s = 0. The limit is twice the expected time, up to 10 s.
EXPECTED_S = {"cal-on-unary": F(1638) * F(7, 6), "unary-scan": F(650), "preset": F(80)}


def limit_s(kind):
    return 10 * math.ceil(2 * EXPECTED_S[kind] / 10)


def paths(repo):
    """The development code of the follow-up (dosedev*.py) and of the prep (batch2x.py) must be importable: put
    their dev/ folders on PYTHONPATH. REPO is a checkout holding campaign 6's code (the -impl branch at ecfcd1c1)."""
    import batch2x                                       # noqa: F401  (PREP dev)
    import dosedev2
    dosedev2.repo_paths(repo)


def guard_seed(text):
    assert text == str(SEED), f"refused: this smoke is for instance {SEED} alone, not {text!r}"
    return SEED


@contextlib.contextmanager
def seed_guard():
    """batch6.guard_seed, for the block: this smoke's guard (8303 only)."""
    import batch6
    frozen = batch6.guard_seed
    assert frozen.__module__ == "batch6", "refused: batch6.guard_seed is already replaced"
    batch6.guard_seed = guard_seed
    try:
        yield
    finally:
        batch6.guard_seed = frozen


def calibration():
    """plans4.calibration with the UNARY read added after the frozen reads of each stage, before its joint dose."""
    import c4
    import plans4
    from c4 import dnf
    t, plan, reads = 0.0, dict(cells=list(c4.CELLS), gates=[], sources=[], edges=[]), []
    for k in range(c4.STAGES):
        for name, offsets in plans4.CAL_READS + ((UNARY, {1: 0}),):
            plan["gates"].append((t - c4.GATE_LEAD, plans4.gates(())))
            for c in c4.CELLS:
                if name.startswith("both, second") and c != "c":
                    continue
                if name == UNARY:
                    if c not in CELLS_UNARY:
                        continue
                    amp = c4.AMP_OR
                else:
                    amp = c4.AMP_OR if c == "c" else c4.AMP_AND
                for p, off in offsets.items():
                    plan["sources"].append((t + off, c, p, amp))
            reads.append(dict(stage=k, read=name, date=t, gated=True))
            t += c4.SLOT
        plan["gates"].append((t - c4.GATE_LEAD, plans4.gates(c4.CELLS)))
        for c in c4.CELLS:
            for p in (1, 2):
                plan["sources"].append((t, c, p, 0.0))
        reads.append(dict(stage=k, read="joint dose", date=t, gated=False))
        t += c4.SLOT
    plan["horizon"] = t + dnf.SETTLE
    return plan, reads


@contextlib.contextmanager
def unary_plan():
    import plans4
    frozen = plans4.calibration
    assert frozen.__module__ == "plans4", "refused: plans4.calibration is already replaced"
    plans4.calibration = calibration
    try:
        yield
    finally:
        plans4.calibration = frozen


@contextlib.contextmanager
def unary_amplitude(cell):
    """scan6.amp gives 1.0 for `cell`, and scan6.kinds_of lets `cell` be scanned as line1; c unchanged."""
    import c4
    import scan6
    assert cell in CELLS_UNARY, f"refused: the unary cell is a or b, not {cell!r}"
    fa, fk = scan6.amp, scan6.kinds_of
    assert fa.__module__ == "scan6" and fk.__module__ == "scan6", "refused: scan6 is already wrapped"
    scan6.amp = lambda c: c4.AMP_OR if c == cell else fa(c)
    scan6.kinds_of = lambda c: ("line1",) if c == cell else fk(c)
    try:
        yield
    finally:
        scan6.amp, scan6.kinds_of = fa, fk


def cal(repo, out, ngspice, pdk):
    assert __debug__, "refused: not with python -O, the guards are asserts"
    paths(repo)
    import batch2x
    import batch6
    import c4
    import dosedev2
    import dosedev_tol
    dosedev2.outside(repo, out)
    print(c4.require_pinned())
    seen = []
    with dosedev_tol.tolerance(), dosedev2.window(batch2x.PARAMS, seen), unary_plan():
        rec = batch6.cal(Path(out), guard_seed(str(SEED)), "on", Path(ngspice), Path(pdk))
    dosedev2.sidecar(out, f"unary smoke: guard-on calibration deck of {SEED} with the read {UNARY!r} on a and b "
                          "(batch6.cal frozen, plans4.calibration replaced by unary_smoke.calibration)", seen)
    return rec


def scan_kind(repo, out, cell, kind, args, ngspice, pdk):
    assert __debug__, "refused: not with python -O, the guards are asserts"
    assert kind in ("line1", "onesided"), kind
    paths(repo)
    import batch2x
    import dosedev2
    import dosedev_tol
    import scan6
    dosedev2.outside(repo, out)
    seen = []
    with seed_guard(), dosedev_tol.tolerance(), dosedev2.window(batch2x.PARAMS, seen), unary_amplitude(cell):
        rec = scan6.main([str(out), str(SEED), cell, kind, *args, str(ngspice), str(pdk)])
    what = "unary scan (line1, port 1 at 1.0)" if kind == "line1" else "preset check (each port alone at 1.0, s = 0)"
    dosedev2.sidecar(out, f"unary smoke: {what} of {cell}, seed {SEED} (scan6.main frozen, scan6.amp and kinds_of wrapped)", seen)
    return rec


def doses_from_on(repo, on_dir):
    """D_p of a and b (V, as strings, as schedule6 writes them) from the guard-on deck alone: the mean joint-dose
    move of each port over its 8 stages (predict6.doses_V), read with campaign 5's P.load(on, on) as predict6.deck_w
    does. Returns ({cell: (D1, D2)}, problems): a missing joint dose is a problem."""
    paths(repo)
    import predicted as P
    import predict6
    rows, _ = P.load(on_dir, on_dir)
    _, dose, bad = P.table(rows, rows)
    bad = [b for b in bad if b.startswith("missing joint dose")]
    if bad:
        return None, bad
    D = predict6.doses_V(dose)
    return {c: tuple(repr(float(D[(c, p)]) / 1000) for p in (1, 2)) for c in CELLS_UNARY}, []


def jobs(repo, runs, ngspice, pdk, doses=None):
    """W1 when doses is None; else W2 with {cell: (D1_V, D2_V)}."""
    py, me = sys.executable, str(Path(__file__).resolve())
    runs = Path(runs)
    if doses is None:
        return [dict(id=f"{SEED}-cal-on-unary", kind="cal-on-unary", limit_s=limit_s("cal-on-unary"), expected_s=float(EXPECTED_S["cal-on-unary"]),
                     argv=[py, "-B", me, "cal", str(repo), str(runs / f"{SEED}-cal-on-unary"), str(ngspice), str(pdk)])]
    out = []
    for cell in CELLS_UNARY:
        out.append(dict(id=f"{SEED}-unary-scan-{cell}", kind="unary-scan", limit_s=limit_s("unary-scan"), expected_s=float(EXPECTED_S["unary-scan"]),
                        argv=[py, "-B", me, "scan", str(repo), str(runs / f"{SEED}-unary-scan-{cell}"), cell, *doses[cell], str(ngspice), str(pdk)]))
        out.append(dict(id=f"{SEED}-preset-{cell}", kind="preset", limit_s=limit_s("preset"), expected_s=float(EXPECTED_S["preset"]),
                        argv=[py, "-B", me, "preset", str(repo), str(runs / f"{SEED}-preset-{cell}"), cell, *doses[cell], str(ngspice), str(pdk)]))
    return out


def run(repo, runs, ngspice, pdk):
    """W1, then W2 only if W1 is complete and its deck gives the doses. Each wave once (dosedev2.many)."""
    assert __debug__, "refused: not with python -O, the guards are asserts"
    paths(repo)
    import batch2x
    import dosedev2
    runs = Path(runs)
    dosedev2.outside(repo, runs)
    assert not runs.exists(), f"refused: {runs} exists; the smoke is run once"
    runs.mkdir(parents=True)
    s1 = batch2x.run_wave(runs, "W1", jobs(repo, runs, ngspice, pdk))
    out = dict(W1=s1)
    if s1.get(f"{SEED}-cal-on-unary") != "complete":
        out["stopped"] = "W1 is not complete: W2 is not started"
    else:
        D, bad = doses_from_on(repo, runs / f"{SEED}-cal-on-unary")
        if D is None:
            out["stopped"] = "the deck's doses are not usable: " + "; ".join(bad[:3])
        else:
            (runs / "DOSES.json").write_text(json.dumps(D, indent=1) + "\n")
            out["W2"] = batch2x.run_wave(runs, "W2", jobs(repo, runs, ngspice, pdk, D))
    (runs / "RUN.json").write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps(out))
    return out


def report(runs, b2_doses=None):
    """What the runs say, and nothing decided: the deck's UNARY reads (FIRE per stage), each scan's crossing, each
    preset check, the doses against B2's (if b2_doses is given: {cell: (D1, D2)} in V)."""
    runs = Path(runs)
    out = dict(seed=SEED, what="unary smoke on 8303; development; decides nothing")
    deck = runs / f"{SEED}-cal-on-unary" / "record.json"
    if deck.exists():
        rec = json.loads(deck.read_text())
        out["deck"] = dict(wall_s=rec["wall_s"], reached=rec["reached_its_last_date"], unary_reads=sum(r["read"] == UNARY for r in rec["reads"]))
    for cell in CELLS_UNARY:
        for kind in ("unary-scan", "preset"):
            p = runs / f"{SEED}-{kind}-{cell}" / "record.json"
            if p.exists():
                r = json.loads(p.read_text())
                out[f"{kind}-{cell}"] = dict(wall_s=r["wall_s"], result=r["result"])
    if b2_doses and (runs / "DOSES.json").exists():
        D = json.loads((runs / "DOSES.json").read_text())
        out["doses_minus_B2_uV"] = {c: [round((float(D[c][i]) - float(b2_doses[c][i])) * 1e6, 3) for i in (0, 1)] for c in CELLS_UNARY}
    return out


def unary_fires(repo, on_dir):
    """FIRE of the UNARY read of a and b at each stage of the deck (from the guard-on rows): {cell: [bool x 8]}."""
    paths(repo)
    import predicted as P
    rows, _ = P.load(on_dir, on_dir)
    by = {(r["cell"], r["stage"], r["read"]): r for r in rows}
    return {c: [bool(by[(c, k, UNARY)]["fire"]) for k in range(8)] for c in CELLS_UNARY}


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "cal":
        cal(a[1], a[2], a[3], a[4])
    elif a and a[0] == "scan":
        scan_kind(a[1], a[2], a[3], "line1", [SCAN_DELTA, a[4], a[5]], a[6], a[7])
    elif a and a[0] == "preset":
        scan_kind(a[1], a[2], a[3], "onesided", ["0", "0", a[4], a[5]], a[6], a[7])
    elif a and a[0] == "plan":
        paths(a[1])
        w1 = jobs(a[1], a[2], a[3], a[4])
        w2 = jobs(a[1], a[2], a[3], a[4], {c: ("<D1 of the new deck>", "<D2 of the new deck>") for c in CELLS_UNARY})
        for n, w in (("W1", w1), ("W2", w2)):
            for j in w:
                print(n, j["id"], f"expected {j['expected_s']:.0f} s", f"limit {j['limit_s']} s", " ".join(j["argv"][3:]))
        allj = w1 + w2
        print(json.dumps(dict(runs=len(allj), sum_expected_s=round(sum(j["expected_s"] for j in allj)),
                              wall_expected_s=round(w1[0]["expected_s"] + max(j["expected_s"] for j in w2)))))
    elif a and a[0] == "run":
        run(a[1], a[2], a[3], a[4])
    elif a and a[0] == "report":
        print(json.dumps(report(a[1]), indent=1))
    else:
        raise SystemExit(__doc__)
