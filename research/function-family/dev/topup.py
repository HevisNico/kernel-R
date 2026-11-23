"""Development only: the TOP-UP of B2's ten instances (8301-8310) with the unary measures of the step-1 family
(FAMILY_DESIGN.md section 0; the rules in ../TOPUP_RULES.md; the machines in ../MACHINE_PLAN.md). Measures only, no
network run. Not campaign code, not preregistered, and it counts nothing by itself: what it measures is read only by
the rules of TOPUP_RULES.md.

Per instance, at twice the dose and reltol 1e-5 (batch2x's rewrite, unchanged):
  W1  the guard-on and the guard-off calibration decks, each with TWO added reads per stage: port 1 of a and b at
      1.0, then port 2 of a and b at 1.0 (c not pulsed, gated read-only), before the stage's joint dose;
  W2  four unary scans (a port 1, a port 2, b port 1, b port 2: scan6 "line1"/"line2" at 1.0, delta 1/2), with D_p
      from the instance's new guard-on deck; and two preset checks (a, b: each port alone at 1.0 at s = 0).
The frozen functions are called unchanged (batch6.cal, scan6.main). For the time of each call these are wrapped, and
nothing else: net.deck and dosedev.rewrite (batch2x's 2x and 1e-5 rewrite), batch6.guard_seed (this file's guard:
8301-8310 only), plans4.calibration (this file's `calibration`), scan6.amp and scan6.kinds_of (the scanned cell at 1.0,
scannable as line1 and line2).

  topup.py cal    REPO OUT SEED on|off NGSPICE PDK
  topup.py scan   REPO OUT SEED CELL PORT D1_V D2_V NGSPICE PDK
  topup.py preset REPO OUT SEED CELL D1_V D2_V NGSPICE PDK
  topup.py plan   REPO RUNS NGSPICE PDK SEED...          the runs of these instances and their limits; runs nothing
  topup.py worker REPO RUNS NGSPICE PDK SEED...          W1 for these instances, then W2 for each instance whose two
                                                         decks completed and whose guard-on deck gives its doses
  topup.py dup    REPO RUNS NGSPICE PDK SEED              the duplicate guard-on deck of SEED (MACHINE_PLAN.md 2)
  topup.py compare RUN_DIR_1 RUN_DIR_2                    the duplicate's comparison (MACHINE_PLAN.md 2)

Stop rule: a run that fails (non-zero exit: a deck or scan that does not converge) or is cut at its limit (twice its
expected time) is never repeated; the W2 runs of its instance are not started (listed in RUNS/NOT_STARTED_W2.json).
"""
import contextlib
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import sys

SEEDS = tuple(range(8301, 8311))                          # B2's ten instances, never extended
UNARY = {1: "port 1 at 1.0", 2: "port 2 at 1.0"}
CELLS_UNARY = ("a", "b")
SCAN_DELTA = "1/2"
# Expected wall times (s). Decks: B2's mean for 8301-8310 [BATCH2X_REPORT.json] times 8/6 (two added read slots per
# stage, 8 slots against 6); the smoke's guard-on deck with one added slot took 1 778 s on 8303 against B2's 1 638 s.
# Scans: the smoke's unary scans, 576 and 572 s, and B2's line scans of c, up to 668 s: 650 s. Preset: the smoke's
# 52 and 54 s: 80 s. The limit is twice the expected time, up to 10 s.
EXPECTED_S = {"cal-on": F(1662) * F(8, 6), "cal-off": F(1206) * F(8, 6), "unary-scan": F(650), "preset": F(80)}


def limit_s(kind):
    return 10 * math.ceil(2 * EXPECTED_S[kind] / 10)


def paths(repo):
    import batch2x                                        # noqa: F401  (PREP dev)
    import dosedev2
    dosedev2.repo_paths(repo)


def guard_seed(text):
    seed = int(text)
    assert str(seed) == text and seed in SEEDS, f"refused: {text!r} is not one of B2's instances 8301 to 8310"
    return seed


@contextlib.contextmanager
def seed_guard():
    import batch6
    frozen = batch6.guard_seed
    assert frozen.__module__ == "batch6", "refused: batch6.guard_seed is already replaced"
    batch6.guard_seed = guard_seed
    try:
        yield
    finally:
        batch6.guard_seed = frozen


def calibration():
    """plans4.calibration with the two UNARY reads (port 1, then port 2, of a and b at 1.0) added after the frozen
    reads of each stage, before its joint dose. c is not pulsed in those slots."""
    import c4
    import plans4
    from c4 import dnf
    extra = tuple((UNARY[p], {p: 0}) for p in (1, 2))
    t, plan, reads = 0.0, dict(cells=list(c4.CELLS), gates=[], sources=[], edges=[]), []
    for k in range(c4.STAGES):
        for name, offsets in plans4.CAL_READS + extra:
            plan["gates"].append((t - c4.GATE_LEAD, plans4.gates(())))
            for c in c4.CELLS:
                if name.startswith("both, second") and c != "c":
                    continue
                if name in UNARY.values():
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
    """scan6.amp gives 1.0 for `cell`; scan6.kinds_of lets `cell` be scanned as line1 and line2; c unchanged."""
    import c4
    import scan6
    assert cell in CELLS_UNARY, f"refused: the unary cell is a or b, not {cell!r}"
    fa, fk = scan6.amp, scan6.kinds_of
    assert fa.__module__ == "scan6" and fk.__module__ == "scan6", "refused: scan6 is already wrapped"
    scan6.amp = lambda c: c4.AMP_OR if c == cell else fa(c)
    scan6.kinds_of = lambda c: ("line1", "line2") if c == cell else fk(c)
    try:
        yield
    finally:
        scan6.amp, scan6.kinds_of = fa, fk


def cal(repo, out, seed, guard, ngspice, pdk):
    assert __debug__, "refused: not with python -O, the guards are asserts"
    paths(repo)
    import batch2x
    import batch6
    import c4
    import dosedev2
    import dosedev_tol
    dosedev2.outside(repo, out)
    seed = guard_seed(str(seed))
    assert guard in ("on", "off"), guard
    print(c4.require_pinned())
    seen = []
    with dosedev_tol.tolerance(), dosedev2.window(batch2x.PARAMS, seen), unary_plan():
        rec = batch6.cal(Path(out), seed, guard, Path(ngspice), Path(pdk))
    dosedev2.sidecar(out, f"top-up: guard-{guard} calibration deck of {seed} with the reads {list(UNARY.values())} on a and b "
                          "(batch6.cal frozen, plans4.calibration replaced by topup.calibration)", seen)
    return rec


def scan_kind(repo, out, seed, cell, kind, args, ngspice, pdk):
    assert __debug__, "refused: not with python -O, the guards are asserts"
    assert kind in ("line1", "line2", "onesided"), kind
    paths(repo)
    import batch2x
    import dosedev2
    import dosedev_tol
    import scan6
    dosedev2.outside(repo, out)
    seed = guard_seed(str(seed))
    seen = []
    with seed_guard(), dosedev_tol.tolerance(), dosedev2.window(batch2x.PARAMS, seen), unary_amplitude(cell):
        rec = scan6.main([str(out), str(seed), cell, kind, *args, str(ngspice), str(pdk)])
    what = f"unary scan ({kind} at 1.0)" if kind != "onesided" else "preset check (each port alone at 1.0, s = 0)"
    dosedev2.sidecar(out, f"top-up: {what} of {cell}, seed {seed} (scan6.main frozen, scan6.amp and kinds_of wrapped)", seen)
    return rec


def doses_from_on(repo, on_dir):
    """D_p of a and b in V (strings, as schedule6 writes them) from the guard-on deck: predict6.doses_V on campaign
    5's P.table of P.load(on, on). Returns ({cell: (D1, D2)}, problems)."""
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


def _job(rid, kind, argv):
    return dict(id=rid, kind=kind, limit_s=limit_s(kind), expected_s=float(EXPECTED_S[kind]), argv=argv)


def wave1(repo, runs, ngspice, pdk, seeds):
    py, me = sys.executable, str(Path(__file__).resolve())
    return [_job(f"{s}-cal-{g}-unary", f"cal-{g}", [py, "-B", me, "cal", str(repo), str(Path(runs) / f"{s}-cal-{g}-unary"), str(s), g, str(ngspice), str(pdk)])
            for s in seeds for g in ("on", "off")]


def wave2(repo, runs, ngspice, pdk, doses):
    """doses: {seed: {cell: (D1_V, D2_V)}}."""
    py, me = sys.executable, str(Path(__file__).resolve())
    out = []
    for s, D in doses.items():
        for cell in CELLS_UNARY:
            for p in (1, 2):
                rid = f"{s}-unary-scan-{cell}{p}"
                out.append(_job(rid, "unary-scan", [py, "-B", me, "scan", str(repo), str(Path(runs) / rid), str(s), cell, str(p), *D[cell], str(ngspice), str(pdk)]))
            rid = f"{s}-preset-{cell}"
            out.append(_job(rid, "preset", [py, "-B", me, "preset", str(repo), str(Path(runs) / rid), str(s), cell, *D[cell], str(ngspice), str(pdk)]))
    return out


def worker(repo, runs, ngspice, pdk, seeds):
    """W1 for the given instances, then W2 for each whose two decks completed and give the doses. Each wave once."""
    assert __debug__, "refused: not with python -O, the guards are asserts"
    seeds = [guard_seed(str(s)) for s in seeds]
    assert seeds and len(set(seeds)) == len(seeds), "refused: an empty or repeated list of instances"
    paths(repo)
    import batch2x
    import dosedev2
    runs = Path(runs)
    dosedev2.outside(repo, runs)
    assert not runs.exists(), f"refused: {runs} exists; a worker runs once"
    runs.mkdir(parents=True)
    (runs / "INSTANCES.json").write_text(json.dumps(seeds) + "\n")
    s1 = batch2x.run_wave(runs, "W1", wave1(repo, runs, ngspice, pdk, seeds))
    doses, not_started = {}, []
    for s in seeds:
        why = None
        if s1.get(f"{s}-cal-on-unary") == "complete" and s1.get(f"{s}-cal-off-unary") == "complete":
            D, bad = doses_from_on(repo, runs / f"{s}-cal-on-unary")
            if D is None:
                why = "the guard-on deck's doses are not usable: " + "; ".join(bad[:3])
            else:
                doses[s] = D
        else:
            why = "a calibration deck did not complete"
        if why:
            not_started += [dict(id=f"{s}-unary-scan-{c}{p}", why=why) for c in CELLS_UNARY for p in (1, 2)]
            not_started += [dict(id=f"{s}-preset-{c}", why=why) for c in CELLS_UNARY]
    (runs / "DOSES.json").write_text(json.dumps({str(s): D for s, D in doses.items()}, indent=1) + "\n")
    (runs / "NOT_STARTED_W2.json").write_text(json.dumps(not_started, indent=1) + "\n")
    s2 = batch2x.run_wave(runs, "W2", wave2(repo, runs, ngspice, pdk, doses))
    out = dict(instances=seeds, W1=s1, W2=s2, not_started=len(not_started))
    (runs / "WORKER.json").write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps(out))
    return out


def dup(repo, runs, ngspice, pdk, seed):
    """The duplicate guard-on deck of `seed` (MACHINE_PLAN.md 2), in RUNS/<seed>-cal-on-unary-dup."""
    assert __debug__, "refused: not with python -O, the guards are asserts"
    seed = guard_seed(str(seed))
    paths(repo)
    import batch2x
    import dosedev2
    runs = Path(runs)
    dosedev2.outside(repo, runs)
    assert not runs.exists(), f"refused: {runs} exists"
    runs.mkdir(parents=True)
    py, me = sys.executable, str(Path(__file__).resolve())
    rid = f"{seed}-cal-on-unary-dup"
    job = _job(rid, "cal-on", [py, "-B", me, "cal", str(repo), str(runs / rid), str(seed), "on", str(ngspice), str(pdk)])
    return batch2x.run_wave(runs, "DUP", [job])


# Keys of a calibration record that depend on the machine or the clock, not on the simulation.
VOLATILE = {"wall_s", "peak_rss_MB"}
VOLATILE_HEADER = {"interpreter"}
VOLATILE_RESULT = {"wall_s"}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def comparable(run_dir):
    """What must be byte-identical between two machines' runs of one deck: the deck's text, the waveform, and the
    record and result with their clock and machine fields removed (MACHINE_PLAN.md 2)."""
    d = Path(run_dir)
    rec = json.loads((d / "record.json").read_text())
    rec = {k: v for k, v in rec.items() if k not in VOLATILE and k not in ("id", "files")}
    rec["batch"] = {k: v for k, v in rec["batch"].items() if k not in VOLATILE_HEADER}
    res = json.loads((d / "evidence" / "result.json").read_text())
    res = {k: v for k, v in res.items() if k not in VOLATILE_RESULT}
    return dict(input_spice=sha(d / "evidence" / "input.spice"), trace_raw=sha(d / "evidence" / "trace.raw"),
                record=hashlib.sha256(json.dumps(rec, sort_keys=True).encode()).hexdigest(),
                result=hashlib.sha256(json.dumps(res, sort_keys=True).encode()).hexdigest(),
                noise_sha256=(d / "noise.sha256").read_text().strip())


def compare(d1, d2):
    a, b = comparable(d1), comparable(d2)
    out = dict(first=str(d1), second=str(d2), fields={k: dict(first=a[k], second=b[k], equal=a[k] == b[k]) for k in a})
    out["identical"] = all(v["equal"] for v in out["fields"].values())
    return out


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "cal":
        cal(a[1], a[2], a[3], a[4], a[5], a[6])
    elif a and a[0] == "scan":
        scan_kind(a[1], a[2], a[3], a[4], f"line{int(a[5])}", [SCAN_DELTA, a[6], a[7]], a[8], a[9])
    elif a and a[0] == "preset":
        scan_kind(a[1], a[2], a[3], a[4], "onesided", ["0", "0", a[5], a[6]], a[7], a[8])
    elif a and a[0] == "plan":
        paths(a[1])
        seeds = [guard_seed(x) for x in a[5:]]
        w1 = wave1(a[1], a[2], a[3], a[4], seeds)
        w2 = wave2(a[1], a[2], a[3], a[4], {s: {c: ("<D1>", "<D2>") for c in CELLS_UNARY} for s in seeds})
        for n, w in (("W1", w1), ("W2", w2)):
            for j in w:
                print(n, j["id"], f"expected {j['expected_s']:.0f} s", f"limit {j['limit_s']} s")
        allj = w1 + w2
        print(json.dumps(dict(instances=seeds, runs=len(allj), sum_expected_s=round(sum(j["expected_s"] for j in allj)))))
    elif a and a[0] == "worker":
        worker(a[1], a[2], a[3], a[4], a[5:])
    elif a and a[0] == "dup":
        print(json.dumps(dup(a[1], a[2], a[3], a[4], a[5])))
    elif a and a[0] == "compare":
        print(json.dumps(compare(a[1], a[2]), indent=1))
    else:
        raise SystemExit(__doc__)
