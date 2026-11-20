"""Development only: a batch of measures on mismatched cells at twice the dose, with the solver's relative tolerance at
1e-5. Measures only, no network run. Not campaign code, not preregistered, and it counts nothing.

It edits no file of the repository and writes nothing inside it. The frozen functions of campaign 6's batch are called
unchanged (batch6.cal for the two calibration decks, scan6.main for the scans, the both-lines check and the one-sided
sets). For the time of each call, three things are wrapped, and nothing else:
  - net.deck, so that the deck's text has `vhi=0.7` and `reltol=1e-5` (dosedev2.window, dosedev_tol.rewrite);
  - dosedev.rewrite, replaced by dosedev_tol.rewrite (dosedev_tol.tolerance), which knows `reltol`;
  - batch6.guard_seed, the frozen seed guard that scan6.main calls, replaced by this file's `guard_seed`: it accepts
    this batch's seeds (SEEDS below) and nothing else. The frozen guard accepts 7701 to 7710, campaign 6's own batch.

  batch2x.py cal   REPO OUT SEED on|off NGSPICE PDK
  batch2x.py scan  REPO OUT SEED CELL KIND ARGS... NGSPICE PDK
        KIND pair | line1 | line2: ARGS = 1/2 D1_V D2_V;  bothfire: D1_V D2_V;  onesided: S1 S2 D1_V D2_V
  batch2x.py plan  REPO RUNS_DIR NGSPICE PDK          prints the list of the batch's runs and their limits; runs nothing
  batch2x.py w1 | w2 | w3  REPO RUNS_DIR NGSPICE PDK  one wave of the batch (dosedev2.many, four at a time), once each, in order
  batch2x.py smoke REPO OUT_DIR NGSPICE PDK           the nominal cell, before the batch: its two decks, then its both-lines
                                                      check and one one-sided set of a at the frozen bound for a = b = 857/512

The smoke is not an instance of the batch: seed `none`, section `tt`, through the same frozen functions and the same
rewrite, to see that a deck and a one-sided set run at 1e-5 and what they cost.

The three waves, as campaign 6's batch scheduler orders them (schedule6.command): (1) the two decks of every
instance; (2) for each instance whose two decks completed and are usable (predict6.table), its four scans and its
both-lines check, with the doses of its own decks (`doses_of`: predict6.doses_V, written as schedule6 writes them);
(3) for each instance whose two pair scans are consistent, its two one-sided sets at the frozen bound (dosedev2.bound
with 8, which is predict6.layer1_bounds). A run that fails or is cut at its limit stops nothing else; the runs that need it are not
started, and are listed in RUNS_DIR/NOT_STARTED_W2.json and NOT_STARTED_W3.json. No run is ever started twice.
"""
import contextlib
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import dosedev2                                            # noqa: E402
import dosedev_tol                                         # noqa: E402

SEEDS = tuple(range(8301, 8311))                           # this batch's ten development instances, never extended
PARAMS = dict(vhi="0.7", reltol="1e-5")                    # twice the dose; the tolerance of DOSE_ADDENDUM.md section 3
# Expected wall times, in seconds: the means of campaign 6's batch (its report) times a slow-down per kind of run. For
# pair and line scans, 1.4, seen on three pair scans at 1e-5. For the others, the smoke of step 0 against the same
# nominal run at 1e-4 and the unchanged dose: 1 130 / 540, 716 / 404, 52 / 32 and 324 / 162 s, rounded to one decimal.
# Set after the smoke and before any run of the batch. The limit of a run is twice its expected time, rounded up to 10 s.
BATCH6_MEAN_S = {"cal-on": F("804.31"), "cal-off": F("645.14"), "pair": F("494.76"), "line": F("465.40"), "bothfire": F("37.11"), "onesided": F("219.42")}
SLOW_DOWN = {"cal-on": F(21, 10), "cal-off": F(18, 10), "pair": F(14, 10), "line": F(14, 10), "bothfire": F(16, 10), "onesided": F(2)}
SCANS = (("a", "pair"), ("b", "pair"), ("c", "line1"), ("c", "line2"))


def expected_s(kind):
    return BATCH6_MEAN_S[kind] * SLOW_DOWN[kind]


def limit_s(kind):
    return 10 * math.ceil(2 * expected_s(kind) / 10)


def guard_seed(text):
    """This batch's seeds only. `none` (the nominal cell) and every other seed are refused."""
    assert text != "none", "refused: the nominal cell is not an instance of this batch"
    seed = int(text)
    assert seed in SEEDS, f"refused: seed {seed} is not one of this batch's {SEEDS[0]} to {SEEDS[-1]}"
    return seed


@contextlib.contextmanager
def seeds():
    """For the time of the block, batch6.guard_seed is this file's guard."""
    import batch6
    frozen = batch6.guard_seed
    batch6.guard_seed = guard_seed
    try:
        yield
    finally:
        batch6.guard_seed = frozen


def doses_of(repo, on_dir, off_dir):
    """The doses a scan is started with, from an instance's two decks, as schedule6.command computes them:
    predict6.table, then predict6.doses_V, each written `repr(float(mV) / 1000)`. Returns ({cell: (D1_V, D2_V)}, None),
    or (None, why) when the decks are not usable."""
    dosedev2.repo_paths(repo)
    import predict6
    t, dose, bad = predict6.table(on_dir, off_dir)
    if bad:
        return None, "the calibration decks are not usable: " + "; ".join(bad[:3])
    D = predict6.doses_V(dose)
    return {c: tuple(repr(float(D[(c, p)]) / 1000) for p in (1, 2)) for c in ("a", "b", "c")}, None


def cal(repo, out, seed, guard, ngspice, pdk):
    assert __debug__, "refused: not with python -O, the guards are asserts"
    dosedev2.repo_paths(repo)
    dosedev2.outside(repo, out)
    seed = guard_seed(str(seed))
    assert guard in ("on", "off"), guard
    import batch6
    import c4
    print(c4.require_pinned())
    seen = []
    with dosedev_tol.tolerance(), dosedev2.window(PARAMS, seen):
        rec = batch6.cal(Path(out), seed, guard, Path(ngspice), Path(pdk))
    dosedev2.sidecar(out, f"guard-{guard} calibration deck of seed {seed} (batch6.cal, frozen)", seen)
    return rec


def scan(repo, out, seed, argv):
    """argv: CELL KIND ARGS... NGSPICE PDK, as scan6.main takes them after OUT and the seed."""
    assert __debug__, "refused: not with python -O, the guards are asserts"
    dosedev2.repo_paths(repo)
    dosedev2.outside(repo, out)
    seed = guard_seed(str(seed))
    assert argv[1] in ("pair", "line1", "line2", "bothfire", "onesided"), f"refused: kind {argv[1]}"
    import scan6
    seen = []
    with seeds(), dosedev_tol.tolerance(), dosedev2.window(PARAMS, seen):
        rec = scan6.main([str(out), str(seed), *argv])
    dosedev2.sidecar(out, f"{argv[1]} of {argv[0]}, seed {seed} (scan6.main, frozen)", seen)
    return rec


# ---------------------------------------------------------------------------------- the smoke, on the nominal cell

def smoke_cal(repo, out, guard, ngspice, pdk):
    """One deck of the nominal cell (seed None, section `tt`) with the batch's rewrite. The frozen guard is untouched."""
    assert __debug__, "refused: not with python -O, the guards are asserts"
    dosedev2.repo_paths(repo)
    dosedev2.outside(repo, out)
    assert guard in ("on", "off"), guard
    import batch6
    import c4
    print(c4.require_pinned())
    seen = []
    with dosedev_tol.tolerance(), dosedev2.window(PARAMS, seen):
        rec = batch6.cal(Path(out), None, guard, Path(ngspice), Path(pdk))
    dosedev2.sidecar(out, f"smoke: guard-{guard} calibration deck of the nominal cell (batch6.cal, frozen)", seen)
    return rec


def smoke_scan(repo, out, argv):
    """The both-lines check or a one-sided set of the nominal cell (seed `none`, which the frozen guard accepts)."""
    assert __debug__, "refused: not with python -O, the guards are asserts"
    dosedev2.repo_paths(repo)
    dosedev2.outside(repo, out)
    assert argv[1] in ("bothfire", "onesided"), f"refused: kind {argv[1]} (the smoke runs no scan)"
    import scan6
    seen = []
    with dosedev_tol.tolerance(), dosedev2.window(PARAMS, seen):
        rec = scan6.main([str(out), "none", *argv])
    dosedev2.sidecar(out, f"smoke: {argv[1]} of {argv[0]}, nominal cell (scan6.main, frozen)", seen)
    return rec


SMOKE_BOUND = "4097/512"                                   # the frozen bound for s*_a = s*_b = 857/512, half bracket 1/512
SMOKE_EXPECTED_S = {"cal-on": F(760), "cal-off": F(570), "bothfire": F(50), "onesided": F(230)}     # the nominal runs at 1e-4, times 1.4 (the estimate the smoke ran with)


def smoke_jobs(repo, out, ngspice, pdk, doses=None):
    here, py = str(Path(__file__).resolve()), sys.executable
    lim = lambda k: 10 * math.ceil(2 * SMOKE_EXPECTED_S[k] / 10)
    decks = [dict(id=f"none-smoke-cal-{g}", limit_s=lim(f"cal-{g}"), argv=[py, "-B", here, "smoke-cal", str(repo), str(Path(out) / f"none-smoke-cal-{g}"), g, str(ngspice), str(pdk)])
             for g in ("on", "off")]
    if doses is None:
        return decks
    rest = [dict(id="none-smoke-bothfire-c", limit_s=lim("bothfire"),
                 argv=[py, "-B", here, "smoke-scan", str(repo), str(Path(out) / "none-smoke-bothfire-c"), "c", "bothfire", *doses["c"], str(ngspice), str(pdk)]),
            dict(id="none-smoke-onesided-a", limit_s=lim("onesided"),
                 argv=[py, "-B", here, "smoke-scan", str(repo), str(Path(out) / "none-smoke-onesided-a"), "a", "onesided", SMOKE_BOUND, SMOKE_BOUND, *doses["a"], str(ngspice), str(pdk)])]
    return rest


def smoke(repo, out, ngspice, pdk):
    out = Path(out)
    dosedev2.outside(repo, out)
    assert not out.exists(), f"refused: {out} exists"
    out.mkdir(parents=True)
    s1 = run_wave(out, "S1", smoke_jobs(repo, out, ngspice, pdk))
    if all(v == "complete" for v in s1.values()):
        D, why = doses_of(repo, out / "none-smoke-cal-on", out / "none-smoke-cal-off")
        assert D is not None, why
        (out / "DOSES.json").write_text(json.dumps(D, indent=1) + "\n")
        s2 = run_wave(out, "S2", smoke_jobs(repo, out, ngspice, pdk, D))
    else:
        s2 = {}
    print(json.dumps(dict(S1=s1, S2=s2)))


# ------------------------------------------------------------------------------------------------- the list of runs

def job(repo, runs, rid, kind, tail, ngspice, pdk):
    """One run of the batch as dosedev2.many takes it. tail: the arguments after `batch2x.py <cal|scan> REPO OUT`."""
    here = Path(__file__).resolve()
    what = "cal" if kind in ("cal-on", "cal-off") else "scan"
    return dict(id=rid, kind=kind, limit_s=limit_s(kind), expected_s=float(expected_s(kind)),
                argv=[sys.executable, "-B", str(here), what, str(repo), str(Path(runs) / rid), *tail, str(ngspice), str(pdk)])


def wave1(repo, runs, ngspice, pdk):
    return [job(repo, runs, f"{s}-cal-{g}", f"cal-{g}", [str(s), g], ngspice, pdk) for s in SEEDS for g in ("on", "off")]


def wave2(repo, runs, ngspice, pdk, doses):
    """doses: {seed: {cell: (D1_V, D2_V)}} for the instances whose guard-on deck completed."""
    out = []
    for s in SEEDS:
        if s not in doses:
            continue
        for cell, kind in SCANS:
            out.append(job(repo, runs, f"{s}-scan-{cell}-{kind}", "pair" if kind == "pair" else "line", [str(s), cell, kind, "1/2", *doses[s][cell]], ngspice, pdk))
        out.append(job(repo, runs, f"{s}-bothfire-c", "bothfire", [str(s), "c", "bothfire", *doses[s]["c"]], ngspice, pdk))
    return out


def wave3(repo, runs, ngspice, pdk, doses, bounds):
    """bounds: {seed: {a: bound, b: bound}} (stages, as strings) for the instances whose two pair scans are consistent."""
    return [job(repo, runs, f"{s}-onesided-{x}", "onesided", [str(s), x, "onesided", bounds[s][x], bounds[s][x], *doses[s][x]], ngspice, pdk)
            for s in SEEDS if s in bounds for x in ("a", "b")]


def planned(repo, runs, ngspice, pdk):
    """The 90 runs of the batch if every run completes, with place-holders where a value comes from an earlier run."""
    d = {s: {c: ("<D1 of its decks>", "<D2 of its decks>") for c in "abc"} for s in SEEDS}
    b = {s: {x: "<bound from its pair scans>" for x in "ab"} for s in SEEDS}
    return [wave1(repo, runs, ngspice, pdk), wave2(repo, runs, ngspice, pdk, d), wave3(repo, runs, ngspice, pdk, d, b)]


def status_of(runs, sub):
    p = Path(runs) / sub / "STATE.json"
    return {k: v["status"] for k, v in json.loads(p.read_text())["runs"].items()} if p.exists() else {}


def run_wave(runs, name, jobs):
    """One wave through dosedev2.many: its JOBS file, its state under RUNS/<name>/, the runs' folders under RUNS/."""
    runs = Path(runs)
    spec = dict(folder=str(runs / name), waves=[[dict(id=j["id"], limit_s=j["limit_s"], argv=j["argv"]) for j in jobs]])
    (runs / f"JOBS_{name}.json").write_text(json.dumps(spec, indent=1) + "\n")
    if jobs:
        dosedev2.many(runs / f"JOBS_{name}.json")
    return status_of(runs, name)


def w1(repo, runs, ngspice, pdk):
    assert __debug__, "refused: not with python -O, the guards are asserts"
    runs = Path(runs)
    dosedev2.outside(repo, runs)
    assert not runs.exists(), f"refused: {runs} exists; each wave of the batch is run once"
    runs.mkdir(parents=True)
    return run_wave(runs, "W1", wave1(repo, runs, ngspice, pdk))


def w2(repo, runs, ngspice, pdk):
    assert __debug__, "refused: not with python -O, the guards are asserts"
    runs = Path(runs)
    s1 = status_of(runs, "W1")
    assert len(s1) == 2 * len(SEEDS) and "running" not in s1.values(), "refused: wave 1 has not ended"
    assert not (runs / "W2").exists() and not (runs / "JOBS_W2.json").exists(), "refused: wave 2 was already started"
    not_started = []
    doses = {}
    for s in SEEDS:
        why = None
        if s1.get(f"{s}-cal-on") == "complete" and s1.get(f"{s}-cal-off") == "complete":
            D, why = doses_of(repo, runs / f"{s}-cal-on", runs / f"{s}-cal-off")
            if D is not None:
                doses[s] = D
        else:
            why = "a calibration deck did not complete"
        if why is not None:
            not_started += [dict(id=i, why=why) for i in [f"{s}-scan-{c}-{k}" for c, k in SCANS] + [f"{s}-bothfire-c", f"{s}-onesided-a", f"{s}-onesided-b"]]
    (runs / "DOSES.json").write_text(json.dumps({str(s): v for s, v in doses.items()}, indent=1) + "\n")
    (runs / "NOT_STARTED_W2.json").write_text(json.dumps(not_started, indent=1) + "\n")
    return run_wave(runs, "W2", wave2(repo, runs, ngspice, pdk, doses))


def w3(repo, runs, ngspice, pdk):
    assert __debug__, "refused: not with python -O, the guards are asserts"
    runs = Path(runs)
    s2 = status_of(runs, "W2")
    assert (runs / "JOBS_W2.json").exists() and "running" not in s2.values(), "refused: wave 2 has not ended"
    assert not (runs / "W3").exists() and not (runs / "JOBS_W3.json").exists(), "refused: wave 3 was already started"
    doses = {int(s): {c: tuple(v) for c, v in d.items()} for s, d in json.loads((runs / "DOSES.json").read_text()).items()}
    not_started = []
    bounds = {}
    for s in doses:
        S, h = {}, {}
        for x in ("a", "b"):
            rid = f"{s}-scan-{x}-pair"
            res = json.loads((runs / rid / "record.json").read_text())["result"] if s2.get(rid) == "complete" else {}
            if res.get("consistent"):
                S[x], h[x] = F(res["s_star"]), F(res["half_bracket"])
        if len(S) == 2:
            bounds[s] = {x: str(v) for x, v in dosedev2.bound(F(8), S, h).items()}
        else:
            not_started += [dict(id=f"{s}-onesided-{x}", why="its two pair scans are not both complete and consistent") for x in "ab"]
    (runs / "BOUNDS.json").write_text(json.dumps({str(s): v for s, v in bounds.items()}, indent=1) + "\n")
    (runs / "NOT_STARTED_W3.json").write_text(json.dumps(not_started, indent=1) + "\n")
    return run_wave(runs, "W3", wave3(repo, runs, ngspice, pdk, doses, bounds))


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "cal":
        cal(a[1], a[2], a[3], a[4], a[5], a[6])
    elif a and a[0] == "scan":
        scan(a[1], a[2], a[3], a[4:])
    elif a and a[0] == "plan":
        waves = planned(a[1], a[2], a[3], a[4])
        for n, w in enumerate(waves, 1):
            for j in w:
                print(f"W{n}", j["id"], j["kind"], f"expected {j['expected_s']:.0f} s", f"limit {j['limit_s']} s", " ".join(j["argv"][3:4] + j["argv"][6:-2]))
        allj = [j for w in waves for j in w]
        print(json.dumps(dict(runs=len(allj), sum_expected_s=round(sum(j["expected_s"] for j in allj)), four_at_a_time_at_best_s=round(sum(j["expected_s"] for j in allj) / 4))))
    elif a and a[0] in ("w1", "w2", "w3"):
        print(json.dumps({"w1": w1, "w2": w2, "w3": w3}[a[0]](a[1], a[2], a[3], a[4])))
    elif a and a[0] == "smoke-cal":
        smoke_cal(a[1], a[2], a[3], a[4], a[5])
    elif a and a[0] == "smoke-scan":
        smoke_scan(a[1], a[2], a[3:])
    elif a and a[0] == "smoke":
        smoke(a[1], a[2], a[3], a[4])
    else:
        raise SystemExit(__doc__)
