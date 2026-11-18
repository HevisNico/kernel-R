"""Campaign 6's development batch: the runs of one machine, four at a time, each limited (BATCH_SPEC.md section 1).
New code. Started detached (`setsid nohup ... &`) by the machine's session, which stays active until it ends.

  schedule6.py batch MACHINE BATCH_DIR DELTA NGSPICE PDK      the machine's five instances (7701-7705 on a, 7706-7710 on b),
                                                              refused unless the pushed marker names this very code
  schedule6.py merge BATCH_DIR                                 BATCH_DIR/RUNS.json from a/RUNS.json and b/RUNS.json
  schedule6.py smoke OUT RC_CAL_ON RC_CAL_OFF NGSPICE PDK       the declared nominal smokes (section 1), before the marker:
                                                              the whole nominal instance at 1/4, and its a pair and c
                                                              line 1 at 1/2

Per instance, three waves, each run started as soon as its inputs exist:
1. the two calibration decks (batch6.py cal);
2. the four crossing scans (scan6.py) and c's both-lines FIRE check at s = 0 (scan6.py bothfire), with D_p from the
   guard-on deck;
3. the two one-sided sets (scan6.py onesided), each at W_x + h_x (MAPPING_U.md 2), so each waits for both pair scans of
   its instance and is "not started" if either has no consistent bracket.
A run whose inputs failed is not started ("not started: <why>"). A run at its limit is killed and recorded "missing
(limit)"; a run that fails is "failed"; neither is ever repeated. Every run's state, outer wall time and status go to
DIR/STATE.json as they change, and to DIR/RUNS.json at the end.
"""
from fractions import Fraction as F
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
import batch6                                           # noqa: E402
import predict6                                         # noqa: E402

PY = sys.executable
JOBS = 4


def cost_kind(kind):
    return dict(pair="pair", line1="line", line2="line", both="both").get(kind, kind)


def instance_jobs(seed, delta):
    """The nine runs of one instance: id, kind (for the limit), cost kind (for E), and how to build its command."""
    s = "none" if seed is None else str(seed)
    jobs = [dict(id=f"{s}-cal-{g}", limit="cal", cost_kind=f"cal-{g}", wave=1, guard=g, seed=seed) for g in ("on", "off")]
    for c, kind in predict6.CROSSINGS:
        jobs.append(dict(id=f"{s}-scan-{c}-{kind}", limit="scan", cost_kind=cost_kind(kind), wave=2, cell=c, kind=kind, seed=seed, delta=str(delta)))
    jobs.append(dict(id=f"{s}-bothfire-c", limit="onesided", cost_kind="bothfire", wave=2, cell="c", kind="bothfire", seed=seed))
    for c in ("a", "b"):
        jobs.append(dict(id=f"{s}-onesided-{c}", limit="onesided", cost_kind="onesided", wave=3, cell=c, kind="onesided", seed=seed))
    return jobs


def command(job, folder, cal_dirs, ngspice, pdk):
    """The command of a job, or (None, why) if its inputs failed. cal_dirs: (on, off) of the job's instance."""
    s = "none" if job["seed"] is None else str(job["seed"])
    out = str(folder / job["id"])
    if job["wave"] == 1:
        return [PY, "-B", str(HERE / "batch6.py"), "cal", out, s, job["guard"], str(ngspice), str(pdk)], None
    t, dose, bad = predict6.table(*cal_dirs)
    if bad:
        return None, "the calibration decks are not usable: " + "; ".join(bad[:3])
    D = predict6.doses_V(dose)
    c = job["cell"]
    dv = [repr(float(D[(c, p)]) / 1000) for p in (1, 2)]
    if job["kind"] == "bothfire":
        return [PY, "-B", str(HERE / "scan6.py"), out, s, "c", "bothfire", *dv, str(ngspice), str(pdk)], None
    if job["wave"] == 2:
        return [PY, "-B", str(HERE / "scan6.py"), out, s, c, job["kind"], job["delta"], *dv, str(ngspice), str(pdk)], None
    S, h = {}, {}
    for x in ("a", "b"):                                    # the bound needs both pair scans, through K (MAPPING_U.md 2)
        pair = folder / f"{s}-scan-{x}-pair" / "record.json"
        if not pair.exists():
            return None, f"the pair scan of {x} did not complete"
        r = json.loads(pair.read_text())["result"]
        if not r.get("consistent"):
            return None, f"the pair scan of {x} has no consistent bracket"
        S[x], h[x] = F(r["s_star"]), F(r["half_bracket"])
    b = predict6.layer1_bounds(S, h)[c]
    return [PY, "-B", str(HERE / "scan6.py"), out, s, c, "onesided", str(b), str(b), *dv, str(ngspice), str(pdk)], None


REPO = HERE.parent.parent.parent
BRANCH = "research/learned-dnf-circuit-campaign-6-wip"
MARKER = "research/learned-dnf-circuit-campaign-6/BATCH_MARKER.json"
CHECK_BRANCH = "evidence/learned-dnf-circuit-campaign-6-check7692"
CHECK_FILE = "research/learned-dnf-circuit-campaign-6/evidence/check7692/CHECK_7692.json"


def git(*args):
    return subprocess.run(["git", "-C", str(REPO), *args], check=True, capture_output=True).stdout


def marker_check():
    """No seed of 7701 to 7710 runs before the marker: the marker, pushed on the -wip branch (fetched by name), names
    the code's commit and each file's SHA-256, and every one of those files, here and at that commit, has that hash;
    it names every file the batch imports (campaign 5's whole frozen list but its workflow); and it records the 7692 check's CHECK_7692.json (its SHA-256, on its
    evidence branch) with all_within true, so that the check's STOP is enforced here."""
    import hashlib
    git("fetch", "-q", "origin", BRANCH)
    m = json.loads(git("show", f"FETCH_HEAD:{MARKER}"))
    git("merge-base", "--is-ancestor", m["code_commit"], "FETCH_HEAD")
    for path, h in m["files"].items():
        assert hashlib.sha256((REPO / path).read_bytes()).hexdigest() == h, f"refused: {path} differs from the marker"
        assert hashlib.sha256(git("show", f"{m['code_commit']}:{path}")).hexdigest() == h, f"refused: {path} at the marker's commit differs"
    missing = [f for f in imported_files() if f not in m["files"]]
    assert not missing, f"refused: the marker does not name every file the batch imports: {missing[:5]}"
    c = m.get("check7692", {})
    assert c.get("all_within") is True, "refused: the declared 7692 check is not recorded as within its tolerances"
    git("fetch", "-q", "origin", CHECK_BRANCH)
    got = hashlib.sha256(git("show", f"FETCH_HEAD:{CHECK_FILE}")).hexdigest()
    assert got == c.get("sha256"), "refused: CHECK_7692.json on its evidence branch is not the one the marker records"
    assert json.loads(git("show", f"FETCH_HEAD:{CHECK_FILE}"))["all_within"] is True, "refused: CHECK_7692.json says not within"
    return m


def imported_files():
    """Every file the batch runs: its own (batch/*.py but the tests) and every file of campaign 5's plan.FROZEN but its
    CI workflow (66): campaign 5's own 38, and the 28 outside its folder that define the deck's physics and the gate
    (research/learned-dnf-circuit, network-circuit, circuit, sky130-supervisor-closure, learned-coincidence)."""
    own = sorted(str(p.relative_to(REPO)) for p in HERE.glob("*.py") if p.name != "test_batch.py")
    import plan
    c5 = [f for f in plan.FROZEN if not f.startswith(".github/")]
    return own + c5


def wave_deps(j, jobs):
    """The runs a run waits for: the instance's two decks (waves 2 and 3), and, for a one-sided set (wave 3), both pair
    scans of its instance (a and b), since its bound needs K over both (MAPPING_U.md 2)."""
    return [x for x in jobs if x["seed"] == j["seed"] and (x["wave"] == 1 and j["wave"] > 1
                                                         or j["wave"] == 3 and x["id"].endswith(("-scan-a-pair", "-scan-b-pair")))]


def write_state(folder, jobs, status="running"):
    tmp = folder / "STATE.json.tmp"
    tmp.write_text(json.dumps(dict(status=status, jobs=jobs), indent=1, default=str) + "\n")
    os.replace(tmp, folder / "STATE.json")


def schedule(folder, jobs, cal_of, ngspice, pdk):
    folder.mkdir(parents=True, exist_ok=True)
    for j in jobs:
        j.update(status="waiting", limit_s=batch6.limit_s(j["limit"]))
    running = {}
    write_state(folder, jobs)
    while True:
        for j in jobs:
            if j["status"] != "waiting" or len(running) >= JOBS:
                continue
            deps = wave_deps(j, jobs)
            if any(x["status"] in ("waiting", "running") for x in deps):
                continue
            if any(x["status"] != "complete" for x in deps if x["wave"] == 1):
                j.update(status="not started: a calibration deck did not complete")
                continue
            cmd, why = command(j, folder, cal_of(j["seed"]), ngspice, pdk)
            if cmd is None:
                j.update(status=f"not started: {why}")
                continue
            log = open(folder / f"{j['id']}.log", "w")
            p = subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, start_new_session=True, cwd=str(HERE))
            running[j["id"]] = (p, time.time(), log)
            j.update(status="running", started_unix=time.time(), argv=cmd)
            write_state(folder, jobs)
        for i, (p, t0, log) in list(running.items()):
            j = next(x for x in jobs if x["id"] == i)
            code = p.poll()
            if code is None and time.time() - t0 > j["limit_s"]:
                os.killpg(p.pid, signal.SIGKILL)
                p.wait()
                code = "limit"
            if code is None:
                continue
            log.close()
            del running[i]
            wall = time.time() - t0
            rec = folder / i / "record.json"
            if code == 0 and rec.exists():
                j.update(status="complete", wall_s=json.loads(rec.read_text())["wall_s"], outer_wall_s=wall)
            else:
                j.update(status="missing (limit)" if code == "limit" else f"failed (exit {code})", outer_wall_s=wall)
            write_state(folder, jobs)
        if not running and not any(j["status"] == "waiting" for j in jobs):
            break
        time.sleep(5)
    write_state(folder, jobs, "ended")
    (folder / "RUNS.json").write_text(json.dumps([dict(id=j["id"], machine=j.get("machine"), cost_kind=j["cost_kind"], status=j["status"],
                                                       wall_s=j.get("wall_s")) for j in jobs], indent=1) + "\n")
    return jobs


def expected_ids():
    return {j["id"] for s in batch6.SEEDS for j in instance_jobs(s, F(1, 4))}


def merge(batch_dir):
    """BATCH_DIR/RUNS.json from BATCH_DIR/a/RUNS.json and BATCH_DIR/b/RUNS.json: every run of both machines, each
    status kept as it is; no id twice, and exactly the batch's 90 runs (10 instances x 9)."""
    runs = []
    for m in ("a", "b"):
        part = json.loads((batch_dir / m / "RUNS.json").read_text())
        assert all(r["machine"] == m for r in part), f"a run of {m}/RUNS.json is not of machine {m}"
        runs += part
    ids = [r["id"] for r in runs]
    assert len(ids) == len(set(ids)), "an id appears twice"
    assert set(ids) == expected_ids() and len(ids) == 90, "not the batch's 90 runs"
    (batch_dir / "RUNS.json").write_text(json.dumps(runs, indent=1) + "\n")
    return runs


def main(argv=None):
    a = sys.argv[1:] if argv is None else argv
    batch6.require_debug()
    if a[0] == "batch":
        machine, folder, delta, ngspice, pdk = a[1], Path(a[2]), F(a[3]), Path(a[4]), Path(a[5])
        assert machine in ("a", "b") and delta in batch6.DELTAS
        m = marker_check()
        assert F(m["delta"]) == delta, f"refused: the marker's ascent step is {m['delta']}, not {delta}"
        seeds = [s for s in batch6.SEEDS if batch6.MACHINE_OF[s] == machine]
        jobs = [dict(j, machine=machine) for s in seeds for j in instance_jobs(s, delta)]
        jobs.sort(key=lambda j: (j["wave"], j["seed"]))
        schedule(folder / machine, jobs, lambda s: (folder / machine / f"{s}-cal-on", folder / machine / f"{s}-cal-off"), ngspice, pdk)
    elif a[0] == "merge":
        print(json.dumps(dict(runs=len(merge(Path(a[1]))))))
    elif a[0] == "smoke":
        folder, on, off, ngspice, pdk = Path(a[1]), Path(a[2]), Path(a[3]), Path(a[4]), Path(a[5])
        jobs = []
        for delta in batch6.DELTAS:
            tag = "q" if delta == F(1, 4) else "h"
            kinds = predict6.CROSSINGS if delta == F(1, 4) else (("a", "pair"), ("c", "line1"))
            for c, kind in kinds:
                jobs.append(dict(id=f"none-{tag}-scan-{c}-{kind}", limit="scan", cost_kind=f"{cost_kind(kind)}@{delta}", wave=2, cell=c, kind=kind,
                                 seed=None, delta=str(delta), machine="a"))
        jobs.append(dict(id="none-bothfire-c", limit="onesided", cost_kind="bothfire", wave=2, cell="c", kind="bothfire", seed=None, machine="a"))
        for c in ("a", "b"):
            jobs.append(dict(id=f"none-onesided-{c}", limit="onesided", cost_kind="onesided", wave=3, cell=c, kind="onesided", seed=None, machine="a"))
        folder.mkdir(parents=True, exist_ok=True)
        for c, kind in predict6.CROSSINGS:          # the whole chain reads the 1/4 instance under the batch's names
            link = folder / f"none-scan-{c}-{kind}"
            if not link.exists():
                link.symlink_to(f"none-q-scan-{c}-{kind}")
        schedule(folder, jobs, lambda s: (on, off), ngspice, pdk)
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
