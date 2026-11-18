"""Campaign 6's development batch: the runs of one machine, four at a time, each limited (BATCH_SPEC.md section 1).
New code. Started detached (`setsid nohup ... &`) by the machine's session, which stays active until it ends.

  schedule6.py batch MACHINE BATCH_DIR DELTA NGSPICE PDK      the machine's five instances (7701-7705 on a, 7706-7710 on b)
  schedule6.py smoke OUT RC_CAL_ON RC_CAL_OFF NGSPICE PDK       the declared nominal smokes (section 1), before the marker

Per instance, three waves, each run started as soon as its inputs exist:
1. the two calibration decks (batch6.py cal);
2. the five crossing scans (scan6.py), with D_p from the guard-on deck;
3. the two one-sided sets (scan6.py onesided), with their bounds from the rescaled deck, the pair scan's theta_x and
   H_x (predict6.one_sided_bounds).
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
    if job["wave"] == 2:
        return [PY, "-B", str(HERE / "scan6.py"), out, s, c, job["kind"], job["delta"], *dv, str(ngspice), str(pdk)], None
    pair = folder / f"{s}-scan-{c}-pair" / "record.json"
    if not pair.exists():
        return None, "its pair scan did not complete"
    r = json.loads(pair.read_text())["result"]
    if not r.get("consistent"):
        return None, "its pair scan has no consistent bracket"
    theta = int(r["L"])
    t2 = {key: dict(v, Z=predict6.scale(v["Z"], theta)) for key, v in t.items() if key[0] == c}
    H = math.ceil(F(r["half_bracket"]) * predict6.steps(t2, c)["both"])
    b = predict6.one_sided_bounds(t2, c, H)
    return [PY, "-B", str(HERE / "scan6.py"), out, s, c, "onesided", str(b[1]), str(b[2]), *dv, str(ngspice), str(pdk)], None


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
            deps = [x for x in jobs if x["seed"] == j["seed"] and (x["wave"] == 1 and j["wave"] > 1
                                                                 or j["wave"] == 3 and x["id"].endswith(f"-scan-{j['cell']}-pair"))]
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


def main(argv=None):
    a = sys.argv[1:] if argv is None else argv
    batch6.require_debug()
    if a[0] == "batch":
        machine, folder, delta, ngspice, pdk = a[1], Path(a[2]), F(a[3]), Path(a[4]), Path(a[5])
        assert machine in ("a", "b") and delta in batch6.DELTAS
        seeds = [s for s in batch6.SEEDS if batch6.MACHINE_OF[s] == machine]
        jobs = [dict(j, machine=machine) for s in seeds for j in instance_jobs(s, delta)]
        jobs.sort(key=lambda j: (j["wave"], j["seed"]))
        schedule(folder / machine, jobs, lambda s: (folder / machine / f"{s}-cal-on", folder / machine / f"{s}-cal-off"), ngspice, pdk)
    elif a[0] == "smoke":
        folder, on, off, ngspice, pdk = Path(a[1]), Path(a[2]), Path(a[3]), Path(a[4]), Path(a[5])
        jobs = []
        for delta in batch6.DELTAS:
            tag = "q" if delta == F(1, 4) else "h"
            for c, kind in (("a", "pair"), ("c", "line1"), ("c", "both")):
                jobs.append(dict(id=f"none-{tag}-scan-{c}-{kind}", limit="scan", cost_kind=f"{cost_kind(kind)}@{delta}", wave=2, cell=c, kind=kind,
                                 seed=None, delta=str(delta), machine="a"))
        jobs.append(dict(id="none-onesided-a", limit="onesided", cost_kind="onesided", wave=3, cell="a", kind="onesided", seed=None, machine="a"))
        folder.mkdir(parents=True, exist_ok=True)
        # the one-sided smoke's bounds come from the 1/4 pair scan
        link = folder / "none-scan-a-pair"
        if not link.exists():
            link.symlink_to("none-q-scan-a-pair")
        schedule(folder, jobs, lambda s: (on, off), ngspice, pdk)
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
