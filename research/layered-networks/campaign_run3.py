"""campaign_run2.py with a core budget (the coordinator's point (a), 2026-11-24). Development only.

campaign_run2.py is pushed and kept as it is. The problem it had: the kit's in-deck gate (invinst.indeck) measures an
instance's inverters in parallel inside one job, so a front-end job used 2 cores (XOR3) while it held one of the
`jobs` slots.

The fix chosen: **a job counts as the cores it uses.** Every step runs under a core budget of `jobs` cores; the
`inverters` step takes as many cores as the instance has inverters (capped at `jobs`), every other step takes one. A
step waits until its cores are free. The jobs' threads are no longer the limit (the pool has room for every job); the
budget is. Running the inverters one at a time was the other option; it would make every front-end instance's chain
longer by about 6 minutes per extra inverter, and the kit's interface runs them together.

Also: PLAN `steps_until` (for example "D"): each instance's chain stops after that step (a stage-D-only run; no seal,
no stage N, no controls).

  campaign_run3.py launch | run | wait | status ...     as campaign_run2.py
"""
import concurrent.futures as cf
import json
from pathlib import Path
import sys
import threading
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402


class Budget:
    """At most `cores` cores in use; acquire(n) waits until n are free. Records the peak in use."""

    def __init__(self, cores):
        self.cores, self.used, self.peak = cores, 0, 0
        self.cv = threading.Condition()

    def acquire(self, n):
        n = min(n, self.cores)
        with self.cv:
            while self.used + n > self.cores:
                self.cv.wait()
            self.used += n
            self.peak = max(self.peak, self.used)
        return n

    def release(self, n):
        with self.cv:
            self.used -= n
            self.cv.notify_all()


BUDGET = Budget(4)


class Instance(C2.Instance):
    def step(self, name, argv, outputs, kind, cwd=HERE, env=None):
        if self.done(name):
            return True
        st = self.status["steps"].get(name)
        if st and st["status"] != "done":
            return False
        until = self.plan.get("steps_until")
        order = ["deck", "inverters", "D", "seal", "N0", "C0", "N1", "C1", "N2", "C2", "N3", "C3"]
        if until and name in order and order.index(name) > order.index(until):
            return False                                       # the plan stops the chain before this step
        n = len([f"n{j}" for j in range(self.s["m"])]) if name == "inverters" else 1
        got = BUDGET.acquire(n)
        try:
            ok = super().step(name, argv, outputs, kind, cwd, env)
        finally:
            BUDGET.release(got)
        self.status["steps"][name]["cores"] = got
        self.save()
        return ok


def cmd_run(plan_path, root, *rest):
    kw = dict(a.split("=", 1) for a in rest)
    BUDGET.cores = int(kw.get("jobs", 4))
    C2.Instance = Instance                     # campaign_run2.cmd_run builds its instances from this name
    orig = cf.ThreadPoolExecutor

    class Pool(orig):                          # room for every job: the core budget is the limit
        def __init__(self, max_workers=None, *a, **k):
            super().__init__(max_workers=64, *a, **k)
    cf.ThreadPoolExecutor = Pool
    plan = json.loads(Path(plan_path).read_text())
    saved = CR.untrained, CR.duplicate
    if plan.get("steps_until"):                # a partial chain: no controls
        CR.untrained = lambda root_, inst, plan_: dict(instance=inst.dir.name, ok=None, why="not run: steps_until")
        CR.duplicate = lambda root_, inst, plan_: dict(instance=inst.dir.name, ok=None, why="not run: steps_until")
    try:
        ok = C2.cmd_run(plan_path, root, *rest)
    finally:
        cf.ThreadPoolExecutor = orig
        CR.untrained, CR.duplicate = saved
    r = json.loads((Path(root) / "RESULT.json").read_text())
    r["core_budget"] = dict(cores=BUDGET.cores, peak_in_use=BUDGET.peak)
    (Path(root) / "RESULT.json").write_text(json.dumps(r, indent=1, sort_keys=True) + "\n")
    return ok


def cmd_launch(plan_path, root, *rest):
    import subprocess
    root = Path(root).resolve()
    n = subprocess.run(["pgrep", "-c", "ngspice"], capture_output=True, text=True).stdout.strip()
    if n not in ("", "0"):
        raise SystemExit(f"refused: {n} ngspice process(es) running")
    if root.exists() and any(root.iterdir()):
        raise SystemExit(f"refused: {root} exists and is not empty (no run folders before a launch)")
    plan = json.loads(Path(plan_path).read_text())
    root.mkdir(parents=True, exist_ok=True)
    (root / "INVENTORY_START").write_text(C2.inventory(plan))
    log = (root / "driver.log").open("w")
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run3.py"), "run", str(Path(plan_path).resolve()),
                          str(root), *rest], stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                         start_new_session=True, cwd=HERE)
    (root / "DRIVER_PID").write_text(f"{p.pid}\n")
    print(f"launched pid {p.pid}")
    return True


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c == "run":
        sys.exit(0 if cmd_run(*a) else 1)
    elif c == "launch":
        sys.exit(0 if cmd_launch(*a) else 1)
    elif c == "wait":
        sys.exit(0 if C2.cmd_wait(*a) else 3)
    elif c == "status":
        C2.cmd_status(*a)
    else:
        sys.exit(__doc__)
