"""campaign_run4.py with the owner's additions B and C of 2026-11-24. Development only.

campaign_run4.py and the earlier drivers are kept as they are.

B. **Raw traces kept where they may be needed, and a disk guard.**
- A stage-N folder's trace.raw is deleted (once its digest exists) only when its comparison is `agrees`. It is kept
  when the comparison is anything else (refuted, observed only, run failed), or when the comparison is missing.
- Kept always:
  - the duplicates' raws (DUP_*, DUPX_*);
  - the raws of the instances named in PLAN `keep_raw`: the originals of the cross-machine duplicates, written by
    plan_split2.py.
- **Disk guard**: before any step starts, the OUTROOT's free disk must be at least PLAN `disk_guard_gb` (default 20 GB).
  - Below it, the step does not start and the driver stops launching steps; nothing is deleted to make room.
  - The step gets no status entry, so a `run` after space is freed starts it.
  - RESULT.json lists the steps held back, under `stopped_for_disk`.

C. **Stage N refuses to start without the seal-log commit.**
- Before N<n> starts, seal_push.json must say `pushed: true` and name the 40-hex commit that logged the seal.
  - `dry` counts only when PLAN `allow_dry_seal` is true; that is for development runs.
  - Otherwise N<n> is not started, and its status says why.
- The commit and branch are written to N<n>/SEAL_LOG.json before stage N starts, and listed in the instance's
  SHA256SUMS. analyze3 compares them with the seal log.
- Writing the commit inside the stage-N record itself needs the controls' stagen to accept it. That has been asked of
  their session and is not done here.
- The duplicates (identity reruns, not predicted runs) are exempt.

  campaign_run5.py launch | run | wait | status ...     as campaign_run4.py
"""
import json
import re
import shutil
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run3 as C3  # noqa: E402
import campaign_run4 as C4  # noqa: E402

STATE = dict(keep=set(), guard_gb=20.0, root=None, held=[])
_drop_raw = CR.drop_raw


def drop_raw(folder):
    folder = Path(folder)
    inst = folder.parent.name
    if inst.startswith(("DUP_", "DUPX_")) or inst in STATE["keep"]:
        return
    comp = folder / "comparison.json"
    if comp.exists() and json.loads(comp.read_text()).get("verdict") == "agrees":
        _drop_raw(folder)


def disk_ok():
    root = STATE["root"]
    free = shutil.disk_usage(root).free / 1e9 if root else float("inf")
    return free >= STATE["guard_gb"], round(free, 2)


class Instance(C4.Instance):
    def step(self, name, argv, outputs, kind, cwd=HERE, env=None):
        if self.done(name):
            return True
        ok, free = disk_ok()
        if not ok:
            STATE["held"].append(dict(instance=self.dir.name, step=name, free_gb=free))
            return False                                   # not started, no status entry: a later run starts it
        return super().step(name, argv, outputs, kind, cwd, env)

    def round(self, n):
        d, plan = self.dir, self.plan
        name = f"N{n}"
        if not self.done(name) and name not in self.status["steps"]:
            sp = d / "seal_push.json"
            r = json.loads(sp.read_text()) if sp.exists() else {}
            pushed = r.get("pushed") is True or (r.get("pushed") == "dry" and plan.get("allow_dry_seal"))
            commit = r.get("commit") or ""
            if not pushed or not re.fullmatch(r"[0-9a-f]{40}", commit):
                self.status["steps"][name] = dict(status="refused", why="no pushed seal-log commit (seal_push.json)",
                                                  ended=C2.now())
                self.save()
                return False
            (d / name).mkdir(parents=True, exist_ok=True)
            (d / name / "SEAL_LOG.json").write_text(json.dumps(dict(commit=commit, branch=r.get("branch"),
                                                                    seal_sha256=r.get("seal_sha256"), line=r.get("line"),
                                                                    pushed=r.get("pushed")), indent=1, sort_keys=True) + "\n")
        return super().round(n)


def cmd_run(plan_path, root, *rest):
    plan = json.loads(Path(plan_path).read_text())
    STATE.update(keep=set(plan.get("keep_raw", [])), guard_gb=float(plan.get("disk_guard_gb", 20)),
                 root=Path(root).resolve(), held=[])
    Path(root).mkdir(parents=True, exist_ok=True)
    CR.drop_raw = drop_raw
    C4.Instance = Instance
    saved_c4_instance = C3.Instance
    try:
        ok = C4.cmd_run(plan_path, root, *rest)
    finally:
        CR.drop_raw = _drop_raw
        C3.Instance = saved_c4_instance
    r = json.loads((Path(root) / "RESULT.json").read_text())
    r["stopped_for_disk"] = STATE["held"]
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
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run5.py"), "run", str(Path(plan_path).resolve()),
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
