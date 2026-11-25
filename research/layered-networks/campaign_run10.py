"""campaign_run9.py with the sealed prediction folder carried by the seal log (the owner's decision, relayed
2026-11-25). Development only. campaign_run9.py and the earlier drivers are kept as they are.

- **Machine A (the sealpush step).** It runs sealpush2.py instead of sealpush.py. The SEALS.txt line and the whole
  seal folder (seals/<instance>/: the files its SHA256SUMS lists, and SHA256SUMS) go in one append-only commit on the
  machine's log branch evidence/combined-seals-K<nn>. Stage N still starts only after that push succeeds, which
  campaign_run5 checks as before; seal_push.json then also records the folder's size.
- **Machine B (the remote duplicate).** A PLAN `remote_duplicates[]` entry needs only `seal_log` = [commit, branch]
  (the original's). No `seal_dir` is needed. B fetches the branch by name from PLAN seal_push.remote and takes
  seals/<instance>/ at that commit (sealpush2.fetch, recorded in DUPX_<inst>/seal_fetch.json). Then campaign_run9's
  checks apply:
  - the commit is on the branch;
  - the SEALS.txt line equals the sha256 of the folder's SHA256SUMS;
  - seal.verify holds.
  B then writes its comparison. An entry that gives `seal_dir` is used as in campaign_run9.

  campaign_run10.py launch | run | wait | status ...     as campaign_run9.py
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run7 as C7  # noqa: E402
import campaign_run9 as C9  # noqa: E402
import sealpush2  # noqa: E402
import spec as specmod  # noqa: E402


class Instance(C7.Instance):
    def step(self, name, argv, outputs, kind, cwd=HERE, env=None):
        if name == "sealpush":
            argv = list(argv)
            argv[2] = HERE / "sealpush2.py"
        return super().step(name, argv, outputs, kind, cwd, env)


_c9_remote_duplicate = C9.remote_duplicate


def remote_duplicate(root, x, plan):
    if x.get("seal_dir") or not x.get("seal_log"):
        return _c9_remote_duplicate(root, x, plan)
    s = specmod.load(HERE / x["spec"])
    inst = f"{s['tag']}_{x['seed']}"
    d = Path(root) / f"DUPX_{inst}"
    d.mkdir(parents=True, exist_ok=True)
    commit, branch = x["seal_log"]
    with tempfile.TemporaryDirectory() as t:
        ok, why = sealpush2.fetch(plan["seal_push"]["remote"], branch, commit, inst, Path(t) / "seal")
        (d / "seal_fetch.json").write_text(json.dumps(dict(remote=str(plan["seal_push"]["remote"]), branch=branch,
                                                           commit=commit, path=f"{sealpush2.PREFIX}/{inst}", ok=ok,
                                                           why=why), indent=1, sort_keys=True) + "\n")
        return _c9_remote_duplicate(root, dict(x, seal_dir=str(Path(t) / "seal") if ok else None), plan)


def cmd_run(plan_path, root, *rest):
    saved = C7.Instance, C9.remote_duplicate
    C7.Instance, C9.remote_duplicate = Instance, remote_duplicate
    try:
        return C9.cmd_run(plan_path, root, *rest)
    finally:
        C7.Instance, C9.remote_duplicate = saved


def cmd_launch(plan_path, root, *rest):
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
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run10.py"), "run", str(Path(plan_path).resolve()),
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
