"""campaign_run11.py with envcheck_layered4's checks: envcheck_layered3's, and Python 3.13.18 (relayed 2026-11-25).
Development only. campaign_run11.py and the earlier drivers are kept as they are.

launch and run refuse unless every envcheck_layered4 check holds. ENV.json is written as in campaign_run11
(envcheck_layered3.env, format layered-env/3).

  campaign_run12.py launch | run | wait | status ...     as campaign_run11.py
"""
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run9 as C9  # noqa: E402
import campaign_run10 as C10  # noqa: E402
import campaign_run11 as C11  # noqa: E402
import envcheck_layered4 as E4  # noqa: E402


def refuse_unless_env():
    bad = [k for k, v in E4.checks().items() if not v["ok"]]
    if bad:
        raise SystemExit("refused: envcheck_layered4 fails: " + ", ".join(bad))


def set_env(plan, root):
    refuse_unless_env()
    return C11.set_env(plan, root)


def cmd_run(plan_path, root, *rest):
    saved = C9.set_env
    C9.set_env = set_env
    try:
        return C10.cmd_run(plan_path, root, *rest)
    finally:
        C9.set_env = saved


def cmd_launch(plan_path, root, *rest):
    refuse_unless_env()
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
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run12.py"), "run", str(Path(plan_path).resolve()),
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
