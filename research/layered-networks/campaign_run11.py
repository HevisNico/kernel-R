"""campaign_run10.py with ENV.json written by envcheck_layered3 (Lean's real toolchain binary, pinned), relayed
2026-11-25. Development only. campaign_run10.py and the earlier drivers are kept as they are.

- **The check.** Before ENV.json is written, envcheck_layered3.checks() must hold: numpy, ngspice, the PDK, Lean 4.35.0,
  and the real lean binary's sha256 bf8d54e4…, not elan's proxy. Otherwise the run is refused (SystemExit) and no
  step runs.
- **ENV.json** is envcheck_layered3.env (format layered-env/3). A resumed root still refuses a changed static part, as
  before.

  campaign_run11.py launch | run | wait | status ...     as campaign_run10.py
"""
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run9 as C9  # noqa: E402
import campaign_run10 as C10  # noqa: E402
import envcheck_layered3 as E3  # noqa: E402


def set_env(plan, root):
    bad = [k for k, v in E3.checks().items() if not v["ok"]]
    if bad:
        raise SystemExit("refused: envcheck_layered3 fails: " + ", ".join(bad))
    root = Path(root)
    root.mkdir(parents=True, exist_ok=True)
    e = E3.env(plan)
    f = root / "ENV.json"
    if f.exists():
        old = json.loads(f.read_text())
        if old["static_sha256"] != e["static_sha256"]:
            raise SystemExit(f"refused: mixed environment in {root}: ENV.json static {old['static_sha256'][:12]}, "
                             f"this machine now {e['static_sha256'][:12]}")
        rs = root / "ENV_RESUMES.json"
        log = json.loads(rs.read_text()) if rs.exists() else []
        log.append(dict(uptime_s=e["uptime_s"], static_sha256=e["static_sha256"]))
        rs.write_text(json.dumps(log, indent=1) + "\n")
    else:
        f.write_bytes(E3.E.canon(e))
    os.environ["LAYERED_ENV_SHA256"] = CR.sha(f)
    return os.environ["LAYERED_ENV_SHA256"]


def cmd_run(plan_path, root, *rest):
    saved = C9.set_env
    C9.set_env = set_env
    try:
        return C10.cmd_run(plan_path, root, *rest)
    finally:
        C9.set_env = saved


def cmd_launch(plan_path, root, *rest):
    bad = [k for k, v in E3.checks().items() if not v["ok"]]
    if bad:
        raise SystemExit("refused: envcheck_layered3 fails: " + ", ".join(bad))
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
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run11.py"), "run", str(Path(plan_path).resolve()),
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
