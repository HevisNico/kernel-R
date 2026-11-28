"""envcheck_layered3.py with Python's version pinned (the audit, relayed 2026-11-25). Development only.
envcheck_layered3.py and the earlier versions are kept as they are.

envcheck_layered3 recorded Python (static.python: version, executable_sha256) but did not refuse any version.
Here the checks also require Python 3.13.18, the version of every yield-lot machine (their ENV.json:
3.13.18, executable sha256 3fff8e682225671f…). Any other version is REFUSED. The executable's sha256 is recorded, as
before, and not pinned. ENV.json is envcheck_layered3's (format layered-env/3; this check changes no recorded field).

  envcheck_layered4.py [--json OUT]               the checks: envcheck_layered3's, and python == 3.13.18
  envcheck_layered4.py env OUTROOT [PLAN.json]    writes OUTROOT/ENV.json (as envcheck_layered3)
"""
import json
from pathlib import Path
import platform
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import envcheck_layered3 as E3  # noqa: E402

PYTHON_VERSION = "3.13.18"
E = E3.E
env = E3.env


def checks():
    out = E3.checks()
    got = platform.python_version()
    out["python"] = dict(ok=got == PYTHON_VERSION, want=PYTHON_VERSION, got=got, executable=str(Path(sys.executable).resolve()))
    return out


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "env":
        root = Path(a[1])
        plan = json.loads(Path(a[2]).read_text()) if len(a) > 2 else None
        root.mkdir(parents=True, exist_ok=True)
        (root / "ENV.json").write_bytes(E.canon(env(plan)))
        print((root / "ENV.json").read_text())
    else:
        r = checks()
        ok = all(v["ok"] for v in r.values())
        text = json.dumps(dict(ok=ok, checks=r), indent=1, sort_keys=True)
        if "--json" in a:
            Path(a[a.index("--json") + 1]).write_text(text + "\n")
        print(text)
        if not ok:
            print("REFUSED: " + ", ".join(k for k, v in r.items() if not v["ok"]), file=sys.stderr)
        sys.exit(0 if ok else 1)
