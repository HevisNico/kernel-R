"""envcheck_layered2.py with Lean's real toolchain binary hashed and pinned (the audit of the yield lot's ENV.json,
relayed 2026-11-25). Development only. envcheck_layered.py and envcheck_layered2.py are kept as they are.

The defect: envcheck_layered hashed `shutil.which("lean")`, resolved. Under elan that is elan's proxy (~/.elan/bin/lean,
sha256 54238e7f…), not the toolchain's binary. So 11 of the 12 yield-lot machines recorded the proxy. K02, installed
from the tarball, recorded the real binary (bf8d54e4…).

Here:
- **The real binary.** It is found in this order: `elan which lean`; else `lean --print-prefix`/bin/lean; else
  `which lean`. Each is resolved with readlink -f (Path.resolve).
- **The pin.** That binary's sha256 must be `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`, the
  bin/lean that campaign (a) pinned (research/function-family-campaign/AMENDMENT_2c.md on main: lean-4.35.0-linux.tar.zst
  sha256 7289597a…, its bin/lean bf8d54e4…). Anything else is REFUSED, and so is a version other than 4.35.0.
- **ENV.json** (format layered-env/3).
  - `static.lean` = {version, executable_sha256 (the real binary)}. It holds no path and no resolution method, so an elan
    machine and a tarball machine with the same binary have the same static part.
  - The proxy, when there is one, is recorded separately, outside `static`: `lean_proxy` = {path, sha256}; also
    `lean_binary_path` (the real binary's path) and `lean_resolved_by`.
- Everything else is envcheck_layered2's (numpy by its package files) and envcheck_layered's.

  envcheck_layered3.py [--json OUT]               the checks: numpy, ngspice, pdk, lean version AND lean binary sha256
  envcheck_layered3.py env OUTROOT [PLAN.json]    writes OUTROOT/ENV.json (layered-env/3)
  envcheck_layered3.py lean                       prints the resolution (real binary, its sha256, the proxy)
"""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import envcheck_layered as E  # noqa: E402
import envcheck_layered2 as E2  # noqa: E402

LEAN_VERSION = "4.35.0"
LEAN_SHA256 = "bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38"
FORMAT = "layered-env/3"


def _sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest() if p and Path(p).is_file() else None


def _out(argv):
    try:
        r = subprocess.run(argv, capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired):
        return None
    return r.stdout.strip() if r.returncode == 0 and r.stdout.strip() else None


def lean_resolution():
    on_path = shutil.which("lean")
    real, how = None, None
    if shutil.which("elan"):
        w = _out(["elan", "which", "lean"])
        if w and Path(w).exists():
            real, how = Path(w).resolve(), "elan which lean"
    if real is None and on_path:
        pre = _out(["lean", "--print-prefix"])
        if pre and (Path(pre) / "bin" / "lean").exists():
            real, how = (Path(pre) / "bin" / "lean").resolve(), "lean --print-prefix"
    if real is None and on_path:
        real, how = Path(on_path).resolve(), "which lean"
    proxy = None
    if on_path and real is not None and Path(on_path).resolve() != real:
        proxy = dict(path=str(Path(on_path).resolve()), sha256=_sha(Path(on_path).resolve()))
    ver = _out([str(real), "--version"]) if real else None
    import re
    m = re.search(r"version (\S+?),", ver or "")
    return dict(path=str(real) if real else None, sha256=_sha(real), resolved_by=how, version=m.group(1) if m else None,
                proxy=proxy)


def checks():
    out = E.checks()
    r = lean_resolution()
    out["lean"] = dict(ok=r["version"] == LEAN_VERSION, want=LEAN_VERSION, got=r["version"])
    out["lean_binary"] = dict(ok=r["sha256"] == LEAN_SHA256, want=LEAN_SHA256, got=r["sha256"], path=r["path"],
                              resolved_by=r["resolved_by"], proxy=r["proxy"])
    return out


def env(plan=None):
    e = E2.env(plan)
    r = lean_resolution()
    static = dict(e["static"], lean=dict(version=r["version"], executable_sha256=r["sha256"]))
    return dict(e, format=FORMAT, static=static, static_sha256=hashlib.sha256(E.canon(static)).hexdigest(),
                lean_binary_path=r["path"], lean_resolved_by=r["resolved_by"], lean_proxy=r["proxy"])


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "env":
        root = Path(a[1])
        plan = json.loads(Path(a[2]).read_text()) if len(a) > 2 else None
        root.mkdir(parents=True, exist_ok=True)
        (root / "ENV.json").write_bytes(E.canon(env(plan)))
        print((root / "ENV.json").read_text())
    elif a and a[0] == "lean":
        print(json.dumps(lean_resolution(), indent=1))
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
