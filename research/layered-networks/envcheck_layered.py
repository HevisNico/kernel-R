"""The campaign machine check for the layered campaign (plan §7: a machine that fails it is dropped). Development only.

  envcheck_layered.py [--json OUT]       exit 0 only when every check holds
  envcheck_layered.py env OUTROOT [PLAN.json]   writes OUTROOT/ENV.json (below)

ENV.json, the environment provenance of one machine's OUTROOT (coordinator, 2026-11-24):
- `static`: python (version, executable sha256), numpy (version, sha256 of its dist-info RECORD), ngspice (path, sha256),
  the PDK commit, lean (version, executable sha256), the OS (os-release PRETTY_NAME, kernel release), and the branch
  tips (this tree's HEAD and, from the plan, the kit and controls trees' HEADs);
- `static_sha256`: the sha256 of the canonical `static` part: what must not change within one OUTROOT;
- `uptime_s`: `uptime -s` when it was written (a restart changes it, not the environment).

Checks, each against its pin:
- numpy == the pin of research/circuit/requirements.txt (2.3.5). The inverter kit's in-deck gate (invinst.indeck,
  sim.py, measure.py) computes with numpy; another version is REFUSED, not warned about;
- ngspice on PATH: its executable's sha256 is config.json `circuit.ngspice_sha256`;
- the SKY130 models: research/circuit/pdk at config.json `circuit.pdk_commit`;
- lean on PATH is 4.35.0 (the pinned toolchain of the Lean gates).
"""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
CIRCUIT = (HERE / ".." / "circuit").resolve()
CFG = json.loads((HERE / "config.json").read_text())


def pin(name):
    for line in (CIRCUIT / "requirements.txt").read_text().splitlines():
        m = re.fullmatch(rf"\s*{re.escape(name)}==(\S+)\s*", line)
        if m:
            return m.group(1)
    raise SystemExit(f"no pin for {name} in research/circuit/requirements.txt")


def checks():
    out = {}
    want = pin("numpy")
    try:
        import numpy
        got = numpy.__version__
    except ImportError:
        got = None
    out["numpy"] = dict(ok=got == want, want=want, got=got)
    ng = shutil.which("ngspice")
    real = str(Path(ng).resolve()) if ng else None
    h = hashlib.sha256(Path(real).read_bytes()).hexdigest() if real else None
    out["ngspice"] = dict(ok=h == CFG["circuit"]["ngspice_sha256"], want=CFG["circuit"]["ngspice_sha256"], got=h, path=real)
    pdk = (HERE / CFG["circuit"]["pdk"]).resolve()
    head = subprocess.run(["git", "-C", str(pdk), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip() if pdk.exists() else None
    out["pdk"] = dict(ok=head == CFG["circuit"]["pdk_commit"], want=CFG["circuit"]["pdk_commit"], got=head)
    lv = subprocess.run(["lean", "--version"], capture_output=True, text=True).stdout if shutil.which("lean") else ""
    m = re.search(r"version (\S+?),", lv)
    out["lean"] = dict(ok=bool(m) and m.group(1) == "4.35.0", want="4.35.0", got=m.group(1) if m else None)
    return out


def canon(obj):
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def file_sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest() if path and Path(path).exists() else None


def git_head(tree):
    r = subprocess.run(["git", "-C", str(tree), "rev-parse", "HEAD"], capture_output=True, text=True)
    return r.stdout.strip() or None


def env(plan=None):
    import platform
    try:
        import numpy
        from importlib import metadata
        dist = metadata.distribution("numpy")
        rec = next((f for f in dist.files or [] if str(f).endswith("RECORD")), None)
        np_ = dict(version=numpy.__version__, record_sha256=file_sha(dist.locate_file(rec)) if rec else None)
    except ImportError:
        np_ = dict(version=None, record_sha256=None)
    ng = shutil.which("ngspice")
    ln = shutil.which("lean")
    lv = subprocess.run(["lean", "--version"], capture_output=True, text=True).stdout.strip() if ln else None
    osr = dict(l.split("=", 1) for l in Path("/etc/os-release").read_text().splitlines() if "=" in l) if Path("/etc/os-release").exists() else {}
    pdk = (HERE / CFG["circuit"]["pdk"]).resolve()
    tips = dict(stage_d_tree=git_head(HERE))
    for k in ("kit_tree", "noise_tree"):
        if plan and plan.get(k):
            tips[k] = git_head(plan[k])
    static = dict(python=dict(version=platform.python_version(), executable_sha256=file_sha(Path(sys.executable).resolve())),
                  numpy=np_, ngspice=dict(path=str(Path(ng).resolve()) if ng else None, sha256=file_sha(Path(ng).resolve()) if ng else None),
                  pdk_commit=git_head(pdk) if pdk.exists() else None,
                  lean=dict(version=lv, executable_sha256=file_sha(Path(ln).resolve()) if ln else None),
                  os=dict(pretty_name=osr.get("PRETTY_NAME", "").strip('"'), kernel=platform.release()), tips=tips)
    up = subprocess.run(["uptime", "-s"], capture_output=True, text=True).stdout.strip()
    return dict(format="layered-env/1", static=static, static_sha256=hashlib.sha256(canon(static)).hexdigest(), uptime_s=up)


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "env":
    root = Path(sys.argv[2])
    plan = json.loads(Path(sys.argv[3]).read_text()) if len(sys.argv) > 3 else None
    root.mkdir(parents=True, exist_ok=True)
    (root / "ENV.json").write_bytes(canon(env(plan)))
    print((root / "ENV.json").read_text())
    sys.exit(0)

if __name__ == "__main__":
    r = checks()
    ok = all(v["ok"] for v in r.values())
    text = json.dumps(dict(ok=ok, checks=r), indent=1, sort_keys=True)
    if "--json" in sys.argv:
        Path(sys.argv[sys.argv.index("--json") + 1]).write_text(text + "\n")
    print(text)
    if not ok:
        print("REFUSED: " + ", ".join(k for k, v in r.items() if not v["ok"]), file=sys.stderr)
    sys.exit(0 if ok else 1)
