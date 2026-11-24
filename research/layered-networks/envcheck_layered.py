"""The campaign machine check for the layered campaign (plan §7: a machine that fails it is dropped). Development only.

  envcheck_layered.py [--json OUT]       exit 0 only when every check holds

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
