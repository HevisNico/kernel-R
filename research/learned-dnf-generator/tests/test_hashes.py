"""Reproducibility of the generated Lean files (the coordinator's item 2 after M4). The files are not kept; their
SHA-256 are recorded in results/REPORT.json under "generated_sha256", and this test regenerates them and compares.

  python -I tests/test_hashes.py record IMPL_ROOT     regenerate into a temporary directory, write the hashes
  python -I tests/test_hashes.py check  IMPL_ROOT     regenerate and compare with the recorded hashes

Regenerated: every file of tests/run_synth.py (Synth_S0..S5, Mut_S0, Mut_S1, Reach, Control_pass, Control_fail and
the 8 Flip_* copies) and tests/k3_finding.py's K3Finding.lean. k3_finding.py needs numpy (campaign 5's cases.py fits
a geometric model in floats), so the interpreter matters for that file: the recorded hashes name the interpreter that
produced them, and `check` reports it.
"""
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
REPORT = HERE.parent / "results" / "REPORT.json"


def interpreter():
    try:
        import numpy
        nv = numpy.__version__
    except ImportError:
        nv = None
    return dict(python=platform.python_version(), numpy=nv, executable=sys.executable)


def generate(impl, tmp):
    subprocess.run([sys.executable, "-I", str(HERE / "run_synth.py"), str(tmp)], check=True, capture_output=True)
    subprocess.run([sys.executable, "-I", str(HERE / "k3_finding.py"), str(impl), str(tmp / "K3Finding.lean")], check=True, capture_output=True)
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(tmp.glob("*.lean"))}


def main():
    mode, impl = sys.argv[1], Path(sys.argv[2]).resolve()
    with tempfile.TemporaryDirectory() as t:
        got = generate(impl, Path(t))
    rep = json.loads(REPORT.read_text())
    if mode == "record":
        rep["generated_sha256"] = dict(interpreter=interpreter(), files=got)
        REPORT.write_text(json.dumps(rep, indent=1) + "\n")
        print(f"recorded {len(got)} hashes with {interpreter()}")
        return
    want = rep["generated_sha256"]
    bad = [n for n in sorted(set(want["files"]) | set(got)) if want["files"].get(n) != got.get(n)]
    print(f"recorded with {want['interpreter']}; checked with {interpreter()}")
    for n in sorted(got):
        print(f"  {n}: {'same' if n not in bad else 'DIFFERENT'} {got[n]}")
    for n in bad:
        if n not in got:
            print(f"  {n}: MISSING")
    print(f"test_hashes: {len(got) - len([n for n in bad if n in got])} of {len(want['files'])} identical")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
