"""Reproducibility of the generated layered Lean files. The files are not kept; their SHA-256 are recorded in
layered/results/REPORT.json under "generated_sha256", and this test regenerates them and compares.

  python -I tests/test_hashes.py record      regenerate into a temporary directory, write the hashes
  python -I tests/test_hashes.py check       regenerate and compare with the recorded hashes

Regenerated: every file of tests/run_layered.py and tests/test_example.py's LayeredEx.lean. No file here uses numpy.
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


def generate(tmp):
    subprocess.run([sys.executable, "-I", str(HERE / "run_layered.py"), str(tmp)], check=True, capture_output=True)
    subprocess.run([sys.executable, "-I", str(HERE / "test_example.py"), str(tmp / "LayeredEx.lean")], check=True, capture_output=True)
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(tmp.glob("*.lean"))}


def main():
    mode = sys.argv[1]
    with tempfile.TemporaryDirectory() as t:
        got = generate(Path(t))
    me = dict(python=platform.python_version(), executable=sys.executable)
    rep = json.loads(REPORT.read_text())
    if mode == "record":
        rep["generated_sha256"] = dict(interpreter=me, files=got)
        REPORT.write_text(json.dumps(rep, indent=1) + "\n")
        print(f"recorded {len(got)} hashes with {me}")
        return
    want = rep["generated_sha256"]
    bad = [n for n in sorted(set(want["files"]) | set(got)) if want["files"].get(n) != got.get(n)]
    print(f"recorded with {want['interpreter']}; checked with {me}")
    for n in bad:
        print(f"  {n}: {'MISSING' if n not in got else 'DIFFERENT'}")
    print(f"test_hashes (layered): {len(want['files']) - len(bad)} of {len(want['files'])} identical")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
