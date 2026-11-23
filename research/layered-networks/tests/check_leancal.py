"""Negative controls and the axiom check of a calibrated Lean file (leancal.py output). Needs Lean on PATH.

  python3 -B tests/check_leancal.py OUT/Cal<TAG><K>.lean

1. the file itself compiles (warnings as errors);
2. `computes`, if present, depends only on propext, Classical.choice and Quot.sound;
3. a copy with one lesson read's measured score raised by 10 thousand must fail;
4. where validity is asserted true: a copy with every testError set to 99999 must fail (Cell.Valid's anchors).
Copies are written to a temporary folder; the file is not changed.
"""
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent.parent
BUILD = HERE / "build"


def lean(path):
    env = dict(os.environ, LEAN_PATH=str(BUILD))
    p = subprocess.run(["lean", "-DwarningAsError=true", str(path)], cwd=path.parent, env=env, capture_output=True,
                       text=True, timeout=3600)
    return p.returncode == 0, p.stdout + p.stderr


def main(path):
    path = Path(path).resolve()
    text = path.read_text()
    ns = re.search(r"namespace (\S+)", text).group(1)
    ok = True
    with tempfile.TemporaryDirectory() as d:
        d = Path(d)

        def variant(name, new):
            f = d / f"{name}.lean"
            f.write_text(new.replace(ns, ns + name))
            return lean(f)
        good, _ = lean(path)
        print("compiles:", good)
        ok &= good
        if "theorem computes" in text:
            good, out = variant("Ax", text.replace(f"end {ns}", f"#print axioms computes\nend {ns}"))
            axioms = re.search(r"depends on axioms: \[([^\]]*)\]", out)
            got = set(a.strip() for a in axioms.group(1).split(",")) if axioms else None
            fine = got is not None and got <= {"propext", "Classical.choice", "Quot.sound"}
            print("axioms of computes:", got, "allowed" if fine else "NOT ALLOWED")
            ok &= fine
        m = re.search(r"(  \| \d+, \d+, \d+, \d+ => .*?, )(-?\d+)(⟩\))\n", text)
        bad = text[:m.start(2)] + str(int(m.group(2)) + 10000) + text[m.end(2):]
        good, _ = variant("NegScore", bad)
        print("a lesson score raised by 10000 is rejected:", not good)
        ok &= not good
        if "checkLayeredValid circuit = true" in text:            # only where validity is asserted true
            good, _ = variant("NegTestError", re.sub(r"testError := \d+", "testError := 99999", text))
            print("testError 99999 is rejected:", not good)
            ok &= not good
    print("all checks hold" if ok else "A CHECK FAILED")
    return ok


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1]) else 1)
