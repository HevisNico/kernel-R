"""Checks of a leancal2.py file (an instance with an inverter front end), beyond tests/check_leancal.py's:
it compiles, `computes` uses only propext, Classical.choice and Quot.sound, a raised lesson score and a raised testError
are rejected (check_leancal.main); and, for the front end, an inverter emission moved one time unit later than measured
(outside the front's emitLate) is rejected.

  tests/check_leancal2.py FILE
"""
from pathlib import Path
import re
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import check_leancal  # noqa: E402


def main(path):
    ok = check_leancal.main(path)
    path = Path(path).resolve()
    text = path.read_text()
    ns = re.search(r"namespace (\S+)", text).group(1)
    block = re.search(r"def testInv : Nat → List \(ReadObservation 1\)\n(.*?)\n  \| _ => \[\]", text, re.S)
    m = re.search(r"\[\((-?\d+) / (\d+) : Rat\)\]", block.group(1))
    if m is None:
        print("no inverter emission in the tests: front negative control not applicable")
        return ok
    a, b = int(m.group(1)), int(m.group(2))
    start = block.start(1) + m.start(1)
    end = block.start(1) + m.end(2)
    bad = text[:start] + f"{a + b} / {b}" + text[end:]                  # emission + 1 tu
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "NegFront.lean"
        f.write_text(bad.replace(ns, ns + "NegFront"))
        good, _ = check_leancal.lean(f)
    print("an inverter emission moved 1 tu later is rejected:", not good)
    ok &= not good
    print("all front checks hold" if ok else "A FRONT CHECK FAILED")
    return ok


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1]) else 1)
