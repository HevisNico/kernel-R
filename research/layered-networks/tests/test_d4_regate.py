"""Tests of d4_regate.py on real records (no simulation). Run with the pinned environment:
python -B tests/test_d4_regate.py

- The audited lines of the 2x solo records reproduce their fits' D4_stage per cell, under the loader each fit used:
  - dev/cal6_xor3 (fit_v2.json): records2, the repeat rule v2 that stage D uses;
  - dev/cal5_not1 and dev/cal5_andor3 (fit.json): records, v1. Under records2, cal5_andor3's c3_0 is 0.0040664
    against v1's 0.0040480 (the disputed repeat). Both are under 0.005.
- The regate of a sealed instance (dev/dryrun_b/ANDOR3_9805) at the frozen 0.005 reproduces its sealed verdicts.
  At 0.0138 (the largest 1x value) it loses K0 through c2_0's "g0: early silence k=2". Its sealed D/ is unchanged.
"""
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import d4_regate as D4  # noqa: E402
import records  # noqa: E402
import records2  # noqa: E402

SOLO = "this run's solo scans"


def fit_d4(f):
    return {c["cell"]: F(c["budgets"]["K0"]["D4_stage"]) for c in json.loads(Path(f).read_text())["cells"]
            if ((c.get("budgets") or {}).get("K0") or {}).get("D4_source") == SOLO}


def per_cell(lines):
    return {c: max(v.values()) for c, v in lines.items() if v}


def test_2x_solo_records_reproduce_their_fits():
    cases = [("dev/cal6_xor3", "fit_v2.json", records2.load), ("dev/cal5_not1", "fit.json", records.load),
             ("dev/cal5_andor3", "fit.json", records.load)]
    for d, fit, load in cases:
        mx, want = per_cell(D4.audited_lines(HERE / d, load)), fit_d4(HERE / d / fit)
        assert want and all(mx[c] == v for c, v in want.items()), (d, want, mx)
    v2 = per_cell(D4.audited_lines(HERE / "dev/cal5_andor3"))
    assert abs(float(v2["c3_0"]) - 0.0040664) < 1e-6 and v2["c3_0"] < D4.FROZEN


def digest(d):
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(Path(d).iterdir()) if p.is_file()}


def test_regate_sealed_instance():
    inst = HERE / "dev/dryrun_b/ANDOR3_9805"
    before = digest(inst / "D")
    r0 = D4.regate(HERE / "specs/andor3.json", inst, D4.FROZEN)
    assert r0["reproduces_sealed"] and r0["regated"] == r0["sealed"] and not r0["newly_failing_K0"]
    r1 = D4.regate(HERE / "specs/andor3.json", inst, F("0.0138"))
    assert r1["sealed"]["eligible_K0"] and not r1["gate_holds_K0"]
    assert r1["newly_failing_K0"] == {"c2_0": ["g0: early silence k=2"]}
    assert digest(inst / "D") == before                                    # the sealed D/ is never written


if __name__ == "__main__":
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
