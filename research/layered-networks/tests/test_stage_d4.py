"""Tests of stage_d4.py (no simulation). Run: python3 -B tests/test_stage_d4.py"""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import stage_d  # noqa: E402

old = {g: stage_d.read_masks(g) for g in ("both", "copy", "either")}
import stage_d4  # noqa: E402,F401


def test_masks():
    assert old["either"] == [(1,), (2,)]                       # the defect
    assert stage_d.read_masks("either") == [(1,), (2,), (1, 2)]
    assert stage_d.read_masks("both") == old["both"] == [(1,), (2,), (1, 2)]
    assert stage_d.read_masks("copy") == old["copy"] == [(1,)]


def test_andor3_needs_the_either_pair():
    import spec as specmod
    s = specmod.load(HERE / "specs/andor3.json")
    full = dict(copy={(1,): True}, both={(1,): False, (2,): False, (1, 2): True}, either={(1,): True, (2,): True, (1, 2): True})
    t = {c: dict(full[g]) for c, _, _, g in stage_d.cell_names(s)}
    assert stage_d.compose(s, t)[1]["7"] is True
    del t["c2_0"][(1, 2)]
    assert stage_d.compose(s, t)[1]["7"] is None              # what the dry run met on ANDOR3 9805


if __name__ == "__main__":
    test_masks()
    test_andor3_needs_the_either_pair()
    print("2 tests passed")
