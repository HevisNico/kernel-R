"""Tests of campaign_run7.py's argument building (no simulation). Run: python3 -B tests/test_campaign_run7.py"""
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import campaign_run7 as C7  # noqa: E402


def test_stagen_tools_and_save_ref():
    with tempfile.TemporaryDirectory() as d:
        inst = Path(d) / "XOR3_9806"
        inst.mkdir()
        (inst / "seal_push.json").write_text(json.dumps(dict(pushed=True, commit="a" * 40, branch="evidence/combined-seals-K01")))
        nz = Path("/nz")
        plan = dict(stagen="controls4", save_ref_round=2)
        a1 = C7.stagen_argv(plan, nz, "spec", inst / "N1", 9806, 1, "ov")
        a2 = C7.stagen_argv(plan, nz, "spec", inst / "N2", 9806, 2, "ov")
        assert a1[2] == nz / "controls4.py" and "save_ref=1" not in a1 and f"seal_log={'a' * 40}" in a1
        assert a2[2] == nz / "controls5.py" and a2[-1] == "save_ref=1" and "seal_branch=evidence/combined-seals-K01" in a2
        dup = Path(d) / "DUP_XOR3_9806"
        dup.mkdir()
        a3 = C7.stagen_argv(plan, nz, "spec", dup / "N2", 9806, 2, "ov")       # a duplicate: no save_ref, original's seal
        assert a3[2] == nz / "controls4.py" and f"seal_log={'a' * 40}" in a3


if __name__ == "__main__":
    test_stagen_tools_and_save_ref()
    print("1 test passed")
