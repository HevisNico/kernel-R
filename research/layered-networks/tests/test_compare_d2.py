"""Tests of compare_d2.py (no simulation). Run: python3 -B tests/test_compare_d2.py"""
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "tests"))
import compare_d2  # noqa: E402
import seal  # noqa: E402
import test_stage_d as T  # noqa: E402


def run(pred, rec):
    with tempfile.TemporaryDirectory() as d:
        seal.seal(Path(d) / "S", T.write_instance(d, "i", pred))
        (Path(d) / "r.json").write_text(json.dumps(rec))
        return compare_d2.compare(Path(d) / "S", T.SPECS / "not1.json", Path(d) / "r.json")


def skew_slot(cell, fired):
    return dict(kind="skew", info=dict(cell=cell, layer=1, index=0),
                reads=[dict(layer=1, index=0, emission=5 if fired else None)])


def test_skews():
    pred = T.fake_prediction()
    pred["prediction"]["skew_silent"] = ["c1_0"]          # a both cell, for the test only
    rec = T.fake_record()
    assert run(pred, rec)["verdict"] == "agrees"           # no `skews` in the record: not required (compare_d's rule)
    rec["skews"] = []
    r = run(pred, rec)
    assert r["verdict"] == "refuted" and r["differences"][0]["why"] == "no shift slot" and r["format"].endswith("/2")
    rec["slots"].append(skew_slot("c1_0", False))
    rec["skews"] = [2]
    assert run(pred, rec)["verdict"] == "agrees"
    rec["slots"][2] = skew_slot("c1_0", True)
    assert run(pred, rec)["verdict"] == "refuted"
    import compare_d
    assert compare_d.FORMAT.endswith("/1")                 # compare_d restored after the call


if __name__ == "__main__":
    test_skews()
    print("ok test_skews\n1 test passed")
