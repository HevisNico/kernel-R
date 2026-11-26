"""Tests of analyze5.py (no simulation). Run: python3 -B tests/test_analyze5.py"""
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "tests"))
import analyze5  # noqa: E402
import test_analyze3 as T3  # noqa: E402


def test_per_group_thresholds():
    assert analyze5.word(20, False, 20) == "established" and analyze5.word(20, False, 30).startswith("held on 20")
    assert analyze5.word(40, True, 20) == "refuted"
    with tempfile.TemporaryDirectory() as d:
        root = T3.setup(d)
        st = json.loads((root / "NOT1_9804" / "status.json").read_text())
        st["steps"]["N0"]["started"] = "2099-01-01T00:00:00Z"
        (root / "NOT1_9804" / "status.json").write_text(json.dumps(st))
        commit = json.loads((Path(d) / "p.json").read_text())["commit"]
        for n in range(4):
            (root / "NOT1_9804" / f"N{n}" / "SEAL_LOG.json").write_text(json.dumps(dict(commit=commit)))
        th = Path(d) / "t.json"
        th.write_text(json.dumps(dict(K0=dict(NOT1=1), K3=dict(NOT1=1))))
        out = Path(d) / "o"
        analyze5.main(out, root, "times=bare", f"thresholds={th}")
        r = json.loads((out / "RESULTS.json").read_text())
        assert r["groups"]["NOT1"]["K0"]["verdict"] == "established" and r["groups"]["NOT1"]["K0"]["threshold"] == 1
        assert r["family"]["K0"] == "established" and r["thresholds"]["file"] == "t.json"


if __name__ == "__main__":
    test_per_group_thresholds()
    print("1 test passed")
