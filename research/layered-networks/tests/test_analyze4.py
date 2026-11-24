"""Tests of analyze4.py (no simulation). Run: python3 -B tests/test_analyze4.py"""
import json
from pathlib import Path
import shutil
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "tests"))
import analyze4  # noqa: E402
import test_analyze3 as T3  # noqa: E402


def run(d, root):
    out = Path(d) / "out4"
    if out.exists():
        shutil.rmtree(out)
    analyze4.main(out, root, "times=bare")
    return json.loads((out / "RESULTS.json").read_text())


def test_stage_n_seal_log_required():
    with tempfile.TemporaryDirectory() as d:
        root = T3.setup(d)
        st = json.loads((root / "NOT1_9804" / "status.json").read_text())
        st["steps"]["N0"]["started"] = "2099-01-01T00:00:00Z"
        (root / "NOT1_9804" / "status.json").write_text(json.dumps(st))
        r = run(d, root)                                   # no SEAL_LOG.json in the N folders: not counted
        assert r["groups"]["NOT1"]["K0"]["counted"] == 0 and any("stage_n_seal_log" in x for x in r["seal_defects"])
        commit = json.loads((Path(d) / "p.json").read_text())["commit"]
        for n in range(4):
            (root / "NOT1_9804" / f"N{n}" / "SEAL_LOG.json").write_text(json.dumps(dict(commit=commit)))
        r = run(d, root)
        assert r["groups"]["NOT1"]["K0"]["counted"] == 1 and r["groups"]["NOT1"]["K3"]["counted"] == 1 and r["seal_defects"] == []
        (root / "NOT1_9804" / "N2" / "SEAL_LOG.json").write_text(json.dumps(dict(commit="0" * 40)))
        r = run(d, root)
        assert r["groups"]["NOT1"]["K0"]["counted"] == 1 and r["groups"]["NOT1"]["K3"]["counted"] == 0


if __name__ == "__main__":
    test_stage_n_seal_log_required()
    print("1 test passed")
