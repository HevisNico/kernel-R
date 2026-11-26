"""Tests of analyze3.py on a copy of dev/envsmoke and a local bare repository (no simulation).
Run: python3 -B tests/test_analyze3.py"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import analyze3  # noqa: E402
import sealpush as SP  # noqa: E402

os.environ.update(GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")
SRC = HERE / "dev" / "envsmoke"


def setup(d):
    root = Path(d) / "K01"
    shutil.copytree(SRC, root)
    bare = Path(d) / "log.git"
    subprocess.run(["git", "init", "-q", "--bare", str(bare)], check=True)
    SP.install_hook(bare)
    plan = json.loads((root / "PLAN.json").read_text())
    plan["seal_push"] = dict(remote=str(bare), branch="evidence/combined-seals-K01", dry=False)
    (root / "PLAN.json").write_text(json.dumps(plan))
    assert SP.push(bare, plan["seal_push"]["branch"], "NOT1_9804", root / "NOT1_9804" / "seal", Path(d) / "w", Path(d) / "p.json")
    return root


def run(d, root):
    out = Path(d) / "out"
    if out.exists():
        shutil.rmtree(out)
    analyze3.main(out, root, "times=bare")
    return json.loads((out / "RESULTS.json").read_text()), (out / "RESULTS.json").read_bytes()


def test_pushed_after_stage_n_is_not_sealed():
    with tempfile.TemporaryDirectory() as d:
        root = setup(d)
        r, _ = run(d, root)                       # the real N0 started hours before this push
        x = r["instances"][0]["seal"]
        assert x["regenerated_identical"] and not x["log_ok"] and "after stage N" in x["log"]["why"]
        assert r["groups"]["NOT1"]["K0"]["counted"] == 0 and r["groups"]["NOT1"]["K0"]["not_sealed"] == ["NOT1_9804"]


def test_pushed_before_stage_n_counts_and_is_deterministic():
    with tempfile.TemporaryDirectory() as d:
        root = setup(d)
        st = json.loads((root / "NOT1_9804" / "status.json").read_text())
        st["steps"]["N0"]["started"] = "2099-01-01T00:00:00Z"                 # synthetic: stage N after the push
        (root / "NOT1_9804" / "status.json").write_text(json.dumps(st))
        r, b1 = run(d, root)
        _, b2 = run(d, root)
        assert b1 == b2
        assert r["instances"][0]["seal"]["log_ok"] and r["seal_defects"] == []
        assert r["groups"]["NOT1"]["K0"]["counted"] == 1 and r["groups"]["NOT1"]["K3"]["counted"] == 1


def test_regeneration_mismatch_is_a_defect():
    with tempfile.TemporaryDirectory() as d:
        root = setup(d)
        st = json.loads((root / "NOT1_9804" / "status.json").read_text())
        st["steps"]["N0"]["started"] = "2099-01-01T00:00:00Z"
        (root / "NOT1_9804" / "status.json").write_text(json.dumps(st))
        rec = json.loads((root / "NOT1_9804" / "D" / "record.json").read_text())
        rec["words"]["1/0/0"] = "sssFF"                                        # a record that is not the sealed one
        (root / "NOT1_9804" / "D" / "record.json").write_text(json.dumps(rec, indent=1))
        r, _ = run(d, root)
        x = r["instances"][0]["seal"]
        assert not x["regenerated_identical"] and r["groups"]["NOT1"]["K0"]["counted"] == 0


if __name__ == "__main__":
    test_pushed_after_stage_n_is_not_sealed()
    test_pushed_before_stage_n_counts_and_is_deterministic()
    test_regeneration_mismatch_is_a_defect()
    print("3 tests passed")
