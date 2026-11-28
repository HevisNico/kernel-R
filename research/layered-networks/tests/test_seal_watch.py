"""Tests of seal_watch.py and analyze3 with times=lsremote (local bare repository). Run: python3 -B tests/test_seal_watch.py"""
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "tests"))
import analyze3  # noqa: E402
import seal_watch as SW  # noqa: E402
import sealpush as SP  # noqa: E402
import test_analyze3 as T3  # noqa: E402


def test_lsremote_log_and_analysis():
    with tempfile.TemporaryDirectory() as d:
        root = T3.setup(d)                              # one pushed seal on evidence/combined-seals-K01
        bare = Path(d) / "log.git"
        log = Path(d) / "SEAL_WATCH.log"
        assert SW.poll(bare, log) == 1 and SW.poll(bare, log) == 0      # each tip once
        commit = json.loads((Path(d) / "p.json").read_text())["commit"]
        t = SP.times(bare, "evidence/combined-seals-K01", f"lsremote:{log}")
        assert list(t) == [commit]
        st = json.loads((root / "NOT1_9804" / "status.json").read_text())
        st["steps"]["N0"]["started"] = "2099-01-01T00:00:00Z"
        (root / "NOT1_9804" / "status.json").write_text(json.dumps(st))
        out = Path(d) / "o"
        analyze3.main(out, root, f"times=lsremote:{log}")
        r = json.loads((out / "RESULTS.json").read_text())
        assert r["instances"][0]["seal"]["log_ok"] and r["times_source"]["log"] == "SEAL_WATCH.log"
        assert str(d) not in (out / "RESULTS.json").read_text()                 # no absolute path


if __name__ == "__main__":
    test_lsremote_log_and_analysis()
    print("1 test passed")
