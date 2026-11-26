"""Tests of sealpush.py on a local bare repository (no network). Run: python3 -B tests/test_sealpush.py"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "tests"))
import sealpush as SP  # noqa: E402
import test_stage_d as T  # noqa: E402
import seal  # noqa: E402

os.environ.update(GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")


def make_seal(d, name, seed):
    inst = T.write_instance(d, name, T.fake_prediction(seed=seed))
    seal.seal(Path(d) / f"S_{name}", inst)
    return Path(d) / f"S_{name}"


def test_push_append_times_and_failures():
    with tempfile.TemporaryDirectory() as d:
        d = Path(d)
        bare = d / "remote.git"
        subprocess.run(["git", "init", "-q", "--bare", str(bare)], check=True)
        SP.install_hook(bare)
        s1, s2 = make_seal(d, "a", 9801), make_seal(d, "b", 9802)
        br = "evidence/combined-seals-K01"
        assert SP.push(bare, br, "NOT1_9801", s1, d / "w", d / "p1.json")
        assert SP.push(bare, br, "NOT1_9802", s2, d / "w", d / "p2.json")
        r1, r2 = (json.loads((d / f).read_text()) for f in ("p1.json", "p2.json"))
        assert r1["pushed"] is True and r2["previous"] == r1["commit"] and r1["seal_sha256"] == SP.seal_sha(s1)
        lines = SP.log_lines(bare, br, d / "check")
        assert [x["instance"] for x in lines] == ["NOT1_9801", "NOT1_9802"]
        assert lines[1]["seal_sha256"] == SP.seal_sha(s2) and lines[1]["commit"] == r2["commit"]
        t = SP.times(bare, br, "bare")
        assert set(t) == {r1["commit"], r2["commit"]} and t[r1["commit"]] <= t[r2["commit"]]
        # dry: no push
        assert SP.push(bare, br, "X_1", s1, d / "w2", d / "p3.json", dry=True)
        assert json.loads((d / "p3.json").read_text())["pushed"] == "dry" and len(SP.log_lines(bare, br, d / "c2")) == 2
        # a broken seal is refused
        (s1 / "MANIFEST.json").write_text("{}")
        assert not SP.push(bare, br, "Y_1", s1, d / "w", d / "p4.json")
        assert "does not verify" in json.loads((d / "p4.json").read_text())["why"]
        # an unreachable remote: the push fails
        assert not SP.push(d / "nowhere.git", br, "Z_1", s2, d / "w3", d / "p5.json")
        # a rewritten log is detected
        w = d / "w"
        (w / "SEALS.txt").write_text("forged\n")
        subprocess.run(["git", "-C", str(w), "commit", "-qam", "rewrite"], check=True)
        subprocess.run(["git", "-C", str(w), "push", "-q", "-f", str(bare), f"HEAD:refs/heads/{br}"], check=True)
        try:
            SP.log_lines(bare, br, d / "c3")
            raise AssertionError("a rewritten log was accepted")
        except AssertionError as e:
            assert "rewritten" in str(e)


if __name__ == "__main__":
    test_push_append_times_and_failures()
    print("1 test passed")
