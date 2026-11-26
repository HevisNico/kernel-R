"""Tests of the ENV.json provenance: envcheck_layered.env, campaign_run3.set_env, analyze2 (no simulation)."""
import json
import os
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import analyze2  # noqa: E402
import campaign_run3 as C3  # noqa: E402
import envcheck_layered as E  # noqa: E402


def test_env_stable_and_mixed_refused():
    a, b = E.env(), E.env()
    assert a["static_sha256"] == b["static_sha256"] and E.canon(a["static"]) == E.canon(b["static"])
    with tempfile.TemporaryDirectory() as d:
        sha = C3.set_env({}, d)
        assert sha == C3.CR.sha(Path(d) / "ENV.json") and os.environ["LAYERED_ENV_SHA256"] == sha
        assert C3.set_env({}, d) == sha and len(json.loads((Path(d) / "ENV_RESUMES.json").read_text())) == 1
        e = json.loads((Path(d) / "ENV.json").read_text())
        e["static_sha256"] = "0" * 64
        (Path(d) / "ENV.json").write_text(json.dumps(e))
        try:
            C3.set_env({}, d)
            raise AssertionError("a mixed environment was accepted")
        except SystemExit as x:
            assert "mixed" in str(x)


def test_analyze2_refuses_mixed():
    with tempfile.TemporaryDirectory() as d:
        d = Path(d)
        sha = C3.set_env({}, d)
        (d / "X_1").mkdir()
        (d / "X_1" / "status.json").write_text(json.dumps(dict(env_sha256=sha, steps={})))
        assert analyze2.env_section(d)["env_json_sha256"] == sha
        (d / "Y_2").mkdir()
        (d / "Y_2" / "status.json").write_text(json.dumps(dict(env_sha256="f" * 64, steps={})))
        try:
            analyze2.env_section(d)
            raise AssertionError("mixed environments were accepted")
        except SystemExit as x:
            assert "Y_2" in str(x)


if __name__ == "__main__":
    test_env_stable_and_mixed_refused()
    test_analyze2_refuses_mixed()
    print("2 tests passed")
