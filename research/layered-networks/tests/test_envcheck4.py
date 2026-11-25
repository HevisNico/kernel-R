"""Tests of envcheck_layered4.py and campaign_run12 (no simulation). Run with the pinned environment:
python -B tests/test_envcheck4.py

- Python 3.13.18 passes; a different reported version is REFUSED, and campaign_run12.set_env then writes no ENV.json.
- envcheck_layered3 alone does not refuse another Python version (the defect this version fixes).
"""
from pathlib import Path
import platform
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import campaign_run12 as C12  # noqa: E402
import envcheck_layered3 as E3  # noqa: E402
import envcheck_layered4 as E4  # noqa: E402


def test_python_pinned():
    c = E4.checks()
    assert c["python"]["ok"] == (platform.python_version() == "3.13.18")
    saved = platform.python_version
    platform.python_version = lambda: "3.13.17"
    try:
        c = E4.checks()
        assert not c["python"]["ok"] and c["python"]["got"] == "3.13.17"
        assert "python" not in E3.checks()                                   # envcheck_layered3 had no such check
        with tempfile.TemporaryDirectory() as d:
            try:
                C12.set_env({}, Path(d) / "out")
                raise AssertionError("another Python version was accepted")
            except SystemExit as e:
                assert "python" in str(e)
            assert not (Path(d) / "out" / "ENV.json").exists()
    finally:
        platform.python_version = saved


if __name__ == "__main__":
    test_python_pinned()
    print("1 test passed")
