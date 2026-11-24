"""Tests of campaign_run2.py (no simulation). Run: python3 -B tests/test_campaign_run2.py"""
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import campaign_run2 as C2  # noqa: E402

PLAN = dict(groups=dict(NOT1=dict(spec="specs/not1.json", seeds=[9801])))


def test_running_becomes_interrupted_and_is_never_rerun():
    with tempfile.TemporaryDirectory() as d:
        i = C2.Instance(d, "NOT1", "specs/not1.json", 9801, PLAN)
        i.status["steps"]["D"] = dict(status="running", started="x")
        i.save()
        j = C2.Instance(d, "NOT1", "specs/not1.json", 9801, PLAN)
        assert j.status["steps"]["D"]["status"] == "interrupted"
        assert not j.step("D", [C2.CR.PY, "-c", "pass"], [], "D")
        assert json.loads((j.dir / "status.json").read_text())["steps"]["D"]["status"] == "interrupted"


def test_step_records_running_then_done():
    with tempfile.TemporaryDirectory() as d:
        i = C2.Instance(d, "NOT1", "specs/not1.json", 9801, PLAN)
        seen = Path(d) / "seen.json"
        code = f"import json,shutil; shutil.copy({str(i.status_path)!r}, {str(seen)!r})"
        assert i.step("deck", [C2.CR.PY, "-c", code], [], "deck")
        assert json.loads(seen.read_text())["steps"]["deck"]["status"] == "running"     # written before the run
        assert i.status["steps"]["deck"]["status"] == "done" and "ended" in i.status["steps"]["deck"]


def test_launch_refuses_a_used_outroot():
    with tempfile.TemporaryDirectory() as d:
        (Path(d) / "x").write_text("1")
        try:
            C2.cmd_launch(str(HERE / "dev" / "pipeline_plan_val2.json"), d)
            raise AssertionError("a non-empty OUTROOT was accepted")
        except SystemExit as e:
            assert "refused" in str(e)          # a used OUTROOT (or, while a run is live, a running ngspice)


if __name__ == "__main__":
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
