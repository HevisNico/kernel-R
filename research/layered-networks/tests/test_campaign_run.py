"""Tests of campaign_run.py's mechanics (no simulation). Run: python3 -B tests/test_campaign_run.py"""
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402

PLAN = dict(groups=dict(NOT1=dict(spec="specs/not1.json", seeds=[9801], timeout_s=dict(deck=2))))


def test_run_child_cpu_and_timeout():
    with tempfile.TemporaryDirectory() as d:
        rc, cpu, to = CR.run_child([CR.PY, "-c", "x=0\nfor i in range(3*10**7): x+=i"], d, Path(d) / "a.log", 60)
        assert rc == 0 and not to and cpu > 0.3, (rc, cpu, to)
        rc, cpu, to = CR.run_child([CR.PY, "-c", "import time; time.sleep(30)"], d, Path(d) / "b.log", 1)
        assert to and rc != 0


def test_step_done_failed_timeout_and_resume():
    with tempfile.TemporaryDirectory() as d:
        i = CR.Instance(d, "NOT1", "specs/not1.json", 9801, PLAN)
        ok = i.step("deck", [CR.PY, "-c", f"open({str(i.dir / 'x.txt')!r},'w').write('1')"], ["x.txt"], "deck")
        assert ok and i.status["steps"]["deck"]["status"] == "done"
        j = CR.Instance(d, "NOT1", "specs/not1.json", 9801, PLAN)          # resume: kept, not re-run
        assert j.step("deck", [CR.PY, "-c", "raise SystemExit(3)"], ["x.txt"], "deck")
        (i.dir / "x.txt").write_text("2")                                    # an output changed after it was recorded
        try:
            j.done("deck")
            raise AssertionError("a changed output was accepted")
        except SystemExit:
            pass
        assert not j.step("D", [CR.PY, "-c", "raise SystemExit(3)"], ["y"], "D")
        assert j.status["steps"]["D"]["status"] == "failed"
        assert not j.step("D", [CR.PY, "-c", "pass"], [], "D")                # a failed step is never re-run
        assert not j.step("seal", [CR.PY, "-c", "import time; time.sleep(30)"], [], "deck")
        assert j.status["steps"]["seal"]["status"] == "timeout"
        assert json.loads((j.dir / "status.json").read_text())["steps"]["seal"]["status"] == "timeout"


if __name__ == "__main__":
    n = 0
    for k, f in list(globals().items()):
        if k.startswith("test_"):
            f()
            n += 1
            print("ok", k)
    print(f"{n} tests passed")
