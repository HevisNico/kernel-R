"""Tests of campaign_run3.py (no simulation). Run: python3 -B tests/test_campaign_run3.py"""
from pathlib import Path
import sys
import tempfile
import threading
import time

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import campaign_run3 as C3  # noqa: E402


def test_budget_never_exceeds_and_weights():
    b = C3.Budget(4)
    seen, lock = [], threading.Lock()

    def job(n):
        got = b.acquire(n)
        with lock:
            seen.append(b.used)
        time.sleep(0.05)
        b.release(got)
    ts = [threading.Thread(target=job, args=(n,)) for n in (2, 2, 1, 1, 1, 2, 3, 1)]
    [t.start() for t in ts]
    [t.join() for t in ts]
    assert max(seen) <= 4 and b.peak <= 4 and b.used == 0
    assert b.acquire(9) == 4                                  # capped at the budget
    b.release(4)


def test_inverter_step_takes_its_inverter_count():
    plan = dict(groups=dict(XOR3=dict(spec="specs/xor3.json", seeds=[9803])))
    with tempfile.TemporaryDirectory() as d:
        i = C3.Instance(d, "XOR3", "specs/xor3.json", 9803, plan)
        C3.BUDGET = C3.Budget(4)
        assert i.step("inverters", [C3.CR.PY, "-c", "pass"], [], "inverters")
        assert i.status["steps"]["inverters"]["cores"] == 2
        assert i.step("deck", [C3.CR.PY, "-c", "pass"], [], "deck") and i.status["steps"]["deck"]["cores"] == 1
        i.plan = dict(plan, steps_until="D")
        assert not i.step("seal", [C3.CR.PY, "-c", "pass"], [], "seal") and "seal" not in i.status["steps"]


if __name__ == "__main__":
    test_budget_never_exceeds_and_weights()
    test_inverter_step_takes_its_inverter_count()
    print("2 tests passed")
