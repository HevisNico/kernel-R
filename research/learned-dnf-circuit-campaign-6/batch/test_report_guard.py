"""Tests of report6_guard.py (the owner's ruling on report6's question 4) without the batch's outputs.

  python -B -m unittest test_report_guard        (from this folder, with the pinned venv)
"""
import difflib
import inspect
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import report6                                          # noqa: E402
import report6_guard                                    # noqa: E402

WALL = {"cal-on": 800.5, "cal-off": 640.25, "pair": 500.0, "line": 470.75, "bothfire": 37.0, "onesided": 220.5}
N = dict(report6.KINDS)


def complete_runs(seeds, machine):
    return [dict(id=f"{s}-{k}-{j}", machine=machine, cost_kind=k, status="complete", wall_s=w + s % 7 + j)
            for s in seeds for k, w in WALL.items() for j in range(N[k])]


def instances(seeds, eligible):
    return [dict(seed=s, measured=True, eligible=s in eligible, gate_K0=s in eligible, why_not_eligible=[] if s in eligible else ["x"],
                 question_1={"a": dict(predicted=4, observed=4, agree=True)}) for s in seeds]


class ReportGuard(unittest.TestCase):
    def test_complete_runs_equal_report6(self):
        recs = complete_runs((7701, 7702, 7703), "a") + complete_runs((7706, 7708), "b")
        xs = instances((7701, 7702, 7703, 7706, 7708), {7701, 7703, 7706})
        self.assertEqual(report6_guard.report(xs, recs), report6.report(xs, recs))

    def test_failed_and_not_started(self):
        recs = complete_runs((7701, 7702, 7703), "a") + complete_runs((7706,), "b")
        recs.append(dict(id="7707-cal-on-0", machine="b", cost_kind="cal-on", status="complete", wall_s=810.0))
        recs.append(dict(id="7707-cal-off-0", machine="b", cost_kind="cal-off", status="failed (exit 1)", wall_s=35.2))
        recs += [dict(id=f"7707-x{i}", machine="b", cost_kind=k, status="not started: a calibration deck did not complete", wall_s=None)
                 for i, k in enumerate(("pair", "pair", "line", "line", "bothfire", "onesided", "onesided"))]
        xs = instances((7701, 7702, 7703, 7706), {7701, 7703, 7706})
        with self.assertRaises(TypeError):              # report6 alone stops on wall_s null
            report6.report(xs, recs)
        out = report6_guard.report(xs, recs)
        complete = [r for r in recs if r["status"] == "complete"]
        self.assertEqual(out["question_4"]["cal-off@b"]["n"], 1)               # the failed 7707-cal-off is not in it
        self.assertEqual(out["question_4"]["pair@b"]["n"], 2)                  # nor the not-started runs
        self.assertEqual(sum(v["n"] for v in out["question_4"].values()), len(complete))
        means = report6.mean_walls(recs)
        self.assertEqual(out["k"], 3)
        self.assertEqual(out["means"], {k: str(v) for k, v in means.items()})
        self.assertEqual(out["decision"], {k: str(v) for k, v in report6.decision(3, means).items()})
        self.assertEqual(out["runs_left_out_of_the_means"], [r["id"] for r in recs if r["status"] not in ("complete", "missing (limit)")])

    def test_one_line_differs(self):
        a = inspect.getsource(report6.report).splitlines()
        b = inspect.getsource(report6_guard.report).splitlines()
        d = [x for x in difflib.unified_diff(a, b, lineterm="", n=0) if x[:1] in "+-" and not x.startswith(("+++", "---"))]
        self.assertEqual(d, ["-    for r in records:", '+    for r in (r for r in records if r["status"] == "complete"):'])


if __name__ == "__main__":
    unittest.main()
