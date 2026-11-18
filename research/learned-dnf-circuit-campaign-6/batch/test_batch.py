"""Tests of the development batch's code without a simulator (BATCH_SPEC.md). The table of the tests is campaign 5's
nominal table (`cases.nominal()`, CALIBRATION.json of #172), with synthetic scans; no run of the batch is read.

  python -B -m unittest test_batch        (from this folder, with the pinned venv)
"""
from fractions import Fraction as F
import copy
from pathlib import Path
import sys
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import batch6                                           # noqa: E402
import predict6                                         # noqa: E402
import report6                                          # noqa: E402
import scan6                                            # noqa: E402
import c4                                               # noqa: E402
import cases                                            # noqa: E402
import predicted as P                                   # noqa: E402


def nominal_scans(L=None, s_star="7/2", half="1/64"):
    L = L or {}
    out = {}
    for key in predict6.CROSSINGS:
        out[key] = dict(crossing=True, consistent=True, contradictory=False, s_star=s_star, half_bracket=half,
                        bracket=[str(F(s_star) - F(half)), str(F(s_star) + F(half))], L=L.get(key, 100000))
    return out


ONES = {c: dict(all_silent=True, silent={"1": True, "2": True}) for c in ("a", "b")}
STATUSES = {f"7701-{x}": "complete" for x in ("cal-on", "cal-off")}


class Guards(unittest.TestCase):
    def test_seeds(self):
        self.assertEqual(batch6.SEEDS, tuple(range(7701, 7711)))
        self.assertEqual([s for s in batch6.SEEDS if batch6.MACHINE_OF[s] == "a"], [7701, 7702, 7703, 7704, 7705])
        self.assertIsNone(batch6.guard_seed("none"))
        self.assertEqual(batch6.guard_seed("7710"), 7710)
        for bad in ("7700", "7711", "7601", "7692", "7801"):
            with self.assertRaises(AssertionError):
                batch6.guard_seed(bad)

    def test_limits(self):
        self.assertEqual((batch6.limit_s("cal"), batch6.limit_s("scan"), batch6.limit_s("onesided")), (2780, 2360, 750))
        self.assertEqual(batch6.DELTAS, (F(1, 4), F(1, 2)))


class Wrapper(unittest.TestCase):
    def setUp(self):
        self.t, self.dose = cases.nominal()

    def test_fire_bit_entries_replaced(self):
        bad = ["FIRE bit False and Z = 100673 disagree at ('b', 3, 'both')", "missing read ('c', 2, 'empty')"]
        with mock.patch.object(P, "load", return_value=([], [])), mock.patch.object(P, "table", return_value=({}, {}, list(bad))):
            _, _, kept = predict6.table("on", "off")
        self.assertEqual(kept, ["missing read ('c', 2, 'empty')"])

    def test_own_level_test(self):
        why, _ = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], nominal_scans(), ONES)
        self.assertEqual(why, [])
        # a level of a's pair read above every firing pair read of the deck: the deck's FIRE bits now disagree with it
        why, _ = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], nominal_scans({("a", "pair"): 100000, ("c", "both"): 200000}), ONES)
        self.assertTrue(any("disagree with the cell's own level" in w and "'c'" in w for w in why), why)

    def test_question_1_in_measured(self):
        why, data = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], nominal_scans(s_star="9/2"), ONES)
        self.assertTrue(any(w.startswith("question 1: need a:") for w in why))
        self.assertEqual(data["question_1"]["a"], dict(predicted=5, observed=4, agree=False))

    def test_causes(self):
        sc = nominal_scans()
        sc[("c", "line2")] = dict(crossing=False, why="no crossing below 8")
        why, _ = predict6.measure_instance(7701, dict(STATUSES, **{"7701-scan-a-pair": "missing (limit)"}), self.t, self.dose, [], sc, ONES)
        self.assertIn("run 7701-scan-a-pair did not complete: missing (limit)", why)
        self.assertIn("scan ('c', 'line2'): no crossing below 8", why)
        ones = dict(ONES, b=dict(all_silent=False, bounds={"1": "4", "2": "4"}))
        why, _ = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], nominal_scans(), ones)
        self.assertTrue(any(w.startswith("one-sided set of b") for w in why))

    def test_rescaling(self):
        self.assertEqual(predict6.scale(100000, 100000), 100000)
        self.assertEqual(predict6.scale(99000, 99000), 100000)
        self.assertEqual(predict6.scale(1, 200000), 0)                  # 0.5, to the even
        self.assertEqual(predict6.scale(3, 200000), 2)                  # 1.5, to the even
        _, data = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], nominal_scans({("a", "pair"): 99000}), ONES)
        self.assertEqual(data["theta"]["a"], 99000)
        self.assertEqual(data["t2"][("a", 4, "both")]["Z"], round(F(self.t[("a", 4, "both")]["Z"]) * 100000 / 99000))
        self.assertEqual(data["t2"][("b", 4, "both")]["Z"], self.t[("b", 4, "both")]["Z"])

    def test_errors_and_room(self):
        L = {("c", "line1"): 100000, ("c", "line2"): 100040, ("c", "both"): 100020}
        why, data = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], nominal_scans(L), ONES)
        self.assertEqual(why, [])
        self.assertEqual(data["S"], dict(a=0, b=0, c=40))
        for c in c4.CELLS:
            st = predict6.steps(data["t2"], c)
            want = max(-(-F(1, 64) * st[predict6.DECK_READ[k]] // 1) for (cc, k) in predict6.CROSSINGS if cc == c)
            self.assertEqual(data["H"][c], want)
        x0 = P.instance(7701, data["t2"], self.dose, [], c4.DECISION5)
        x = predict6.augmented(x0, data["H"], data["S"], data["t2"])
        for K in ("K0", "K3"):
            for c in c4.CELLS:
                for side in ("training", "testing"):
                    self.assertEqual(x["budgets"][K][c][side], x0["budgets"][K][c][side] + data["H"][c] + data["S"][c])
        z = predict6.augmented(x0, {c: 0 for c in c4.CELLS}, {c: 0 for c in c4.CELLS}, data["t2"])
        self.assertEqual((z["room"], z["eligible"], z["room_at_K3"]), (x0["room"], x0["eligible"], x0["room_at_K3"]))
        big = predict6.augmented(x0, {c: 10 ** 5 for c in c4.CELLS}, {c: 0 for c in c4.CELLS}, data["t2"])
        self.assertFalse(big["eligible"])

    def test_one_sided_bounds(self):
        t = {("a", k, f"port {p}"): dict(Z=40000 + 10000 * k) for k in range(8) for p in (1, 2)}
        self.assertEqual(predict6.one_sided_bounds(t, "a", 0), {1: F(6), 2: F(6)})
        self.assertEqual(predict6.one_sided_bounds(t, "a", 5000), {1: F(13, 2), 2: F(13, 2)})
        self.assertEqual(predict6.one_sided_bounds(t, "a", 60000), {1: F(8), 2: F(8)})


class Scan(unittest.TestCase):
    def test_majority_and_consistency(self):
        reads = [dict(s="1", fire=False), dict(s="2", fire=True), dict(s="3/2", fire=True), dict(s="5/4", fire=False), dict(s="11/8", fire=False)]
        self.assertFalse(scan6.contradictory(reads))
        reads += [dict(s="13/8", fire=False)]                         # silent above a fired state
        self.assertTrue(scan6.contradictory(reads))
        states, ok = scan6.verdicts(reads + [dict(s="13/8", fire=True), dict(s="13/8", fire=True)])
        self.assertTrue(states[F(13, 8)])
        self.assertTrue(ok)
        states, ok = scan6.verdicts(reads + [dict(s="13/8", fire=False), dict(s="13/8", fire=True)])
        self.assertFalse(states[F(13, 8)])                            # silent by the majority, above the fired 3/2
        self.assertFalse(ok)


class Choice(unittest.TestCase):
    def costs(self, b, c):
        return {"1/4": dict(pair=b, line=b, both=b, onesided=F(250) / F(151, 100)), "1/2": dict(pair=c, line=c, both=c, onesided=F(250) / F(151, 100))}

    def test_rule(self):
        tie = report6.choose(self.costs(F(785) / F(151, 100), F(785) / F(151, 100)))
        self.assertEqual((tie["B"]["least_k"], tie["C"]["least_k"], tie["choice"], tie["delta"]), (4, 4, "B", "1/4"))
        c = report6.choose(self.costs(F(785) / F(151, 100), F(685) / F(151, 100)))
        self.assertEqual((c["B"]["least_k"], c["C"]["least_k"], c["choice"], c["delta"]), (4, 3, "C", "1/2"))


class StoppingRule(unittest.TestCase):
    MEANS = dict(report6.RM_CAL, pair=F(785), line=F(785), both=F(785), onesided=F(250))

    def test_table(self):
        d3, d4 = report6.decision(3, self.MEANS), report6.decision(4, self.MEANS)
        self.assertEqual((d3["I"], round(float(d3["E"]), 1), d3["go"]), (10, 31319.1, False))
        self.assertEqual((d4["I"], round(float(d4["E"]), 1), d4["go"]), (8, 28504.5, True))
        self.assertFalse(report6.decision(1, self.MEANS)["go"])
        self.assertEqual(report6.least_k(self.MEANS), 4)

    def test_report(self):
        recs = [dict(id=f"x{i}-{k}", machine="a", cost_kind=k, status="complete", wall_s=float(v)) for i in range(2) for k, v in self.MEANS.items()]
        xs = [dict(seed=7701 + i, measured=True, eligible=i < 4, gate_K0=i < 4, question_1={}) for i in range(10)]
        out = report6.report(xs, recs)
        self.assertEqual(out["k"], 4)
        self.assertEqual(out["decision"]["go"], "True")
        self.assertEqual(out["decision"]["I"], "8")


if __name__ == "__main__":
    unittest.main()
