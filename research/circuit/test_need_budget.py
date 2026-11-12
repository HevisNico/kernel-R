"""Numerical and missing-data checks for the retrospective diagnostic."""
import math
from pathlib import Path
import tempfile
import unittest

import need_budget


class NeedBudgetTests(unittest.TestCase):
    def test_known_centre_and_bounded_variation(self):
        r = need_budget.proxy_budget(math.exp(-3.5 * 0.04), 1, [0.038, 0.042])
        self.assertEqual(r["ceiling_count"], 4)
        self.assertAlmostEqual(r["a_proxy"], 0)
        self.assertAlmostEqual(r["b_sample"], 0.002)
        self.assertAlmostEqual(r["room_proxy"], 0.02 - 4 * 0.002 - 1 / 8000)
        self.assertTrue(r["proxy_passes"])

    def test_no_dispersion_is_not_zero(self):
        r = need_budget.proxy_budget(0.99, 1, [], fallback=0.04)
        self.assertEqual(r["ceiling_count"], 1)
        for k in ("b_sample", "room_proxy", "proxy_passes"):
            self.assertIsNone(r[k])
        self.assertEqual(r["d0_source"], "pooled_fallback")

    def test_invalid_inputs_are_not_qualified(self):
        for args in ((0, 1, [0.04]), (1, math.nan, [0.04]),
                     (1, 1, [math.inf]), (1, 1, [-0.04]), (1, 1, [])):
            with self.assertRaises(ValueError):
                need_budget.proxy_budget(*args)

    def test_whole_missing_campaign_keeps_every_planned_port(self):
        with tempfile.TemporaryDirectory() as folder:
            rows, _ = need_budget.analyze(Path(folder))
        self.assertEqual(len(rows), 200)
        self.assertTrue(all(r["qualification"] == "not_evaluable" for r in rows))
        self.assertTrue(all(r["proxy_passes"] is None for r in rows))
        self.assertTrue(all(r["observed_silent"] is None for r in rows))

    def test_known_disagreement_is_retained_even_when_proxy_passes(self):
        rows, _ = need_budget.analyze(Path(__file__).parent / "results")
        row = next(r for r in rows if (r["run"], r["port"]) == ("mc_2064", 1))
        self.assertEqual(row["observed_silent"], 3)
        self.assertEqual(row["ceiling_count"], 4)
        self.assertTrue(row["proxy_passes"])
        self.assertFalse(row["count_agrees"])
        self.assertEqual(row["qualification"], "not_evaluable")

    def test_scale_of_voltage_proxy_cancels(self):
        x = need_budget.proxy_budget(0.8, 1, [0.039, 0.041])
        y = need_budget.proxy_budget(0.4, 0.5, [0.039, 0.041])
        self.assertEqual(x, y)


if __name__ == "__main__":
    unittest.main()
