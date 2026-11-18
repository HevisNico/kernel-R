"""Tests of predict6_guard.py (STOPPING_RULE_AMENDMENT_1.md) without a simulator and without the batch's runs: campaign
5's nominal table (`cases.nominal()`) with synthetic scans, as test_batch.

  python -B -m unittest test_guard        (from this folder, with the pinned venv)
"""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import predict6                                         # noqa: E402
import predict6_guard                                   # noqa: E402
import test_batch as tb                                 # noqa: E402
import cases                                            # noqa: E402
import report6                                          # noqa: E402
P = predict6.P

# Both pair crossings at 1023/256, so K = 8 - 1023/256 and g = d (K - s*) is about 0.001 THETA: the stage-0 single reads
# of a and b are below the frozen geometric fit's floor h >= 0.05 THETA, the case of the batch's 7709.
EDGE = {("a", "pair"): "1023/256", ("b", "pair"): "1023/256"}


def instance(scans, guarded):
    """predict6.predict_instance on the nominal table and `scans`, the deck files replaced by the table itself."""
    t, dose = cases.nominal()
    with mock.patch.object(predict6, "table", return_value=(t, dose, [])), \
            mock.patch.object(predict6, "deck_w", return_value=tb.nominal_w(t)), mock.patch.object(predict6, "deck_u0", return_value=None):
        args = (7701, "a", tb.STATUSES, "on", "off", scans, tb.ones_for(scans), dict(kind="bothfire", fired=True))
        if guarded:
            with mock.patch.object(P, "instance", predict6_guard.guarded_instance):
                return predict6.predict_instance(*args)
        return predict6.predict_instance(*args)


def dumps(x):
    return json.dumps(x, indent=1, default=str)


class Guard(unittest.TestCase):
    def test_edge_is_measured_and_the_frozen_code_raises(self):
        t, dose = cases.nominal()
        why, data = tb.run(t, dose, tb.nominal_scans(EDGE))
        self.assertEqual(why, [])                       # section 3 finds it measured
        with self.assertRaises(TypeError):              # predicted.geometric: best is None
            P.instance(7701, data["t2"], dose, [], predict6.c4.DECISION5)
        with self.assertRaises(TypeError):              # and predict6 alone stops on it
            instance(tb.nominal_scans(EDGE), guarded=False)

    def test_guard_records_it_not_eligible(self):
        x = instance(tb.nominal_scans(EDGE), guarded=True)
        self.assertTrue(x["measured"])
        self.assertFalse(x["eligible"])
        self.assertEqual(len(x["why_not_eligible"]), 1)
        self.assertTrue(x["why_not_eligible"][0].startswith("the frozen prediction code failed (TypeError: "), x["why_not_eligible"])
        self.assertEqual(x["prediction_failed"], x["why_not_eligible"][0])
        self.assertNotIn("budgets", x)
        self.assertNotIn("observation", x)
        gate = []
        with mock.patch.object(predict6, "gate_file", side_effect=lambda xs, out: gate.append(xs)):
            predict6.gate_each([x], Path("."), check=False)
        self.assertEqual((gate, x["gate_K0"]), ([], False))        # no Lean file, not in k
        r = report6.report([x], [])
        self.assertEqual(r["k"], 0)
        self.assertEqual(r["not_eligible"], {"7701": x["why_not_eligible"]})

    def test_other_instances_byte_identical(self):
        for s in ({}, {("a", "pair"): "800/256"}):
            self.assertEqual(dumps(instance(tb.nominal_scans(s), guarded=True)), dumps(instance(tb.nominal_scans(s), guarded=False)))

    def test_batch_patch_is_scoped(self):
        seen = []
        with tempfile.TemporaryDirectory() as d, \
                mock.patch.object(predict6, "predict_batch", side_effect=lambda *a: seen.append(P.instance) or []):
            predict6_guard.predict_batch(d, d, False)
        self.assertEqual(seen, [predict6_guard.guarded_instance])
        self.assertIs(P.instance, predict6_guard.FROZEN_INSTANCE)


if __name__ == "__main__":
    unittest.main()
