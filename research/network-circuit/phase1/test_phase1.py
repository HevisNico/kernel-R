"""Checks of phase 1 that need no simulator: the Python model against the facts proved in `CircuitNetwork.lean`,
the calendars, the guard of the router, and that the committed constants, predictions and Lean instances are what
the scripts give from the committed measures."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import calendars
import model


class Model(unittest.TestCase):
    gap = dict.fromkeys(model.PORTS, 359378)
    seed = model.seed(8, 10, 8, 10)

    def test_nominal_run_of_the_lean_file(self):
        log, writes, left = model.run(self.gap, self.seed, 224)
        self.assertEqual((left, set(writes.values())), ([], {4}))
        self.assertEqual(model.word(log, "a1"), "ssss" + "F" * 14)
        self.assertEqual(model.word(log, "b1"), "ssss" + "F" * 6)
        self.assertEqual(model.word(log, "a2"), "ssss" + "F" * 6)
        self.assertEqual(model.steps(8, 10, 8, 10), 224)

    def test_margins_of_the_lean_file(self):
        lo, hi = dict.fromkeys(model.PORTS, -23000), dict.fromkeys(model.PORTS, 26000)
        self.assertTrue(model.port_margins(self.gap, lo, hi, self.seed, 224))
        self.assertEqual(len(model.outcomes(self.gap, lo, hi, self.seed, 224)), 1)
        wide = dict.fromkeys(model.PORTS, 60000)
        self.assertFalse(model.port_margins(self.gap, lo, wide, self.seed, 224))
        self.assertGreater(len(model.outcomes(self.gap, lo, wide, self.seed, 224)), 1)

    def test_a_read_without_room_goes_both_ways(self):
        gap = dict(self.gap, b1=395000)                      # the fourth dose crosses by 0.05 dose only
        lo, hi = dict.fromkeys(model.PORTS, -10000), dict.fromkeys(model.PORTS, 10000)
        ends = model.outcomes(gap, lo, hi, self.seed, 224)
        i = model.PORTS.index("b1")
        self.assertEqual({w[i] for w, _ in ends}, {4, 5})
        self.assertEqual({(w[0], f[0]) for w, f in ends}, {(4, 14)})          # the source port of A is not touched


class Calendars(unittest.TestCase):
    def test_separated(self):
        c = calendars.reciprocal(18)
        self.assertEqual(calendars.counts(c), (8, 10, 8, 10))
        self.assertTrue(calendars.holds_by_construction(c))
        self.assertGreaterEqual(min(calendars.separation(c).values()), 16)

    def test_control(self):
        c = calendars.reciprocal(8)
        self.assertEqual(calendars.counts(c), (8, 10, 8, 10))
        self.assertFalse(calendars.holds_by_construction(c))
        self.assertLess(min(calendars.separation(c).values()), 8)


class Guard(unittest.TestCase):
    def test_refusal(self):
        import net
        import router
        unit = net.TU
        self.assertIsNone(router.refusal(None, True, 0.0, 1 * unit))
        self.assertEqual(router.refusal(16, True, None, 0.0), "protected")
        self.assertIsNone(router.refusal(16, False, None, 0.0))
        self.assertIsNone(router.refusal(16, False, 0.0, 16 * unit))
        self.assertEqual(router.refusal(16, False, 0.0, 15.9 * unit), "too soon after the previous pulse of the cell")


class Committed(unittest.TestCase):
    def regenerate(self, script, inputs, outputs):
        with tempfile.TemporaryDirectory() as tmp:
            made = [str(Path(tmp) / name) for name in outputs]
            subprocess.run([sys.executable, "-B", str(HERE / script)] + [str(HERE / name) for name in inputs] + made, check=True)
            for name, path in zip(outputs, made):
                self.assertEqual(Path(path).read_text(), (HERE / name).read_text(), name)

    def test_constants(self):
        self.regenerate("constants.py", ["MEASURES.json"], ["CONSTANTS.json"])

    def test_predictions(self):
        self.regenerate("predict.py", ["CONSTANTS.json"], ["PREDICTED.json", "Instances.lean"])

    def test_no_network_result_for_the_instances(self):
        measures = json.loads((HERE / "MEASURES.json").read_text())
        for instance in measures["instances"].values():
            for train in [instance["quiet_train"]] + instance["noisy_trains"]:
                self.assertIn("each port alone", train["calendar"])

    def test_nominal_rehearsal(self):
        import nominal
        committed = json.loads((HERE / "NOMINAL_REHEARSAL.json").read_text())
        self.assertEqual(committed["words_of_the_model"], {"a1": "ssss" + "F" * 14, "a2": "ssss" + "F" * 6, "b1": "ssss" + "F" * 6, "b2": "ssss" + "F" * 14})
        self.assertEqual(committed["calendar"], calendars.reciprocal(18)["name"])


if __name__ == "__main__":
    unittest.main()
