"""Tests of dosedev.py. No simulation is run.   python -B test_dosedev.py REPO"""
import difflib
import hashlib
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import dosedev

REPO = Path(sys.argv.pop(1)).resolve()
dosedev.repo_paths(REPO)
import c4          # noqa: E402
import net         # noqa: E402
import plans4      # noqa: E402


def changed_lines(a, b):
    return [(x, y) for x, y in zip(a.splitlines(), b.splitlines()) if x != y]


class Deck(unittest.TestCase):
    def test_unchanged_parameters_give_the_repository_deck_byte_for_byte(self):
        original, text, changed = dosedev.deck({})
        self.assertEqual(changed, {})
        self.assertEqual(text.encode(), net.deck(cells=c4.CELLS, section="tt").encode())
        self.assertEqual(hashlib.sha256(text.encode()).hexdigest(), hashlib.sha256(original.encode()).hexdigest())

    def test_vhi_changes_one_line_and_only_that_value(self):
        original, text, changed = dosedev.deck(dosedev.parse(["vhi=0.7"]))
        self.assertEqual(changed, dict(vhi=dict(old="0.6", new="0.7")))
        diff = changed_lines(original, text)
        self.assertEqual(len(diff), 1)
        self.assertEqual(len(original.splitlines()), len(text.splitlines()))
        self.assertEqual(diff[0][0].replace("vhi=0.6", "vhi=0.7"), diff[0][1])
        self.assertTrue(diff[0][0].startswith(".param "))

    def test_cs0_and_idis(self):
        original, text, changed = dosedev.deck(dosedev.parse(["vhi=0.7", "cs0=600f", "idis=12.3n"]))
        self.assertEqual(changed, dict(vhi=dict(old="0.6", new="0.7"), cs0=dict(old="400f", new="600f"), idis=dict(old="8.2n", new="12.3n")))
        diff = changed_lines(original, text)
        self.assertEqual(len(diff), 2)
        for old, new in diff:
            self.assertTrue(old.startswith(".param "))
        self.assertEqual(original.replace("vhi=0.6", "vhi=0.7").replace("cs0=400f", "cs0=600f").replace("idis=8.2n", "idis=12.3n"), text)

    def test_the_same_value_gives_the_same_deck(self):
        original, text, _ = dosedev.deck(dosedev.parse(["vhi=0.6", "cs0=400f", "idis=8.2n", "vlo=0.5"]))
        self.assertEqual(original, text)

    def test_refusals(self):
        for bad in (["cf0=15p"], ["vhi=0.7", "vhi=0.8"], ["vhi=abc"], ["vhi=0.7;quit"], ["vinit=0.4"], ["vhi"]):
            with self.assertRaises(AssertionError, msg=str(bad)):
                dosedev.parse(bad)

    def test_numbers(self):
        self.assertAlmostEqual(dosedev.number("12.3n"), 12.3e-9)
        self.assertAlmostEqual(dosedev.number("600f"), 600e-15)
        self.assertEqual(dosedev.number("0.7"), 0.7)
        self.assertAlmostEqual(dosedev.number("8.2n"), c4.IDIS)

    def test_the_gate_of_a_changed_idis(self):
        plan, _ = plans4.calibration()
        new = dosedev.number("12.3n")
        gates = [(d, {k: (new if v else 0.0) for k, v in s.items()}) for d, s in plan["gates"]]
        self.assertEqual({v for _, s in plan["gates"] for v in s.values()}, {0.0, c4.IDIS})
        self.assertEqual({v for _, s in gates for v in s.values()}, {0.0, new})
        self.assertEqual([[k for k, v in s.items() if v] for _, s in gates], [[k for k, v in s.items() if v] for _, s in plan["gates"]])


if __name__ == "__main__":
    unittest.main(verbosity=2)
