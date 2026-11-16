"""Campaign 4: checks of the implementation against PREDICTION.md, without simulation.

  python -m unittest research/learned-dnf-circuit-campaign-4/test_campaign.py
"""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c4                                               # noqa: E402
import gate4                                            # noqa: E402
import plan                                             # noqa: E402
import plans4                                           # noqa: E402
import predicted as P                                   # noqa: E402
from c4 import dnf                                      # noqa: E402

TEXT = (HERE / "PREDICTION.md").read_text()
FLAT = " ".join(TEXT.split())
PREDICTION_SHA256 = "714cb6b7a37ecca45260a582262750a8705907f889d6fa9fabd4a1cb7ee69c34"
ORIGINALS = {"devnoise.py": "016234f5fa43e2b83e09f0438a0482ae4ddd0d4152aab1ccbdb12ade676dd5a2",
             "model.py": "38630ca29a81619b0793d918ea9b026da0ade18858a48fd544f1d08484917cce",
             "pilot.py": "40ea3b678c61ae2a135bc01447dfd0b6a769ecb9cc1b846a9dc14abe4ca5c0c6",
             "noisegen.py": "2415336b5f31de902ae47d573f76081dd855c6f20355df82d73374ddd2085b45"}


class Protocol(unittest.TestCase):
    def test_prediction_is_the_pushed_file(self):
        self.assertEqual(hashlib.sha256((HERE / "PREDICTION.md").read_bytes()).hexdigest(), PREDICTION_SHA256)

    def test_constants_are_those_of_the_text(self):
        for s in ("Layer-1 pulse amplitude **0.49**", "layer 2 at amplitude 1", "`k = 0, ..., 7`", "**22 units**", "**1.5 units after the FIRE**",
                  "skew bound **1.1 units**", "deadline **2.2 units**", "**0.111 mV between runs, 0.094 mV within a run, 0.009 mV per dose**",
                  "**`R = 3` noisy runs**", "**up to 8 h of expected compute**", "0.01 mV", "at least 1 us", "**`10 x S + n`**",
                  "calibration guard on (`k = 0`), calibration guard off (1), run without noise (2), N1 (3), N2 (4), N3 (5), and the untrained control run last (6)"):
            self.assertIn(s, FLAT)
        self.assertEqual((c4.AMP_AND, c4.AMP_OR, c4.SLOT, c4.WIRE, c4.SKEW_C, c4.DEADLINE_C, c4.STAGES, c4.R), (0.49, 1.0, 22, 1.5, 1.1, 2.2, 8, 3))
        self.assertEqual(c4.DECISION5, dict(between_mV=0.111, within_mV=0.094, per_dose_mV=0.009))
        self.assertEqual(c4.POSITIONS, dict(cal_on=0, cal_off=1, quiet=2, n1=3, n2=4, n3=5, untrained=6))

    def test_seeds_machines_and_noise_seeds(self):
        self.assertEqual(c4.seeds(9), dict(a=[7501, 7502, 7503, 7504, 7505], b=[7506, 7507, 7508, 7509]))
        self.assertEqual([c4.noise_seed(7501, n) for n in (1, 2, 3)], [75011, 75012, 75013])
        self.assertTrue(all(c4.noise_seed(None, n) > 90950 for n in (1, 2, 3)))

    def test_copied_noise_code(self):
        self.assertIn("commit `74e93b4`", (HERE / "noise" / "README.md").read_text())
        self.assertEqual(hashlib.sha256((HERE / "noise" / "noisegen.py").read_bytes()).hexdigest(), ORIGINALS["noisegen.py"])
        sys.path.insert(0, str(HERE / "noise"))
        import pilot
        self.assertEqual(pilot.ALLOWED_SEEDS, ())
        with self.assertRaises(AssertionError):
            pilot.seeded(7501)


class Calendar(unittest.TestCase):
    def test_gates_and_amplitudes(self):
        p, slots = plans4.network((4, 4, 4, 4), "skew")
        self.assertEqual(len(p["gates"]), len(slots))
        for (date, g), s in zip(p["gates"], slots):
            self.assertEqual(date, s["date"] - 3)
            for n, v in g.items():
                self.assertEqual(v, c4.IDIS if n[0] in s["writes"] else 0.0)
        self.assertTrue(all(src[3] == 0.49 for src in p["sources"]))
        self.assertTrue(all(e["amp"] == 1.0 and e["delay"] == 1.5 for e in p["edges"]))

    def test_calibration_plan(self):
        p, reads = plans4.calibration()
        self.assertEqual(len(reads), 8 * 6)
        self.assertEqual(sum(1 for x in reads if x["gated"]), 40)
        c2 = [s for s in p["sources"] if s[1] == "c" and s[2] == 2 and s[3] == 1.0]
        self.assertTrue(any(abs((s[0] % 22) - 0.3) < 1e-9 for s in c2))

    def test_separation_and_settling(self):
        for needs in ((4, 4, 4, 4), (5, 5, 5, 5), (7, 7, 7, 7), (1, 5, 2, 5)):
            for control in (None, "skew", "untrained"):
                slots = dnf.calendar(*needs, control)
                self.assertGreaterEqual(min(dnf.separation(slots).values()), 16)


class Sizing(unittest.TestCase):
    def test_provisional_size_is_that_of_the_text(self):
        I, rows = plan.size(plan.costs(), "device")
        self.assertEqual(I, 9)
        row = next(r for r in rows if r["I"] == 9)
        self.assertAlmostEqual(row["expected_h"], 7.55, places=2)
        self.assertIn("`I = 9`", FLAT)
        self.assertIn("**7.55 h**", FLAT)

    def test_every_stage_within_the_cap(self):
        for model in ("device", "injected"):
            I, rows = plan.size(plan.costs(), model)
            row = next(r for r in rows if r["I"] == I)
            self.assertTrue(all(v <= 14400 for v in row["caps"].values()))
            self.assertLessEqual(row["expected_h"], 8.0)

    def test_extraction_runs(self):
        runs = plan.extract_runs(7501, "a", True)
        self.assertEqual(len(runs), 21)
        self.assertEqual(sum(r["isolation"] for r in runs), 3)
        self.assertEqual(len({r["id"] for r in runs}), 21)
        self.assertTrue(all(r["id"] == r["id"].lower() for r in runs))


class Timing(unittest.TestCase):
    def test_slot_timing_valid(self):
        for skew, deadline, duration in ((P.SKEW_A, P.DEADLINE_A, P.DURATION_A), (P.SKEW_C, P.DEADLINE_C, P.DURATION_C)):
            self.assertTrue(0 <= skew <= deadline < duration)


class ExactArithmetic(unittest.TestCase):
    """Amendment 3, section 2: rounding ties to even, exact rounding-up of one or two square roots, exact solve."""

    def test_ties_to_even(self):
        self.assertEqual([round(F(20735, 2)), round(F(20737, 2)), P.zint(F(1, 200000)), P.zint(F(3, 200000))], [10368, 10368, 0, 2])
        self.assertEqual(P.q(F(5, 100000)), F(0))
        self.assertEqual(P.q(F(15, 100000)), F(2, 10000))

    def test_ceil_sum_sqrt_against_decimal(self):
        import decimal
        import random
        ctx = decimal.Context(prec=80)
        rnd = random.Random(4)
        for _ in range(3000):
            sq = [F(rnd.randint(0, 10 ** 8), rnd.randint(1, 10 ** 4)) for _ in range(rnd.choice((1, 2)))]
            s = sum(ctx.sqrt(decimal.Decimal(v.numerator) / decimal.Decimal(v.denominator)) for v in sq)
            want = int(s.to_integral_value(rounding=decimal.ROUND_CEILING))
            if abs(s - want) > decimal.Decimal(10) ** -40 and abs(s - (want - 1)) > decimal.Decimal(10) ** -40:
                self.assertEqual(P.ceil_sum_sqrt(sq), want, sq)
        self.assertEqual(P.ceil_sum_sqrt([F(4), F(9)]), 5)
        self.assertEqual(P.ceil_sum_sqrt([F(0)]), 0)

    def test_solve_is_exact(self):
        rows = [[1, 0], [1, 1], [1, 2]]
        self.assertEqual(P.solve(rows, [1, 2, 4]), [F(5, 6), F(3, 2)])


if __name__ == "__main__":
    unittest.main()
