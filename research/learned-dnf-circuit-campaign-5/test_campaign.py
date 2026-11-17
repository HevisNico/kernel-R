"""Campaign 5: checks of the implementation against PREDICTION.md (commit a2d8bad), without simulation.

  python -m unittest test_campaign        (from this folder)

Campaign 4's test_campaign.py (093995b), rewritten for campaign 5's rules: the protocol file, the seeds, the limits,
the sizing and its exact figure (10.5: the frozen code must reproduce I = 12 and 28 788.89 s), the split of a stage,
the closed map of stage names, the guards, the exact guarded fit (a float in a row refused), the rehearsal's stages
against the kit's own bound.
"""
from fractions import Fraction as F
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c4                                               # noqa: E402
import plan                                             # noqa: E402
import plans4                                           # noqa: E402
import predicted as P                                   # noqa: E402
import run4                                             # noqa: E402
from c4 import dnf                                      # noqa: E402

TEXT = (HERE / "PREDICTION.md").read_text()
FLAT = " ".join(TEXT.split())
PREDICTION_SHA256 = "36249501a232fb3a9f7e092ac6dee1927767cde852b9519ced7f9c671c110b10"
NOISEGEN_SHA256 = "2415336b5f31de902ae47d573f76081dd855c6f20355df82d73374ddd2085b45"


def kit():
    spec = importlib.util.spec_from_file_location("launch", HERE.parent / "sky130-supervisor-closure" / "launchkit" / "launch.py")
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


class Protocol(unittest.TestCase):
    def test_prediction_is_the_pushed_file(self):
        self.assertEqual(hashlib.sha256((HERE / "PREDICTION.md").read_bytes()).hexdigest(), PREDICTION_SHA256)

    def test_constants_are_those_of_the_text(self):
        for s in ("Layer-1 pulse amplitude **0.49**", "layer 2 at amplitude 1", "`k = 0, ..., 7`", "**22 units**", "**1.5 units after the FIRE**",
                  "skew bound is **1.1 units**", "deadline is **2.2 units**", "`theta = 100 000`", "**1 000 000**",
                  "`b = 0.111` mV between runs, `w = 0.094` mV within a run, `d = 0.009` mV per dose", "`R = 3`", "**`10 x S + n`**",
                  "**90 961**", "**7691, 7692, 7693**", "**Four runs at a time on each machine.**",
                  "calibration guard on (0), calibration guard off (1), run without noise (2), N1 (3), N2 (4), N3 (5), the untrained control run (6)"):
            self.assertIn(s, FLAT)
        self.assertEqual((c4.AMP_AND, c4.AMP_OR, c4.SLOT, c4.WIRE, c4.SKEW_C, c4.DEADLINE_C, c4.STAGES, c4.R, c4.JOBS), (0.49, 1.0, 22, 1.5, 1.1, 2.2, 8, 3, 4))
        self.assertEqual(c4.DECISION5, dict(between_mV=0.111, within_mV=0.094, per_dose_mV=0.009))
        self.assertEqual(c4.POSITIONS, dict(cal_on=0, cal_off=1, quiet=2, n1=3, n2=4, n3=5, untrained=6))
        self.assertEqual((P.THETA, P.RAIL), (100000, 1000000))

    def test_seeds_machines_and_noise_seeds(self):
        self.assertEqual(c4.seeds(12), dict(a=list(range(7601, 7607)), b=list(range(7607, 7613))))
        self.assertEqual([c4.noise_seed(7601, n) for n in (1, 2, 3)], [76011, 76012, 76013])
        self.assertEqual(c4.noise_seed(7612, 3), 76123)
        self.assertEqual(c4.DEV_SEEDS, (7691, 7692, 7693))
        self.assertEqual([c4.noise_seed(s, n) for s in (7691, 7693) for n in (1, 3)], [76911, 76913, 76931, 76933])
        self.assertEqual(c4.noise_seed(None, 1), 90961)
        with self.assertRaises(AssertionError):
            c4.noise_seed(None, 2)

    def test_copied_noise_code_is_unchanged_and_unused(self):
        self.assertEqual(hashlib.sha256((HERE / "noise" / "noisegen.py").read_bytes()).hexdigest(), NOISEGEN_SHA256)
        self.assertEqual(c4.NOISE_MODELS, ("none", "injected"))


class Guards(unittest.TestCase):
    """PREDICTION.md, 10.6: the seed guard and the noise-model guard (outside the kit, every mismatch seed is refused)."""

    def test_seed_guard(self):
        out = Path(tempfile.mkdtemp()) / "run"
        run4.guard(None, 12, out, None)
        for seed, stage in ((7601, None), (7612, None), (7613, None), (7501, None), (7512, None), (7691, "RM"), (7691, "Q"), (7691, None),
                            (7601, "RM"), (7690, "RM")):
            with self.assertRaises(AssertionError, msg=(seed, stage)):
                run4.guard(seed, 12, out, stage)

    def test_noise_model_guard(self):
        run4.noise_guard("network", "injected")
        run4.noise_guard("cal", "none")
        for kind, noise in (("network", "device"), ("extract", "none"), ("network", "corrected")):
            with self.assertRaises(AssertionError):
                run4.noise_guard(kind, noise)


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


class Limits(unittest.TestCase):
    """PREDICTION.md, 10.4 and 11.2."""

    def test_campaign_limits(self):
        cost = plan.costs()
        lim = lambda needs, sc: plan.with_limits(plan.network_run(7601, "a", needs, sc, "injected"), cost, "injected")["timeout_s"]
        self.assertEqual(c4.limit(cost["calibration_deck_s"]), 1850)
        self.assertEqual([lim((4, 4, 4, 4), s) for s in ("quiet", "n1", "untrained")], [1700, 2640, 740])
        self.assertEqual([lim((7, 7, 7, 7), s) for s in ("quiet", "n1")], [2130, 3340])
        for s in ("**calibration deck 1 850 s**", "with the skew slots 1 700 s", "noisy run 2 640 s", "untrained control run 740 s", "2 130 s and 3 340 s",
                  "`limit = 10 x ceil(2 x expected / 10)`"):
            self.assertIn(s, FLAT)

    def test_rehearsal_limits(self):
        cost = plan.costs()
        self.assertEqual(c4.rehearsal_limit(cost["calibration_deck_s"]), 2780)
        lim = lambda needs, sc: plan.with_limits(plan.network_run(7691, "a", needs, sc, "injected"), cost, "injected", rehearsal=True)
        self.assertEqual([lim((4, 4, 4, 4), s)["timeout_s"] for s in ("quiet", "untrained", "n1")], [2540, 1110, 3580])
        self.assertEqual([lim((7, 7, 7, 7), s)["timeout_s"] for s in ("quiet", "n1")], [3200, 3580])
        self.assertEqual(lim((7, 7, 7, 7), "n1")["campaign_limit_s"], 3340)
        self.assertIn("`min(10 x ceil(3 x expected / 10), 3 580 s)`", FLAT)

    def test_ceil10_is_exact(self):
        self.assertEqual([c4.ceil10(x) for x in (1850, 1850.0, F(18501, 10), 0.1, 2632)], [1850, 1850, 1860, 10, 2640])


class Sizing(unittest.TestCase):
    """PREDICTION.md, 10.5: the frozen code must reproduce I = 12 and 28 788.89 s (to 0.01 s)."""

    def test_size_and_expected_compute(self):
        cost = plan.costs()
        I, rows = plan.size(cost)
        self.assertEqual(I, 12)
        st = plan.stages(I, "injected", False, cost)
        self.assertAlmostEqual(plan.expected_compute(st), 28788.89, delta=0.01)
        self.assertGreater(next(r for r in rows if r["I"] == 13)["expected_h"], 8.0)
        self.assertEqual([n for n, _ in st], ["M1", "M2", "Q", "N1", "N2", "N3"])
        caps = {n: plan.stage_cap(r) for n, r in st}
        self.assertEqual(caps, dict(M1=9300.0, M2=9300.0, Q=8310.0, N1=12587.5, N2=12587.5, N3=12587.5))
        quiet = plan.expected(plan.network_run(7601, "a", (4, 4, 4, 4), "quiet", "injected"), cost, "injected")
        self.assertAlmostEqual(quiet, 845.3149, delta=0.0001)
        for s in ("**`I = 12`**", "28 788.89 s", "**845.3149 s**"):
            self.assertIn(s, FLAT)
        self.assertEqual({r["seed"] for r in dict(st)["M1"]}, {7601, 7602, 7603, 7607, 7608, 7609})

    def test_every_stage_within_the_kit(self):
        K = kit()
        for n, runs in plan.stages(12, "injected", False, plan.costs()):
            K.check_budget(runs, K.MAX_BUDGET_S, c4.JOBS)


class Stages(unittest.TestCase):
    """BEFORE_M.md, the runs of each stage, the split of Q and N, the closed map of stage names."""

    def setUp(self):
        self.dir = Path(tempfile.mkdtemp())
        d = dict(rehearsal=dict(path="REHEARSAL.json", commit="0" * 40, sha256="0" * 64, verdict="test"))
        (self.dir / "BEFORE_M.md").write_text(plan.before_m_text(plan.before_m(d)))
        self.b = plan.read_before_m(self.dir / "BEFORE_M.md")

    def test_before_m(self):
        self.assertEqual((self.b["I"], self.b["noise_model"]), (12, "injected"))
        self.assertAlmostEqual(self.b["expected_compute_s"], 28788.89, delta=0.01)
        self.assertEqual(self.b["measure_stages"]["M1"]["limits_s"], [1850])
        self.assertEqual(self.b["limits"]["need7_s"]["noisy"], 3340)

    def test_stage_m(self):
        for name in ("M1", "M2"):
            M, protocol, I = plan.stage_runs(name, here=self.dir)
            self.assertEqual((len(M), protocol, I), (12, "PREDICTION.md", 12))
            self.assertTrue(all(7601 <= r["seed"] <= 7612 and r["timeout_s"] == 1850 for r in M))

    def test_split_at_need_7(self):
        cost = plan.costs()
        runs = [plan.with_limits(plan.network_run(s, c4.machine_of(s, 12), (7, 7, 7, 7), f"n{k}", "injected"), cost, "injected")
                for k in (1, 2, 3) for s in range(7601, 7613)]
        (self.dir / "PREDICTED.json").write_text(json.dumps(dict(network_runs=runs)))
        with self.assertRaises(AssertionError):
            plan.stage_runs("N1", here=self.dir)        # at need 7, N1 does not fit: only its parts exist
        p1, protocol, _ = plan.stage_runs("N1.1", here=self.dir)
        p2, _, _ = plan.stage_runs("N1.2", here=self.dir)
        self.assertEqual(protocol, "PREDICTED.json")
        self.assertEqual(sorted(r["seed"] for r in p1 + p2), list(range(7601, 7613)))
        K = kit()
        for p in (p1, p2):
            K.check_budget(p, K.MAX_BUDGET_S, c4.JOBS)

    def test_governing_map_is_closed(self):
        for n in ("M", "M1", "M2", "RC", "RM"):
            self.assertTrue(plan.governing_of(n).endswith("/PREDICTION.md"))
        for n in ("Q", "Q.1", "N1", "N3.2", "RQ", "RN", "RMEM"):
            self.assertTrue(plan.governing_of(n).endswith("/PREDICTED.json"))
        for n in ("E1", "MEMD", "Mx", "X", "GUARD", "RG", "N4", "Q1"):
            with self.assertRaises(SystemExit):
                plan.governing_of(n)

    def test_campaign_ids_are_valid_and_distinct(self):
        import re
        ids = ["learned-dnf-circuit-5-" + n.lower().replace(".", "-") for n in ("M1", "M2", "Q", "Q.1", "N1.2")]
        ids += ["learned-dnf-circuit-5-rehearsal-" + n.lower() for n in plan.REHEARSAL_STAGES]
        self.assertEqual(len(set(ids)), len(ids))
        self.assertTrue(all(re.fullmatch(r"[a-z0-9][a-z0-9-]{2,63}", i) for i in ids))


class Rehearsal(unittest.TestCase):
    """PREDICTION.md, 11.2: every rehearsal stage one manifest over both machines, within the kit's bound."""

    def test_rehearsal_stages_fit_the_kit(self):
        K = kit()
        dev = dict(instances=[dict(seed=s, measured=True, needs=dict(a=7, b=7, c1=7, c2=7)) for s in c4.DEV_SEEDS], control_instance=7691)
        want = dict(RC=13665.0, RM=13950.0, RQ=13400.0, RN=14360.0, RMEM=14360.0)
        for n in plan.REHEARSAL_STAGES:
            runs = plan.rehearsal_runs(n, dev)
            self.assertEqual({r["machine"] for r in runs}, {"a", "b"})
            a = [r for r in runs if r["machine"] == "a"]
            self.assertEqual([r["id"][2:] for r in a], [r["id"][2:] for r in runs if r["machine"] == "b"])
            self.assertGreaterEqual(len(a), 4)
            self.assertEqual(K.check_budget(runs, K.MAX_BUDGET_S, c4.JOBS)["aggregate_cap_s"], want[n])

    def test_rehearsal_seeds_and_noise(self):
        rc = plan.rehearsal_runs("RC")
        self.assertTrue(all(r["seed"] is None for r in rc))
        self.assertEqual([r["timeout_s"] for r in rc if r.get("stopped_on_purpose")], [120, 120])
        self.assertEqual({r.get("noise_seed") for r in rc if r["kind"] == "network" and r["noise"] != "none"}, {90961})
        rm = plan.rehearsal_runs("RM")
        self.assertEqual(sorted({r["seed"] for r in rm}), list(c4.DEV_SEEDS))
        rn = [r for r in plan.rehearsal_runs("RN", None) if r["machine"] == "a"]
        self.assertEqual([r["noise_seed"] for r in rn], [76911, 76921, 76931, 76911])
        rmem = [r for r in plan.rehearsal_runs("RMEM", None) if r["machine"] == "a"]
        self.assertEqual([r["noise_seed"] for r in rmem], [76911, 76921, 76931, 76912])
        self.assertTrue(all(tuple(r["needs"]) == (7, 7, 7, 7) for r in rmem))


class ExactArithmetic(unittest.TestCase):
    """PREDICTION.md, 4.2: ties to even, exact rounding-up of one or two square roots, the exact guarded fit."""

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
        x = P.solve([[1, 0], [1, 1], [1, 2]], [1, 2, 4])
        self.assertEqual(x, [F(5, 6), F(3, 2)])
        self.assertTrue(all(type(v) is F for v in x))

    def test_a_float_in_the_fit_is_refused(self):
        with self.assertRaises(AssertionError):
            P.solve([[1, 0.0], [1, 1]], [1, 2])
        with self.assertRaises(AssertionError):
            P.solve([[1, 0], [1, 1]], [1, 2.0])

    def test_the_guarded_fit_is_built_of_integers(self):
        t = {(c, k, r): dict(Z=100000 + 1000 * k + 7 * len(P.ports(r))) for c in ("a", "b") for k in range(8) for r in P.GUARDED_READS_1}
        tup = P.guarded(t, P.LAYER1, 6, P.GUARDED_READS_1)
        self.assertTrue(all(type(v) is int for v in list(tup["help"].values()) + list(tup["gain"].values()) + [tup["dose"]]))


class Timing(unittest.TestCase):
    def test_slot_timing_valid(self):
        for skew, deadline, duration in ((P.SKEW_A, P.DEADLINE_A, P.DURATION_A), (P.SKEW_C, P.DEADLINE_C, P.DURATION_C)):
            self.assertTrue(0 <= skew <= deadline < duration)


if __name__ == "__main__":
    unittest.main()
