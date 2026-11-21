"""Tests of unary_smoke.py, with no simulation. Run:
  PYTHONPATH=FUP/dev:PREP/dev:. python -B test_unary_smoke.py REPO
REPO: a checkout holding campaign 6's code (research/learned-dnf-circuit-campaign-6-impl at ecfcd1c1)."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

REPO = sys.argv.pop(1)
import unary_smoke as U                                  # noqa: E402
U.paths(REPO)
import c4                                                # noqa: E402
import plans4                                            # noqa: E402
import scan6                                             # noqa: E402
import batch6                                            # noqa: E402


def slots(plan, reads):
    """Per read: (stage, name, gates, sources relative to the read's date)."""
    out = []
    for r in reads:
        d = r["date"]
        g = [s for (t, s) in plan["gates"] if abs(t - (d - c4.GATE_LEAD)) < 1e-9]
        src = sorted((round(t - d, 9), c, p, a) for (t, c, p, a) in plan["sources"] if d - 1e-9 <= t < d + c4.SLOT - 1e-9)
        out.append((r["stage"], r["read"], r["gated"], json.dumps(g, sort_keys=True), tuple(src)))
    return out


class Plan(unittest.TestCase):
    def setUp(self):
        self.fp, self.fr = plans4.calibration()
        self.up, self.ur = U.calibration()

    def test_frozen_slots_unchanged_in_order(self):
        frozen = slots(self.fp, self.fr)
        mine = [s for s in slots(self.up, self.ur) if s[1] != U.UNARY]
        self.assertEqual(frozen, mine)

    def test_one_unary_read_per_stage_before_the_dose(self):
        names = [r["read"] for r in self.ur]
        self.assertEqual(names.count(U.UNARY), c4.STAGES)
        for k in range(c4.STAGES):
            per = [r["read"] for r in self.ur if r["stage"] == k]
            self.assertEqual(per[-2:], [U.UNARY, "joint dose"])
            self.assertEqual(len(per), 7)

    def test_unary_slot_pulses_a1_and_b1_at_1_and_nothing_else_gated(self):
        for s in slots(self.up, self.ur):
            if s[1] == U.UNARY:
                self.assertEqual(s[4], ((0.0, "a", 1, c4.AMP_OR), (0.0, "b", 1, c4.AMP_OR)))
                self.assertTrue(s[2])
                self.assertEqual(json.loads(s[3]), [plans4.gates(())])
                self.assertTrue(all(v == 0.0 for v in plans4.gates(()).values()))

    def test_horizon_and_length(self):
        self.assertAlmostEqual(self.up["horizon"] - self.fp["horizon"], c4.STAGES * c4.SLOT)

    def test_context_restores_and_refuses_nesting(self):
        frozen = plans4.calibration
        with U.unary_plan():
            self.assertIs(plans4.calibration, U.calibration)
            with self.assertRaises(AssertionError):
                with U.unary_plan():
                    pass
        self.assertIs(plans4.calibration, frozen)

    def test_batch6_cal_takes_the_replaced_plan(self):
        """batch6.cal looks plans4.calibration up at call time (import inside the function)."""
        import inspect
        src = inspect.getsource(batch6.cal)
        self.assertIn("plan, reads = plans4.calibration()", src)
        self.assertIn("import plans4", src)


class Amplitude(unittest.TestCase):
    def test_amp_and_kinds_inside_and_after(self):
        fa, fk = scan6.amp, scan6.kinds_of
        for cell in ("a", "b"):
            with U.unary_amplitude(cell):
                self.assertEqual(scan6.amp(cell), c4.AMP_OR)
                other = "b" if cell == "a" else "a"
                self.assertEqual(scan6.amp(other), c4.AMP_AND)
                self.assertEqual(scan6.amp("c"), c4.AMP_OR)
                self.assertEqual(scan6.kinds_of(cell), ("line1",))
                self.assertEqual(scan6.kinds_of("c"), ("line1", "line2"))
            self.assertIs(scan6.amp, fa)
            self.assertIs(scan6.kinds_of, fk)
        self.assertEqual(scan6.amp("a"), c4.AMP_AND)

    def test_refuses_c_and_nesting(self):
        with self.assertRaises(AssertionError):
            with U.unary_amplitude("c"):
                pass
        with U.unary_amplitude("a"):
            with self.assertRaises(AssertionError):
                with U.unary_amplitude("b"):
                    pass

    def test_frozen_driver_pulses_at_1(self):
        """scan6.Driver.slot, frozen, on a fake session: a read of port 1 of a is pulsed at 1.0 inside the wrapper,
        at 0.49 outside."""
        class Fake:
            def __init__(self):
                self.pulses, self.now = [], 0.0
            def run(self, t, watch=()):
                self.now = t
                return t
            def set(self, *a):
                pass
            def protected(self, c):
                return False
            def pulse(self, c, p, date, amp=1):
                self.pulses.append((c, p, amp))
            def mean(self, v, lo, hi):
                return 0.0
        def drv():
            d = object.__new__(scan6.Driver)
            d.s, d.c, d.moving, d.D, d.t = Fake(), "a", (1,), {1: 2.7e-3, 2: 2.7e-3}, scan6.ORIGIN
            d.scale, d.reads, d.events, d.u = {1: 1.0, 2: 1.0}, [], [], None
            return d
        d = drv()
        with U.unary_amplitude("a"):
            d.slot("read", scan6.READS["line1"])
        self.assertEqual(d.s.pulses, [("a", 1, c4.AMP_OR)])
        d = drv()
        d.slot("read", scan6.READS["line1"])
        self.assertEqual(d.s.pulses, [("a", 1, c4.AMP_AND)])

    def test_moving_line1_is_port_1_alone(self):
        self.assertEqual(scan6.MOVING["line1"], (1,))
        self.assertEqual(scan6.READS["line1"], ((1, 0.0),))


class Guards(unittest.TestCase):
    def test_seed(self):
        self.assertEqual(U.guard_seed("8303"), 8303)
        for bad in ("8304", "none", "7701", "8303 "):
            with self.assertRaises(AssertionError):
                U.guard_seed(bad)

    def test_seed_guard_context(self):
        frozen = batch6.guard_seed
        with U.seed_guard():
            self.assertEqual(batch6.guard_seed("8303"), 8303)
            with self.assertRaises(AssertionError):
                batch6.guard_seed("8306")
        self.assertIs(batch6.guard_seed, frozen)


class Deck(unittest.TestCase):
    def test_deck_text_has_2x_and_1e5(self):
        """The deck's text as the runs get it (net.deck under the batch's two wrappers): vhi 0.7 and reltol 1e-5, and
        nothing else changed. Text only, no simulation."""
        import batch2x
        import dosedev2
        import dosedev_tol
        import net
        frozen = net.deck(cells=c4.CELLS, section=c4.SECTION, leak_per_port=True)
        seen = []
        with dosedev_tol.tolerance(), dosedev2.window(batch2x.PARAMS, seen):
            text = net.deck(cells=c4.CELLS, section=c4.SECTION, leak_per_port=True)
        self.assertEqual(seen[0]["parameters_changed"], {"vhi": {"old": "0.6", "new": "0.7"}, "reltol": {"old": "1e-4", "new": "1e-5"}})
        diff = [(x, y) for x, y in zip(frozen.splitlines(), text.splitlines()) if x != y]
        self.assertEqual(len(frozen.splitlines()), len(text.splitlines()))
        self.assertEqual(len(diff), 2, diff)


class Jobs(unittest.TestCase):
    def test_limits_are_twice_expected(self):
        self.assertEqual(U.limit_s("cal-on-unary"), 3830)
        self.assertEqual(U.limit_s("unary-scan"), 1300)
        self.assertEqual(U.limit_s("preset"), 160)

    def test_waves(self):
        with tempfile.TemporaryDirectory() as t:
            runs = Path(t) / "runs"
            w1 = U.jobs(REPO, runs, "/usr/bin/ngspice", "/pdk")
            self.assertEqual([j["id"] for j in w1], ["8303-cal-on-unary"])
            self.assertEqual(w1[0]["argv"][3], "cal")
            w2 = U.jobs(REPO, runs, "/usr/bin/ngspice", "/pdk", {"a": ("1e-3", "2e-3"), "b": ("3e-3", "4e-3")})
            self.assertEqual([j["id"] for j in w2], ["8303-unary-scan-a", "8303-preset-a", "8303-unary-scan-b", "8303-preset-b"])
            self.assertEqual(w2[0]["argv"][3:], ["scan", REPO, str(runs / "8303-unary-scan-a"), "a", "1e-3", "2e-3", "/usr/bin/ngspice", "/pdk"])
            self.assertEqual(w2[3]["argv"][3:9], ["preset", REPO, str(runs / "8303-preset-b"), "b", "3e-3", "4e-3"])

    def test_run_refuses_an_existing_folder_and_a_folder_in_the_repo(self):
        with tempfile.TemporaryDirectory() as t:
            with self.assertRaises(AssertionError):
                U.run(REPO, t, "/usr/bin/ngspice", "/pdk")
        with self.assertRaises(AssertionError):
            U.run(REPO, Path(REPO) / "x-runs", "/usr/bin/ngspice", "/pdk")

    def test_run_stops_when_w1_is_not_complete(self):
        """W1 'fails' (a fake run_wave): W2 is never started."""
        import batch2x
        calls = []
        frozen = batch2x.run_wave
        batch2x.run_wave = lambda runs, name, jobs: (calls.append(name), {j["id"]: "failed (exit 1)" for j in jobs})[1]
        try:
            with tempfile.TemporaryDirectory() as t:
                out = U.run(REPO, Path(t) / "runs", "/usr/bin/ngspice", "/pdk")
        finally:
            batch2x.run_wave = frozen
        self.assertEqual(calls, ["W1"])
        self.assertIn("stopped", out)

    def test_run_stops_when_w1_is_cut_at_its_limit(self):
        import batch2x
        calls = []
        frozen = batch2x.run_wave
        batch2x.run_wave = lambda runs, name, jobs: (calls.append(name), {j["id"]: "cut at its limit" for j in jobs})[1]
        try:
            with tempfile.TemporaryDirectory() as t:
                out = U.run(REPO, Path(t) / "runs", "/usr/bin/ngspice", "/pdk")
        finally:
            batch2x.run_wave = frozen
        self.assertEqual(calls, ["W1"])
        self.assertIn("stopped", out)


if __name__ == "__main__":
    unittest.main(verbosity=2)
