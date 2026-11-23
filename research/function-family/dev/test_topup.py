"""Tests of topup.py, with no simulation. Run:
  PYTHONPATH=FUP/dev:PREP/dev:. python -B test_topup.py REPO
REPO: a checkout of research/learned-dnf-circuit-campaign-6-impl at ecfcd1c1."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

REPO = sys.argv.pop(1)
import topup as T                                        # noqa: E402
T.paths(REPO)
import c4                                                # noqa: E402
import plans4                                            # noqa: E402
import scan6                                             # noqa: E402
import batch6                                            # noqa: E402
import batch2x                                           # noqa: E402

NG, PDK = "/usr/bin/ngspice", "/pdk"


def slots(plan, reads):
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
        self.up, self.ur = T.calibration()

    def test_frozen_slots_unchanged_in_order(self):
        self.assertEqual(slots(self.fp, self.fr), [s for s in slots(self.up, self.ur) if s[1] not in T.UNARY.values()])

    def test_two_unary_reads_per_stage_before_the_dose(self):
        for k in range(c4.STAGES):
            per = [r["read"] for r in self.ur if r["stage"] == k]
            self.assertEqual(len(per), 8)
            self.assertEqual(per[-3:], [T.UNARY[1], T.UNARY[2], "joint dose"])

    def test_unary_slots_pulse_the_right_port_of_a_and_b_at_1_gated(self):
        seen = {1: 0, 2: 0}
        for s in slots(self.up, self.ur):
            for p, name in T.UNARY.items():
                if s[1] == name:
                    seen[p] += 1
                    self.assertEqual(s[4], ((0.0, "a", p, c4.AMP_OR), (0.0, "b", p, c4.AMP_OR)))
                    self.assertTrue(s[2])
                    self.assertEqual(json.loads(s[3]), [plans4.gates(())])
        self.assertEqual(seen, {1: c4.STAGES, 2: c4.STAGES})
        self.assertTrue(all(v == 0.0 for v in plans4.gates(()).values()))

    def test_horizon(self):
        self.assertAlmostEqual(self.up["horizon"] - self.fp["horizon"], 2 * c4.STAGES * c4.SLOT)

    def test_context_restores_and_refuses_nesting(self):
        frozen = plans4.calibration
        with T.unary_plan():
            self.assertIs(plans4.calibration, T.calibration)
            with self.assertRaises(AssertionError):
                with T.unary_plan():
                    pass
        self.assertIs(plans4.calibration, frozen)

    def test_reads_with_unknown_names_are_ignored_by_the_frozen_table(self):
        """campaign 5's P.table reads only its own read names, so the doses and the frozen reads are unaffected."""
        import inspect
        import predicted as P
        self.assertIn("for name in READS + ((SKEWED,) if c == \"c\" else ())", inspect.getsource(P.table))


class Amplitude(unittest.TestCase):
    def test_inside_and_after(self):
        fa, fk = scan6.amp, scan6.kinds_of
        for cell in ("a", "b"):
            other = "b" if cell == "a" else "a"
            with T.unary_amplitude(cell):
                self.assertEqual(scan6.amp(cell), c4.AMP_OR)
                self.assertEqual(scan6.amp(other), c4.AMP_AND)
                self.assertEqual(scan6.amp("c"), c4.AMP_OR)
                self.assertEqual(scan6.kinds_of(cell), ("line1", "line2"))
                self.assertEqual(scan6.kinds_of(other), ("pair",))
            self.assertIs(scan6.amp, fa)
            self.assertIs(scan6.kinds_of, fk)

    def test_refuses_c_and_nesting(self):
        with self.assertRaises(AssertionError):
            with T.unary_amplitude("c"):
                pass
        with T.unary_amplitude("a"):
            with self.assertRaises(AssertionError):
                with T.unary_amplitude("a"):
                    pass

    def test_frozen_driver_pulses_each_port_at_1(self):
        class Fake:
            def __init__(self):
                self.pulses = []
            def run(self, t, watch=()):
                return t
            def set(self, *a):
                pass
            def protected(self, c):
                return False
            def pulse(self, c, p, date, amp=1):
                self.pulses.append((c, p, amp))
            def mean(self, v, lo, hi):
                return 0.0
        for cell, kind, port in (("a", "line1", 1), ("a", "line2", 2), ("b", "line1", 1), ("b", "line2", 2)):
            d = object.__new__(scan6.Driver)
            d.s, d.c, d.moving, d.D, d.t = Fake(), cell, scan6.MOVING[kind], {1: 2.7e-3, 2: 2.7e-3}, scan6.ORIGIN
            d.scale, d.reads, d.events, d.u = {1: 1.0, 2: 1.0}, [], [], None
            with T.unary_amplitude(cell):
                d.slot("read", scan6.READS[kind])
            self.assertEqual(d.s.pulses, [(cell, port, c4.AMP_OR)])
            self.assertEqual(scan6.MOVING[kind], (port,))


class Guards(unittest.TestCase):
    def test_seed(self):
        for s in range(8301, 8311):
            self.assertEqual(T.guard_seed(str(s)), s)
        for bad in ("8300", "8311", "none", "7701", "08303", "8303 "):
            with self.assertRaises((AssertionError, ValueError)):
                T.guard_seed(bad)

    def test_seed_guard_context(self):
        frozen = batch6.guard_seed
        with T.seed_guard():
            self.assertEqual(batch6.guard_seed("8310"), 8310)
            with self.assertRaises(AssertionError):
                batch6.guard_seed("7701")
        self.assertIs(batch6.guard_seed, frozen)


class Deck(unittest.TestCase):
    def test_deck_text_has_2x_and_1e5_only(self):
        import dosedev2
        import dosedev_tol
        import net
        for kw in (dict(), dict(leak_per_port=True)):
            frozen = net.deck(cells=c4.CELLS, section=c4.SECTION, **kw)
            seen = []
            with dosedev_tol.tolerance(), dosedev2.window(batch2x.PARAMS, seen):
                text = net.deck(cells=c4.CELLS, section=c4.SECTION, **kw)
            self.assertEqual(seen[0]["parameters_changed"], {"vhi": {"old": "0.6", "new": "0.7"}, "reltol": {"old": "1e-4", "new": "1e-5"}})
            diff = [(x, y) for x, y in zip(frozen.splitlines(), text.splitlines()) if x != y]
            self.assertEqual(len(diff), 2, diff)


class Jobs(unittest.TestCase):
    def test_limits(self):
        self.assertEqual(T.limit_s("cal-on"), 4440)
        self.assertEqual(T.limit_s("cal-off"), 3220)
        self.assertEqual(T.limit_s("unary-scan"), 1300)
        self.assertEqual(T.limit_s("preset"), 160)

    def test_waves(self):
        with tempfile.TemporaryDirectory() as t:
            runs = Path(t) / "r"
            w1 = T.wave1(REPO, runs, NG, PDK, [8301, 8302])
            self.assertEqual([j["id"] for j in w1], ["8301-cal-on-unary", "8301-cal-off-unary", "8302-cal-on-unary", "8302-cal-off-unary"])
            w2 = T.wave2(REPO, runs, NG, PDK, {8305: {"a": ("1", "2"), "b": ("3", "4")}})
            self.assertEqual([j["id"] for j in w2], ["8305-unary-scan-a1", "8305-unary-scan-a2", "8305-preset-a", "8305-unary-scan-b1", "8305-unary-scan-b2", "8305-preset-b"])
            self.assertEqual(w2[1]["argv"][3:], ["scan", REPO, str(runs / "8305-unary-scan-a2"), "8305", "a", "2", "1", "2", NG, PDK])
            self.assertEqual(w2[5]["argv"][3:9], ["preset", REPO, str(runs / "8305-preset-b"), "8305", "b", "3"])

    def test_worker_refuses(self):
        with tempfile.TemporaryDirectory() as t:
            with self.assertRaises(AssertionError):
                T.worker(REPO, t, NG, PDK, ["8301"])                     # exists
            with self.assertRaises(AssertionError):
                T.worker(REPO, Path(t) / "x", NG, PDK, [])                # empty
            with self.assertRaises(AssertionError):
                T.worker(REPO, Path(t) / "y", NG, PDK, ["8301", "8301"])  # repeated
            with self.assertRaises(AssertionError):
                T.worker(REPO, Path(t) / "z", NG, PDK, ["8311"])          # not B2's
        with self.assertRaises(AssertionError):
            T.worker(REPO, Path(REPO) / "x", NG, PDK, ["8301"])

    def _fake(self, statuses):
        calls = []
        frozen = batch2x.run_wave
        batch2x.run_wave = lambda runs, name, jobs: (calls.append((name, [j["id"] for j in jobs])), {j["id"]: statuses(j["id"]) for j in jobs})[1]
        return calls, frozen

    def test_worker_w2_only_for_complete_instances(self):
        """8302's guard-off deck fails: its W2 runs are not started; 8301's are (doses faked)."""
        calls, frozen = self._fake(lambda rid: "failed (exit 1)" if rid == "8302-cal-off-unary" else "complete")
        fd = T.doses_from_on
        T.doses_from_on = lambda repo, d: ({"a": ("1", "2"), "b": ("3", "4")}, [])
        try:
            with tempfile.TemporaryDirectory() as t:
                out = T.worker(REPO, Path(t) / "r", NG, PDK, ["8301", "8302"])
                ns = json.loads((Path(t) / "r" / "NOT_STARTED_W2.json").read_text())
        finally:
            batch2x.run_wave, T.doses_from_on = frozen, fd
        self.assertEqual([c[0] for c in calls], ["W1", "W2"])
        self.assertTrue(all(i.startswith("8301-") for i in calls[1][1]))
        self.assertEqual(len(calls[1][1]), 6)
        self.assertEqual(len(ns), 6)
        self.assertEqual(out["not_started"], 6)

    def test_worker_cut_deck_stops_its_instance(self):
        calls, frozen = self._fake(lambda rid: "cut at its limit" if rid.startswith("8301-cal-on") else "complete")
        fd = T.doses_from_on
        T.doses_from_on = lambda repo, d: ({"a": ("1", "2"), "b": ("3", "4")}, [])
        try:
            with tempfile.TemporaryDirectory() as t:
                T.worker(REPO, Path(t) / "r", NG, PDK, ["8301"])
        finally:
            batch2x.run_wave, T.doses_from_on = frozen, fd
        self.assertEqual(calls[1], ("W2", []))


class Compare(unittest.TestCase):
    def _run(self, root, wall, interp, trace=b"TRACE"):
        d = Path(root)
        (d / "evidence").mkdir(parents=True)
        (d / "evidence" / "input.spice").write_text("deck\n")
        (d / "evidence" / "trace.raw").write_bytes(trace)
        (d / "evidence" / "result.json").write_text(json.dumps(dict(occurrences=[1, 2], wall_s=wall)))
        (d / "noise.sha256").write_text("abc\n")
        (d / "record.json").write_text(json.dumps(dict(id=d.name, kind="cal", reads=[1], wall_s=wall, peak_rss_MB=wall, files={"x": wall},
                                                        batch=dict(seed=8301, interpreter=interp))))
        return d

    def test_identical_apart_from_clock_and_machine(self):
        with tempfile.TemporaryDirectory() as t:
            a = self._run(Path(t) / "8301-cal-on-unary", 1.0, "m1")
            b = self._run(Path(t) / "8301-cal-on-unary-dup", 2.0, "m2")
            self.assertTrue(T.compare(a, b)["identical"])

    def test_a_different_waveform_is_not_identical(self):
        with tempfile.TemporaryDirectory() as t:
            a = self._run(Path(t) / "x", 1.0, "m1")
            b = self._run(Path(t) / "y", 1.0, "m1", trace=b"OTHER")
            r = T.compare(a, b)
            self.assertFalse(r["identical"])
            self.assertFalse(r["fields"]["trace_raw"]["equal"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
