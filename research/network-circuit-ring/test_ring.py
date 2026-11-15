"""Checks of phase 0 that need no simulator: the calendar of the ring, its model against the facts proved in
`RingNetwork.lean`, the committed rehearsal against the model, and the cost table against its script."""
import itertools
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "network-circuit"))
import cost
import ring
import router


class Calendar(unittest.TestCase):
    def test_the_timing_condition_holds_by_construction_for_every_size(self):
        for n in range(2, 9):
            c = ring.ring(n, 12)
            self.assertTrue(ring.holds_by_construction(c), n)
            self.assertGreaterEqual(min(ring.separation(c).values()), 16)
            self.assertEqual(len(c["sources"]), 12)
            self.assertEqual({(cell, port) for _, cell, port in c["sources"]}, {("a", 1)})

    def test_the_campaign_size(self):
        c = ring.ring(3, 26)
        self.assertEqual((c["period"], round(c["reach"] / 3, 4)), (37, 5.6667))
        self.assertEqual(ring.ports(3), ["a1", "b1", "c1", "a2"])
        self.assertEqual([(e["source"], e["cell"], e["port"]) for e in c["edges"][26:]], [("b", "c", 1), ("c", "a", 2)])

    def test_the_root_routes_only_its_launches(self):
        c = ring.ring(3, 5)
        bands = [e["gate"] for e in c["edges"] if e["source"] == "a"]
        self.assertEqual(bands, [(37 * lap, 37 * lap + 2) for lap in range(5)])
        inside = lambda date: any(lo <= date < hi for lo, hi in bands)
        for _, k, lap, lo, hi in ring.windows(c):
            if k == 0:                                      # a launch FIRE, for every latency
                self.assertTrue(inside(lo + ring.LATENCY[0]) and inside(hi + ring.LATENCY[1]))
            if k == 3:                                      # a FIRE of the return port
                self.assertFalse(inside(lo + ring.LATENCY[0]) or inside(hi + ring.LATENCY[1]))
        self.assertTrue(all(e["cell"] != "a" or e["port"] == 2 for e in c["edges"]))

    def test_a_lap_is_over_before_the_next_launch(self):
        for n in range(2, 9):
            c = ring.ring(n, 4)
            latest = max(hi for _, k, lap, _, hi in ring.windows(c) if lap == 0 and k == n)
            self.assertGreaterEqual(c["period"] - latest, 16)
            self.assertGreaterEqual(c["period"] - latest, router.net.CYCLE / router.net.TU + 1)

    def test_the_control_is_outside_the_condition_on_the_root_only(self):
        for n in range(3, 7):
            c = ring.control(n, 12)
            sep = ring.separation(c)
            self.assertFalse(ring.holds_by_construction(c))
            self.assertLess(sep["a"], 16)
            self.assertTrue(all(v >= 16 for cell, v in sep.items() if cell != "a"))
            self.assertTrue(ring.gates_hold(c))
            arrival = c["reach"] + n * ring.CONTROL_LATENCY
            self.assertAlmostEqual(arrival, 8.0)
            self.assertGreater(arrival, ring.PROTECTED_UNTIL)

    def test_the_guard_refuses_what_the_condition_excludes(self):
        tu = router.net.TU
        self.assertIsNone(router.refusal(16, False, 0.0, 16 * tu))
        self.assertIsNotNone(router.refusal(16, False, 0.0, 15.9 * tu))
        self.assertIsNotNone(router.refusal(16, True, None, 1.0))
        self.assertIsNone(router.refusal(None, True, 0.0, tu))

    def test_the_train_reads_each_port_alone(self):
        c = ring.train(3)
        self.assertEqual(len(c["sources"]), 40)
        self.assertEqual(len({d for d, _, _ in c["sources"]}), 40)
        for cell in "abc":
            dates = sorted(d for d, x, _ in c["sources"] if x == cell)
            self.assertGreaterEqual(min(b - a for a, b in zip(dates, dates[1:])), 18)


class Model(unittest.TestCase):
    def test_closed_form_against_the_queue_of_the_lean_model(self):
        for n in (2, 3, 4):
            for needs in itertools.product(range(0, 4), repeat=n + 1):
                for laps in (0, 1, 5, 14):
                    self.assertEqual(ring.zero_error(needs, laps)["words"], ring.chain_run(list(needs), laps))

    def test_ring_words_of_the_lean_file(self):
        """`ring_words`: port k has min(need, m) silent reads then m - need FIRE, with m = arriving k."""
        needs, laps = [3, 6, 4, 5], 28
        arriving = laps
        for k, word in enumerate(ring.zero_error(needs, laps)["words"]):
            self.assertEqual(word, "s" * min(needs[k], arriving) + "F" * max(arriving - needs[k], 0))
            arriving = max(arriving - needs[k], 0)

    def test_nominal_ring_of_the_lean_file(self):
        """`nominal_ring`: four writes and laps - 4 (k + 1) FIRE on port k; frozen from lap 4 (N + 1)."""
        for n, laps in ((3, 26), (6, 38)):
            z = ring.zero_error([4] * (n + 1), laps)
            self.assertEqual([w.count("s") for w in z["words"]], [4] * (n + 1))
            self.assertEqual([w.count("F") for w in z["words"]], [laps - 4 * (k + 1) for k in range(n + 1)])
            self.assertEqual(z["freeze_lap"], 4 * (n + 1))
            self.assertEqual(z["after_the_last_write"][-1], 10)

    def test_freeze_and_laps(self):
        needs = [5, 3, 0, 6]
        self.assertEqual(ring.laps_for(needs), 24)
        z = ring.zero_error(needs, ring.laps_for(needs))
        self.assertEqual((z["freeze_lap"], z["after_the_last_write"]), (14, [19, 16, 16, 10]))
        self.assertEqual(ring.zero_error([0, 0, 2, 0], 9)["freeze_lap"], 2)


class Rehearsal(unittest.TestCase):
    R = json.loads((HERE / "REHEARSAL.json").read_text())

    def test_the_nominal_ring_gives_the_words_of_the_model(self):
        self.assertEqual(self.R["need_of_the_nominal_port"], 4)
        for name in ("ring-3-quiet", "ring-3-noise", "ring-3-control", "ring-3-control-10-units"):
            r = self.R["runs"][name]
            z = ring.zero_error([4] * 4, r["laps"])
            self.assertEqual(list(r["words"].values()), z["words"], name)
            self.assertEqual((r["freeze_lap"], r["after_the_last_write"]), (16, [22, 18, 14, 10]), name)
            self.assertTrue(r["as_the_model"] and r["reached_its_last_date"] and not r["still_queued_at_the_horizon"], name)
            self.assertEqual((r["refused"], r["undelivered"], r["on_a_protected_cell"], r["pulses_on_other_ports"]), (0, 0, 0, {}), name)
            self.assertEqual(r["root_fires_routed_nowhere"], len(z["words"][-1]) - z["words"][-1].count("s"), name)

    def test_the_run_inside_the_condition(self):
        r = self.R["runs"]["ring-3-quiet"]
        self.assertTrue(r["holds_by_construction"] and r["guard_units"] == 16)
        self.assertGreaterEqual(min(r["closest_pulses_units"].values()), 16)
        self.assertLess(r["largest_move_that_is_not_a_dose_mV"], 0.01)
        self.assertLess(r["latency_units"][1], ring.LATENCY[1])
        for p, need in zip(ring.ports(3), r["needs"]):
            self.assertAlmostEqual(r["final_u_mV"][p], r["initial_u_mV"][p] - need * sum(r["dose_mV"]) / 2, delta=0.01)

    def test_the_controls_are_outside_it(self):
        for name, near in (("ring-3-control", 8), ("ring-3-control-10-units", 10)):
            r = self.R["runs"][name]
            self.assertFalse(r["holds_by_construction"])
            self.assertIsNone(r["guard_units"])
            self.assertLess(abs(min(r["closest_pulses_units"].values()) - near), 1.2, name)


class Cost(unittest.TestCase):
    def test_the_table_is_what_the_script_gives(self):
        R = json.loads((HERE / "REHEARSAL.json").read_text())
        self.assertEqual(json.loads(json.dumps(cost.build(R))), json.loads((HERE / "COST.json").read_text()))

    def test_the_formulas(self):
        self.assertEqual(cost.kit([100, 200, 300, 400]), 1040 / 4 + 410)
        self.assertEqual(cost.greedy([100, 200, 300, 400]), 250 + 300)
        self.assertEqual(cost.limit(1001), 1310)

    def test_the_proposed_option(self):
        C = json.loads((HERE / "COST.json").read_text())
        by = {o["option"]: o for o in C["options"]}
        self.assertTrue(by["F3s"]["within_4h_expected"] and not by["F3s"]["within_4h_by_the_kit_budget"])
        self.assertLessEqual(by["F3s"]["network_stage_kit_budget_s"], 14400)
        self.assertTrue(by["F1s"]["within_4h_by_the_kit_budget"])
        self.assertFalse(by["I0"]["within_4h_by_the_kit_budget"])


if __name__ == "__main__":
    unittest.main()
