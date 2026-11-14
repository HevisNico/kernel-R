"""Checks of the campaign that need no simulator: the plan against PREDICTION.md and against the launch kit, the
prediction step on the development measures of phase 1, the words of the analysis."""
import hashlib
import json
from pathlib import Path
import re
import sys
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "research" / "sky130-supervisor-closure" / "launchkit"))
import analyze
import launch
import plan
import predicted

TEXT = (HERE / "PREDICTION.md").read_text()
ALL = [i["seed"] for i in plan.instances()]


class Protocol(unittest.TestCase):
    def test_prediction_is_the_file_pushed_alone(self):
        self.assertEqual(hashlib.sha256(TEXT.encode()).hexdigest(), "9b410542a66bc0873ba338aa4b788a1aa9d8e5ae9e216b1f6d20e190274056f9")

    def test_constants_of_the_text(self):
        self.assertIn("seeds **7201, 7202, 7203** (measured on machine `a`) and\n**7204, 7205, 7206** (machine `b`)", TEXT)
        self.assertEqual(plan.SEEDS, dict(a=[7201, 7202, 7203], b=[7204, 7205, 7206]))
        self.assertIn("| scan of one port | 198 to 296 | 375 | 12 |", TEXT)
        self.assertIn("| train of 10 reads, noise | 545 to 556 | 700 | 9 |", TEXT)
        self.assertIn("| network run, 18 units, noise | 678 to 686 (nominal cell) | 860 | 6 |", TEXT)
        self.assertEqual((plan.TIMEOUT_S, plan.READS, plan.NOISY_TRAINS, plan.NOISY_RUNS, plan.GUARD, plan.SECTION, plan.JOBS),
                         (dict(scan=375, train=700, network=860), 10, 3, 2, 16, "tt_mm", 4))
        self.assertIn("+ 0.030 + half bracket", TEXT)
        self.assertEqual((predicted.ALLOWANCE_MV, predicted.K, predicted.HELP_22_MV), (0.030, 3.0, 0.015))
        self.assertEqual((analyze.TOLERANCE_MV, analyze.SEPARATION), (0.01, 16))

    def test_frozen_files_exist(self):
        for name in plan.FROZEN:
            self.assertTrue((ROOT / name).is_file(), name)
        self.assertIn(plan.WORKFLOWS[0], (ROOT / ".github" / "workflows" / "network-circuit-campaign.yml").read_text())


class Plan(unittest.TestCase):
    def test_measure_runs(self):
        runs = plan.measure_runs()
        self.assertEqual(len(runs), 48)
        for machine in ("a", "b"):
            mine = [r for r in runs if r["machine"] == machine]
            self.assertEqual([r["kind"] + str(r["noise"]) for r in mine], ["scan0"] * 12 + ["train0"] * 3 + ["train1"] * 9)
            self.assertEqual({r["seed"] for r in mine}, set(plan.SEEDS[machine]))
        self.assertEqual(len({r["id"] for r in runs}), 48)

    def test_network_runs(self):
        runs = plan.network_runs(ALL, 7205)
        self.assertEqual([r["scenario"] for r in runs if r["machine"] == "a"], ["quiet"] * 3 + ["noisy"] * 6)
        self.assertEqual([r["scenario"] for r in runs if r["machine"] == "b"], ["quiet"] * 3 + ["control"] + ["noisy"] * 6)
        control = next(r for r in runs if r["scenario"] == "control")
        self.assertEqual((control["seed"], control["spacing"], control["guard"], control["noise"]), (7205, 8, 0, 0))
        self.assertTrue(all((r["spacing"], r["guard"]) == (18, 16) for r in runs if r["scenario"] != "control"))
        self.assertEqual([r["seed"] for r in plan.network_runs([7201, 7206], None)], [7201, 7201, 7201, 7206, 7206, 7206])

    def test_budget_of_the_launch_kit(self):
        m = launch.check_budget([plan.entry(r, "measure") for r in plan.measure_runs()], plan.BUDGET_S["measures"], plan.JOBS)
        self.assertEqual(m["wall_cap_s"], dict(a=3995.0, b=3995.0))
        worst = 0
        for control in ALL:
            r = launch.check_budget([plan.entry(x, "network") for x in plan.network_runs(ALL, control)], plan.BUDGET_S["runs"], plan.JOBS)
            self.assertEqual(sorted(r["wall_cap_s"].values()), [2827.5, 3045.0])
            worst = max(worst, r["aggregate_cap_s"])
        self.assertEqual(m["aggregate_cap_s"] + worst, 13862.5)
        self.assertIn("at most 13 862.5 s", TEXT)
        self.assertLessEqual(sum(plan.BUDGET_S.values()), launch.MAX_BUDGET_S)

    def test_entries_are_what_the_kit_accepts(self):
        for stage, runs in (("measure", plan.measure_runs()), ("network", plan.network_runs(ALL, 7201))):
            entries = [plan.entry(r, stage) for r in runs]
            launch.round_robin(entries, [stage])
            for e in entries:
                self.assertIsNotNone(re.fullmatch("[a-zA-Z0-9_-]+", e["id"]))
                self.assertEqual(e["argv"][:2], ["{python}", "{repo}/research/network-circuit-campaign/run.py"])
                self.assertIn(e["noise_fingerprint"], e["required_outputs"])
                self.assertGreaterEqual(e["timeout_s"], e["estimate_s"])
        self.assertEqual(launch.EXECUTOR, plan.EXECUTOR)


class Predicted(unittest.TestCase):
    """The prediction step on the development instances of phase 1, whose measures have the same format."""

    def setUp(self):
        M = json.loads((ROOT / "research" / "network-circuit" / "phase1" / "MEASURES.json").read_text())["instances"]
        self.C, self.I, self.measured, self.eligible, self.control = predicted.predictions(M, {}, [7101, 7102, 7103])

    def test_eligibility_and_control(self):
        self.assertEqual((self.measured, self.eligible, self.control), (["7101", "7102", "7103"], ["7101", "7103"], "7101"))
        self.assertFalse(any(self.I[s]["full_room_at_k3"] for s in self.measured))
        self.assertEqual(self.I["7103"]["zero_error_words"], dict(a1="sss" + "F" * 15, a2="sssss" + "F" * 5, b1="sss" + "F" * 7, b2="ssss" + "F" * 14))

    def test_noise_free_budget(self):
        p, q = self.C["7103"]["ports"]["a1"], self.I["7103"]["noise_free"]["ports"]["a1"]
        hi = max(0.0, p["help_16_mV"], p["help_18_after_silent_mV"], p["help_18_after_fire_mV"]) + 0.030 + p["bracket_half_mV"]
        lo = -(0.015 + 0.030 + p["bracket_half_mV"])
        self.assertAlmostEqual(q["budget_mV"][1], hi, delta=p["dose_mV"] / 100000)
        self.assertAlmostEqual(q["budget_mV"][0], lo, delta=p["dose_mV"] / 100000)
        self.assertGreaterEqual(q["budget_mV"][1], hi)
        self.assertLessEqual(q["budget_mV"][0], lo)

    def test_missing_runs_and_broken_measures(self):
        M = json.loads((ROOT / "research" / "network-circuit" / "phase1" / "MEASURES.json").read_text())["instances"]
        del M["7102"]
        M["7103"]["scans"]["a1"]["pulses"] = M["7103"]["scans"]["a1"]["pulses"][:3]
        C, I, measured, eligible, control = predicted.predictions(M, {"7102": {"x": "time-limit-never-rerun"}}, [7101, 7102, 7103])
        self.assertEqual((measured, eligible, control), (["7101"], ["7101"], "7101"))
        self.assertIn("missing_runs", I["7102"]["why"])
        self.assertIn("constants", I["7103"]["why"])
        self.assertEqual(predicted.predictions({}, {"1": {}, "2": {}}, [1, 2])[2:], ([], [], None))


class Trace:
    def __init__(self, protected, fires, writes):
        self.protected, self.fires, self.writes = protected, fires, writes

    def at(self, name, t):
        return 1.8 if self.protected else 0.0

    def crossings(self, name, lo, hi):
        return [lo] * (self.fires if name.endswith(".p)") else self.writes)


class Words(unittest.TestCase):
    def test_letters(self):
        o = dict(cell="a", port=1, date_s=1e-3, delivered=True)
        self.assertEqual(analyze.letter(Trace(False, 0, 1), o), "s")
        self.assertEqual(analyze.letter(Trace(False, 1, 0), o), "F")
        self.assertEqual(analyze.letter(Trace(False, 1, 1), o), "?")
        self.assertEqual(analyze.letter(Trace(False, 0, 0), o), "?")
        self.assertEqual(analyze.letter(Trace(False, 0, 2), o), "?")
        self.assertEqual(analyze.letter(Trace(True, 0, 1), o), "-")
        self.assertEqual(analyze.letter(Trace(False, 0, 1), dict(o, delivered=False)), "x")
        self.assertEqual(analyze.letter(Trace(False, 0, 1), dict(o, delivered=False, refused="protected")), "r")


if __name__ == "__main__":
    unittest.main()
