"""Checks of campaign 2 that need no simulator: the plan against PREDICTION.md and against the launch kit, the
prediction step on the development measures of phase 1 of campaign 1 relabelled as the ports of a ring, the words
and counts of the analysis, and the rehearsal on the frozen files."""
import hashlib
import itertools
import json
import math
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
import ring

TEXT = (HERE / "PREDICTION.md").read_text()
FLAT = " ".join(TEXT.split())
ALL = [i["seed"] for i in plan.instances()]
RELABEL = dict(a1="a1", b1="b1", c1="b2", a2="a2")         # phase 1 port -> ring port, for the tests only


def relabelled():
    M = json.loads((ROOT / "research" / "network-circuit" / "phase1" / "MEASURES.json").read_text())["instances"]
    return {s: dict(scans={p: I["scans"][q] for p, q in RELABEL.items()}, quiet_train=dict(ports={p: I["quiet_train"]["ports"][q] for p, q in RELABEL.items()}))
            for s, I in M.items()}


class Protocol(unittest.TestCase):
    def test_prediction_is_the_file_pushed_alone(self):
        self.assertEqual(hashlib.sha256(TEXT.encode()).hexdigest(), "cc16b94e6aa4eca8f065724db3d7a32a3640c90e4eaaf4c73fe250e9ea6208e7")

    def test_constants_of_the_text(self):
        self.assertIn("seeds **7301, 7302, 7303** (machine `a`) and **7304, 7305, 7306** (machine `b`)", FLAT)
        self.assertEqual(plan.SEEDS, dict(a=[7301, 7302, 7303], b=[7304, 7305, 7306]))
        self.assertEqual((plan.N, plan.PORTS, plan.UNUSED, plan.SECTION), (3, ["a1", "b1", "c1", "a2"], ["b2", "c2"], "tt_mm"))
        self.assertIn("Measures: a scan 410 s, the train 730 s.", FLAT)
        self.assertEqual(plan.TIMEOUT_S, dict(scan=410, train=730))
        self.assertIn("expected = 3 x (3.7746 s x simulated ms + 3.9820 s x pulses) x (1.3861 if the run has noise) limit = 1.3 x expected, rounded up to 10 s", FLAT)
        self.assertEqual(plan.COST, dict(per_cell_ms_s=3.7746, per_cell_pulse_s=3.9820, noise=1.3861, margin=1.3))
        self.assertIn("`L = S_3 + 10` for its run without noise and for the control; `L' = S_3 + 3` for its noisy runs", FLAT)
        self.assertEqual((plan.AFTER_QUIET, plan.AFTER_NOISY, plan.NOISY_RUNS, plan.READS, plan.GUARD, plan.JOBS), (10, 3, 3, 10, 16, 4))
        self.assertIn("0.090 mV between runs, 0.064 mV within a run, 0.009 mV per dose", FLAT)
        self.assertEqual(predicted.FIXED_NOISE_MV, dict(between_runs=0.090, within_run=0.064, dose=0.009))
        self.assertIn("noise = sqrt(0.064^2 + 0.090^2 + need x 0.009^2) hi = + max(0, the three helps) + 3 x noise + half bracket lo = - (0.015 + 3 x noise + half bracket)", FLAT)
        self.assertIn("hi = + max(0, help at 16, help at 18 after a silence, help at 18 after a FIRE) + 0.030 + half bracket lo = - (0.015 + 0.030 + half bracket)", FLAT)
        self.assertEqual((predicted.ALLOWANCE_MV, predicted.K, predicted.HELP_22_MV, predicted.D), (0.030, 3.0, 0.015, 100000))
        self.assertIn("The **need** of a port is the least `n >= 0` with `n x 100 000 >= gap`.", FLAT)
        self.assertEqual((analyze.TOLERANCE_MV, analyze.SEPARATION), (0.01, 16))
        self.assertIn("5 110 s for the measures, 14 090 s for the network runs, 19 200 s in all", FLAT)

    def test_frozen_files_exist(self):
        for name in plan.FROZEN:
            self.assertTrue((ROOT / name).is_file(), name)
        self.assertIn(f"name: {plan.WORKFLOWS[0]}\n", (ROOT / ".github" / "workflows" / "network-circuit-ring-campaign.yml").read_text())
        self.assertEqual(launch.EXECUTOR, plan.EXECUTOR)
        self.assertEqual(launch.MAX_BUDGET_S, plan.MAX_BUDGET_S)
        self.assertEqual(launch.CLEANUP_ALLOWANCE_S, plan.CLEANUP_S)


class Plan(unittest.TestCase):
    def test_measure_runs(self):
        runs = plan.measure_runs()
        self.assertEqual(len(runs), 30)
        for machine in ("a", "b"):
            mine = [r for r in runs if r["machine"] == machine]
            self.assertEqual([r["kind"] for r in mine], ["scan"] * 12 + ["train"] * 3)
            self.assertEqual([r.get("port") for r in mine[:4]], ["a1", "b1", "c1", "a2"])
            self.assertEqual({r["seed"] for r in mine}, set(plan.SEEDS[machine]))
            self.assertTrue(all(r["noise"] == 0 for r in mine))
        self.assertEqual(len({r["id"] for r in runs}), 30)

    def test_laps(self):
        self.assertEqual(plan.laps([4, 3, 5, 6]), (28, 21))

    def test_network_runs_order(self):
        needs = {s: [4, 4, 5, 4] for s in ALL}
        runs, removed = plan.network_runs(needs, 7305)
        self.assertEqual(removed, [])
        a = [r["id"] for r in runs if r["machine"] == "a"]
        self.assertEqual(a, ["a-7301-ring-quiet", "a-7302-ring-quiet", "a-7303-ring-quiet"] +
                         [f"a-{s}-ring-noisy{k}" for k in (1, 2, 3) for s in (7301, 7302, 7303)])
        self.assertEqual([r["scenario"] for r in runs if r["machine"] == "b"], ["quiet"] * 3 + ["control"] + ["noisy"] * 9)
        control = next(r for r in runs if r["scenario"] == "control")
        self.assertEqual((control["seed"], control["calendar"], control["guard"], control["noise"], control["laps"]), (7305, "control", 0, 0, 27))
        for r in runs:
            if r["scenario"] != "control":
                self.assertEqual((r["calendar"], r["guard"], r["laps"]), ("ring", 16, 27 if r["scenario"] == "quiet" else 20))
                self.assertEqual(r["noise"], int(r["scenario"] == "noisy"))
        self.assertEqual([r["seed"] for r in plan.network_runs({7301: [4] * 4, 7306: [4] * 4}, None)[0]], [7301] * 4 + [7306] * 4)

    def test_cost_model_and_limits(self):
        r = plan.network_run("a", 1, "quiet", [4, 4, 4, 4])
        self.assertEqual((r["laps"], r["pulses"]), (26, 80))
        self.assertAlmostEqual(r["expected_s"], 1172, delta=2)               # the rehearsal of phase 0 on the nominal cell: 1 172 s
        self.assertEqual((r["estimate_s"], r["timeout_s"]), (plan.ceil10(r["expected_s"]), plan.ceil10(1.3 * r["expected_s"])))
        n = plan.network_run("a", 1, "noisy", [4, 4, 4, 4], 1)
        self.assertEqual((n["id"], n["laps"], n["pulses"], n["noise"]), ("a-1-ring-noisy1", 19, 52, 1))
        self.assertAlmostEqual(n["expected_s"], 3 * (3.7746 * ring.ring(3, 19)["horizon"] * 0.02 + 3.9820 * 52) * 1.3861, delta=0.1)

    def test_budget_at_five_doses_per_port(self):
        m = launch.check_budget([plan.entry(r, "measure") for r in plan.measure_runs()], 14400, plan.JOBS)
        self.assertEqual(m["wall_cap_s"], dict(a=2555.0, b=2555.0))
        runs, removed = plan.network_runs({s: [5] * 4 for s in ALL}, 7301)
        self.assertEqual(removed, [])
        r = launch.check_budget([plan.entry(x, "network") for x in runs], plan.MAX_BUDGET_S, plan.JOBS)
        self.assertEqual(round(r["aggregate_cap_s"]), 14090)
        self.assertEqual(round(m["aggregate_cap_s"] + r["aggregate_cap_s"]), 19200)

    def test_noisy_runs_removed_for_the_budget(self):
        needs = {s: [8] * 4 for s in ALL}
        runs, removed = plan.network_runs(needs, 7304)
        self.assertTrue(removed)
        self.assertLessEqual(sum(plan.caps(runs).values()), plan.MAX_BUDGET_S)
        self.assertTrue(all(r["scenario"] == "noisy" for r in removed))
        self.assertEqual(sum(r["scenario"] in ("quiet", "control") for r in runs), 7)
        for machine in ("a", "b"):                                            # what is removed is a tail of the noisy runs of a machine
            mine = [r["id"] for r in runs if r["machine"] == machine and r["scenario"] == "noisy"]
            gone = [r["id"] for r in removed if r["machine"] == machine]
            full = [f"{machine}-{s}-ring-noisy{k}" for k in (1, 2, 3) for s in plan.SEEDS[machine]]
            self.assertEqual(mine + gone[::-1], full)

    def test_entries_are_what_the_kit_accepts(self):
        runs, _ = plan.network_runs({s: [4, 5, 3, 4] for s in ALL}, 7302)
        for stage, rs in (("measure", plan.measure_runs()), ("network", runs)):
            entries = [plan.entry(r, stage) for r in rs]
            launch.round_robin(entries, [stage])
            launch.check_budget(entries, math.ceil(sum(plan.caps(entries).values())), plan.JOBS)
            for e in entries:
                self.assertIsNotNone(re.fullmatch("[a-zA-Z0-9_-]+", e["id"]))
                self.assertEqual(e["argv"][:2], ["{python}", "{repo}/research/network-circuit-ring-campaign/run.py"])
                self.assertIn(e["noise_fingerprint"], e["required_outputs"])
                self.assertGreaterEqual(e["timeout_s"], e["estimate_s"])
        for stage in plan.STAGES.values():
            self.assertIsNotNone(re.fullmatch(r"[a-z0-9][a-z0-9-]{2,63}", stage["campaign_id"]))


class Predicted(unittest.TestCase):
    def setUp(self):
        self.I, self.measured, self.eligible, self.control = predicted.predictions(relabelled(), {}, [7101, 7102, 7103])

    def test_eligibility_and_control(self):
        self.assertEqual((self.measured, self.eligible, self.control), (["7101", "7102", "7103"], ["7101", "7103"], "7103"))
        I = self.I["7103"]
        self.assertEqual(I["need"], dict(a1=3, b1=3, c1=4, a2=5))
        self.assertEqual(I["laps"], dict(quiet=25, noisy=18))
        self.assertEqual(I["zero_error_words"]["quiet"], dict(a1="sss" + "F" * 22, b1="sss" + "F" * 19, c1="ssss" + "F" * 15, a2="sssss" + "F" * 10))
        self.assertEqual(I["zero_error_words"]["noisy"]["a2"], "sssss" + "FFF")
        self.assertEqual(I["freeze_lap"], 15)

    def test_budgets(self):
        for seed in self.measured:
            I = self.I[seed]
            for p in plan.PORTS:
                c, need = I["constants"][p], I["need"][p]
                helps = max(0.0, c["help_16_mV"], c["help_18_after_silent_mV"], c["help_18_after_fire_mV"])
                noise = math.sqrt(0.064 ** 2 + 0.090 ** 2 + need * 0.009 ** 2)
                for name, spread in (("noise_free", 0.030 + c["bracket_half_mV"]), ("noisy_k3", 3 * noise + c["bracket_half_mV"])):
                    B = I["budgets"][name]
                    lo, hi = -(0.015 + spread), helps + spread
                    self.assertEqual(B["budget_mV"][p], [lo, hi])
                    unit = c["dose_mV"] / 100000
                    self.assertTrue(B["lo"][p] * unit <= lo < (B["lo"][p] + 1) * unit)
                    self.assertTrue((B["hi"][p] - 1) * unit < hi <= B["hi"][p] * unit)
                    self.assertEqual(B["own_room"][p], predicted.own(I["gap"][p], B["lo"][p], B["hi"][p], need))

    def test_need_and_own(self):
        self.assertEqual([predicted.need_of(g) for g in (-5, 0, 1, 100000, 100001, 359378)], [0, 0, 1, 1, 2, 4])
        for gap, lo, hi in itertools.product((-30000, 0, 99999, 100000, 359378, 400000), (0, -20000, -80000), (0, 26000, 80000)):
            need = predicted.need_of(gap)
            reads = [(-gap + 100000 * w, False) for w in range(need)] + [(-gap + 100000 * need, True)]
            brute = all((s < 0 and s + hi < 0) if not f else (s >= 0 and s + lo >= 0) for s, f in reads)
            self.assertEqual(predicted.own(gap, lo, hi, need), brute)
        self.assertTrue(predicted.own(359378, -23000, 26000, 4))              # nominal_own of RingNetwork.lean

    def test_lean_text(self):
        text = predicted.lean(self.I, self.measured)
        self.assertEqual(len(re.findall(r"^example : (¬ )?Own \(N := 3\)", text, re.M)), 8 * len(self.measured))
        self.assertNotRegex(text, r"\b(sorry|admit|native_decide|axiom)\b")
        self.assertIn("example : ¬ Own (N := 3) gap7102 100000 lo7102k0 hi7102k0 3 4 := by decide +kernel", text)

    def test_missing_runs_and_broken_measures(self):
        M = relabelled()
        del M["7102"]
        M["7103"]["scans"]["a1"]["pulses"] = M["7103"]["scans"]["a1"]["pulses"][:3]
        I, measured, eligible, control = predicted.predictions(M, {"7102": {"x": "time-limit-never-rerun"}}, [7101, 7102, 7103])
        self.assertEqual((measured, eligible, control), (["7101"], ["7101"], "7101"))
        self.assertIn("missing_runs", I["7102"]["why"])
        self.assertIn("constants", I["7103"]["why"])
        self.assertEqual(predicted.predictions({}, {"1": {}, "2": {}}, [1, 2])[1:], ([], [], None))


class Trace:
    def __init__(self, protected, fires, writes):
        self.protected, self.fires, self.writes = protected, fires, writes

    def at(self, name, t):
        return 1.8 if self.protected else 0.0

    def crossings(self, name, lo, hi):
        return [lo] * (self.fires if name.endswith(".p)") else self.writes)


class Analysis(unittest.TestCase):
    def test_letters(self):
        o = dict(cell="a", port=1, date_s=1e-3, delivered=True)
        self.assertEqual(analyze.letter(Trace(False, 0, 1), o), "s")
        self.assertEqual(analyze.letter(Trace(False, 1, 0), o), "F")
        self.assertEqual(analyze.letter(Trace(False, 1, 1), o), "?")
        self.assertEqual(analyze.letter(Trace(False, 0, 0), o), "?")
        self.assertEqual(analyze.letter(Trace(True, 0, 1), o), "-")
        self.assertEqual(analyze.letter(Trace(False, 0, 1), dict(o, delivered=False)), "x")
        self.assertEqual(analyze.letter(Trace(False, 0, 1), dict(o, delivered=False, refused="protected")), "r")

    def test_n_own(self):
        self.assertIsNone(analyze.n_own("sss", 4))
        self.assertTrue(analyze.n_own("ssss", 4))
        self.assertTrue(analyze.n_own("ssssFFF", 4))
        self.assertTrue(analyze.n_own("FFF", 0))
        self.assertFalse(analyze.n_own("sssFFF", 4))
        self.assertFalse(analyze.n_own("sssssFF", 4))
        self.assertFalse(analyze.n_own("ssss-FF", 4))

    def test_laps_of_a_pulse(self):
        at = lambda units: analyze.router.ORIGIN + units * analyze.net.TU
        self.assertEqual([analyze.lap(at(d), 37) for d in (0, 20.3, 36.9, 37, 74.02)], [1, 1, 1, 2, 3])

    def test_verdicts(self):
        self.assertEqual(analyze.verdict([], bool), "not established")
        self.assertEqual(analyze.verdict([True, True], bool), "holds")
        self.assertEqual(analyze.verdict([True, False], bool), "fails")


class Rehearsal(unittest.TestCase):
    def test_rehearsal_was_made_on_the_frozen_files(self):
        r = json.loads((HERE / "REHEARSAL.json").read_text())
        self.assertTrue(r["all_checks_passed"] and r["second_launch_refused_at_each_stage"] and r["no_link_in_the_evidence"])
        self.assertEqual(r["files"], {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in plan.FROZEN})
        self.assertEqual(r["lean_check"], "Predicted.lean: checked")
        self.assertEqual(len({c for c in r["claims"] if "owner-launch" in c}), 4)
        for run, wall in r["wall_s"].items():
            self.assertLess(wall, r["limits_s"][run], run)


if __name__ == "__main__":
    unittest.main()
