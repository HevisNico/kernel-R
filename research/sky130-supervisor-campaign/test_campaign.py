"""The plan against PREDICTION.md and the bounds, the decisions of a period, and the analysis on made-up runs. No simulation."""
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "sky130-supervisor-closure" / "launchkit"))
import analyze
import launch
import plan
import run as R

K = R.K
TEXT = (HERE / "PREDICTION.md").read_text()
BOUNDS = json.loads((R.CLOSURE / "BOUNDS_JUNCTION.json").read_text())


class PlanTests(unittest.TestCase):
    def test_counts_split_and_order_of_the_preregistration(self):
        runs = plan.runs()
        self.assertEqual(len(runs), 124)
        for machine in ("a", "b"):
            mine = [r for r in runs if r["machine"] == machine]
            self.assertEqual(len(mine), 62)
            self.assertEqual([r["scenario"] for r in mine], [plan.ORDER[i % 11] for i in range(62)])
            for n in range(63):                             # every prefix is balanced
                counts = [sum(r["scenario"] == s for r in mine[:n]) for s in plan.ORDER]
                self.assertLessEqual(max(counts) - min(counts), 1)
        self.assertEqual(sum(r["scenario"].startswith("main-") for r in runs), 94)
        for s in ("quiet", "outside", "self"):
            self.assertEqual(sum(r["scenario"] == s for r in runs), 10)
        self.assertEqual(sorted({r["config"] for r in runs if r["scenario"] == "quiet"}), sorted(analyze.QUIET_CONFIGS))
        self.assertEqual({r["config"] for r in runs if r["scenario"] == "outside"}, set(plan.MAIN))
        self.assertIn("`" + "`, `".join(plan.ORDER[:5]) + "`", TEXT.replace("\n", " "))

    def test_modes_noise_jumps_and_versions(self):
        for r in plan.runs():
            if r["scenario"].startswith("main-"):
                self.assertEqual((r["mode"], r["noise"], r["jump_S"], r["version"], r["config"]), ("supervised", 1, 3e-11, 2, r["scenario"][5:]))
            elif r["scenario"] == "quiet":
                self.assertEqual((r["mode"], r["noise"]), ("supervised", 0))
                self.assertEqual((r["jump_S"], r["version"]), (2e-11, 0) if r["config"] == "tt-40" else (3e-11, 2))
            elif r["scenario"] == "outside":
                self.assertEqual((r["mode"], r["noise"], r["jump_S"], r["version"]), ("supervised", 0, 2e-10, 2))
            else:
                self.assertEqual((r["mode"], r["noise"], r["jump_S"], r["version"]), ("self", 1, 3e-11, 2))
            self.assertNotEqual(r["config"] == "tt-40", r["version"] == 2)
            self.assertFalse(r["config"] == "tt-40" and r["noise"])
        for words in ("`3e-11 S`", "`2e-11 S`", "`2e-10 S`", "24 service periods", "62 runs", "`10000 + i`", "`20000 + i`"):
            self.assertIn(words, TEXT)

    def test_seeds(self):
        runs = plan.runs()
        free = [r["seed"] for r in runs if r["config"] not in plan.INSTANCE]
        self.assertEqual(len(free), len(set(free)))
        self.assertTrue(all(r["seed"] == r["number"] for r in runs if r["config"] not in plan.INSTANCE))
        self.assertTrue(all(r["seed"] == plan.INSTANCE[r["config"]] for r in runs if r["config"] in plan.INSTANCE))

    def test_jumps_stand_where_the_preregistration_says(self):
        self.assertEqual(R.sim.digest(R.CLOSURE / "BOUNDS_JUNCTION.json"), R.BOUNDS_SHA256)
        self.assertIn(R.BOUNDS_SHA256, TEXT)
        for config in plan.MAIN + ["tt-40"]:
            version, inside = ("0", plan.INSIDE_COLD) if config == "tt-40" else ("2", plan.INSIDE)
            for i, port in enumerate(BOUNDS["designs"][config][version]["ports"]):
                self.assertTrue(port["well_formed"] and port["holds_the_reference_leak"])
                self.assertLess(inside, port["largest_leak_S"])
                line = BOUNDS["doses"][config]["loss_line"][i]
                loss = line["own_loss_mV"][1] + line["mV_per_siemens"] * plan.OUTSIDE
                if config != "tt-40":
                    self.assertGreater(loss, 1.7 * port["bounds"]["H"] / 1e4)
        _, bounds = R.bounds_of("tt27", 2)
        self.assertTrue(all(b.well_formed() for b in bounds))
        with self.assertRaises(AssertionError):
            R.bounds_of("tt-40", 2)

    def test_budget_and_manifest_rules_of_the_kit(self):
        entries = [dict(id=r["id"], machine=r["machine"], scenario=r["scenario"], estimate_s=plan.ESTIMATE_S, timeout_s=plan.TIMEOUT_S) for r in plan.runs()]
        launch.round_robin(entries, plan.ORDER)
        budget = launch.check_budget(entries, plan.BUDGET_S, plan.JOBS)
        self.assertEqual(budget["wall_cap_s"], dict(a=7095.0, b=7095.0))
        self.assertLessEqual(budget["aggregate_cap_s"], 14400)
        self.assertEqual(plan.EXECUTOR, launch.EXECUTOR)
        self.assertEqual(len({r["id"] for r in plan.runs()}), 124)
        for name in plan.FROZEN:
            self.assertTrue((plan.ROOT / name).is_file(), name)


class RehearsalTests(unittest.TestCase):
    def test_the_rehearsal_was_run_on_these_very_files(self):
        record = json.loads((HERE / "REHEARSAL.json").read_text())
        self.assertTrue(record["all_checks_passed"])
        self.assertEqual(record["files"], {name: R.sim.digest(plan.ROOT / name) for name in plan.FROZEN})
        self.assertEqual(len(record["runs"]), 4)
        self.assertTrue(all(s["correct"] for x in record["runs"].values() if x["mode"] == "supervised" for s in x["services"]))


class DecisionTests(unittest.TestCase):
    def setUp(self):
        self.b = [K.Bounds(S=100, H=50, Dmin=400, Dmax=420, linear_capacity=10 ** 9, semantic_capacity=700, epsilon=2)] * 2

    def test_leak_changes_at_the_jump_period_only(self):
        self.assertEqual([R.leak_at(n, 3e-11, 8) for n in (None, 0, 7, 8, 23)], [R.G0, R.G0, R.G0, 3e-11, 3e-11])

    def test_self_mode_never_consults_the_kernel(self):
        carry, refused = [0, 0], [None, None]
        self.assertEqual(R.decide("self", self.b, carry, refused, [0, 5000], 3), ([K.WAIT, K.WAIT], [None, None]))
        self.assertEqual((carry, refused), ([0, 0], [None, None]))

    def test_supervised_follows_the_kernel_and_a_refusal_is_recorded_once(self):
        carry, refused = [200, 200], [None, None]
        actions, detail = R.decide("supervised", self.b, carry, refused, [200, 600], 4)
        self.assertEqual(actions, [K.MAINTENANCE, K.WAIT])
        self.assertEqual([d["answer"] for d in detail], actions)
        carry, refused = [600, 200], [None, None]           # port 1: the carry is above the report: the model is violated
        actions, detail = R.decide("supervised", self.b, carry, refused, [100, 200], 9)
        self.assertEqual((detail[0]["answer"], refused), (K.REFUSE, [9, None]))
        self.assertEqual(actions[0], K.prepare(self.b[0], 100))
        actions, detail = R.decide("supervised", self.b, carry, refused, [100, 600], 10)
        self.assertEqual((detail[0], refused, actions[1]), (None, [9, None], K.WAIT))


def made_up(run_id, scenario, config, noise=True, failed=(), refused=(None, None), entered=True, services=24):
    return dict(id=run_id, machine=run_id[0], scenario=scenario, config=config, status="complete", counts=True, measures=dict(
        id=run_id, scenario=scenario, config=config, mode="self" if scenario == "self" else "supervised", noise=noise, fingerprint=run_id, entered=entered,
        record_is_the_waveform=True, refused_at_period=list(refused), writes_not_as_commanded=0, fires_outside_reads=0, report_differs_from_waveform=0,
        enclosure_broken=[], premises_broken=[], reads_outside_floor_and_capacity=[], wall_s=1.0,
        services=[dict(period=n, read=("port1", "port2", "joint")[n % 3], correct=n not in failed, fires=1, latency=0.9, writes=[0, 0], reserve_units=[0, 0])
                  for n in range(services)]))


def campaign(**changes):
    rows = []
    for r in plan.runs():
        kind = "main" if r["scenario"].startswith("main-") else r["scenario"]
        default = dict(main={}, quiet=dict(noise=False), outside=dict(noise=False, refused=(9, 9), failed=(12,)), self=dict(failed=(19, 20)))[kind]
        rows.append(made_up(r["id"], r["scenario"], r["config"], **{**default, **changes.get(r["id"], {})}))
    return rows


class AnalysisTests(unittest.TestCase):
    def test_bounds(self):
        self.assertAlmostEqual(analyze.one_sided_bound(94), 0.0314, places=4)
        lo, hi = analyze.clopper_pearson(1, 10)
        self.assertAlmostEqual(lo, 0.00253, places=4)
        self.assertAlmostEqual(hi, 0.44502, places=4)
        self.assertEqual(analyze.clopper_pearson(0, 10)[0], 0.0)
        self.assertIn("3.1 %", TEXT)

    def test_everything_as_predicted(self):
        out = analyze.evaluate(campaign())
        for k in ("M1", "M2", "M3", "M4", "Q1", "Q2", "Q3", "Q4", "Q5", "Q6", "O1", "O2", "R1", "R2"):
            self.assertEqual(out[k]["verdict"], "holds", k)
        self.assertEqual(out["Q_on_the_nine_configurations"], "holds")
        self.assertIn("failed no service in 94 runs", out["comparison"])
        self.assertIn("20 of 240 services", out["comparison"])
        self.assertIn("holds", analyze.report(campaign(), out))

    def test_one_failed_service_fails_m2_and_is_listed(self):
        out = analyze.evaluate(campaign(**{"a00-main-tt27": dict(failed=(5,))}))
        self.assertEqual(out["M2"]["verdict"], "fails")
        self.assertEqual(out["M2"]["runs_with_a_failed_service"], ["a00-main-tt27"])
        self.assertIn("1 of 94", out["M2"]["bound"]["statement"])
        self.assertTrue(out["comparison"].startswith("Not stated"))

    def test_refusal_no_entry_and_control_timing(self):
        out = analyze.evaluate(campaign(**{"a01-main-ss27": dict(refused=(None, 14)), "b00-main-tt27": dict(entered=False, services=0),
                                           "a09-outside-tt27": dict(refused=(9, 10))}))
        self.assertEqual((out["M1"]["verdict"], out["M2"]["verdict"], out["O2"]["verdict"], out["O1"]["verdict"]), ("fails", "fails", "fails", "holds"))
        out = analyze.evaluate(campaign(**{"a09-outside-tt27": dict(refused=(9, 9), failed=(3,))}))
        self.assertEqual(out["O1"]["verdict"], "fails")

    def test_self_refresh_predictions(self):
        out = analyze.evaluate(campaign(**{"a10-self-tt27": dict(failed=())}))
        self.assertEqual((out["R1"]["verdict"], out["R2"]["verdict"]), ("fails", "holds"))

    def test_truncated_campaign_is_not_established(self):
        rows = campaign()
        for r in rows:
            if r["machine"] == "b" or r["id"] > "a40":
                r.update(counts=False, status="never started")
        out = analyze.evaluate(rows)
        self.assertEqual(out["M2"]["verdict"], "not established")
        self.assertEqual(out["O2"]["verdict"], "not established")
        self.assertEqual(out["Q_per_configuration"]["tt-40"], "not established")
        self.assertEqual(out["Q_per_configuration"]["tt27"], "holds")
        self.assertEqual(out["Q_on_the_nine_configurations"], "not established")

    def test_quiet_failure_refutes_its_configuration_only(self):
        rows = campaign()
        next(r for r in rows if r["id"] == "a19-quiet-ss27")["measures"]["premises_broken"] = [dict(period=3, port=1, action="wait", step_units=-9999)]
        out = analyze.evaluate(rows)
        self.assertEqual((out["Q6"]["verdict"], out["Q_per_configuration"]["ss27"], out["Q_per_configuration"]["tt27"]), ("fails", "fails", "holds"))
        self.assertEqual(out["Q_on_the_nine_configurations"], "fails")


if __name__ == "__main__":
    unittest.main()
