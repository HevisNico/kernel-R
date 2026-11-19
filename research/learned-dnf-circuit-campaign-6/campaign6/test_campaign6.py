"""Tests of campaign 6's code (PREDICTION.md, df1a3cb) without a simulator and without any run of the campaign.

  python -B -m unittest test_campaign6        (from this folder, with the pinned venv)
"""
import difflib
from fractions import Fraction as F
import inspect
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c6                                               # noqa: E402
import c4                                               # noqa: E402
import analyze6                                         # noqa: E402
import inputs6                                          # noqa: E402
import meas6                                            # noqa: E402
import net6                                             # noqa: E402
import predicted6                                       # noqa: E402
import stages6                                          # noqa: E402
import batch6                                           # noqa: E402
import predict6                                         # noqa: E402
import scan6                                            # noqa: E402


def kit_folder(d, rid):
    """A run folder the kit has started: its STATE.json above it, as inside_kit reads it."""
    d = Path(d)
    (d / "STATE.json").write_text(json.dumps(dict(status="running", records=[dict(id=rid, status="started")])))
    return d / rid


def stage_file(d, stage):
    """A stage file as stages6 writes it (safeguard i)."""
    f = Path(d) / f"STAGE_{stage}.md"
    f.write_text(stages6.stage_file_text(stage))
    return f


def diff(a, b):
    return [x for x in difflib.unified_diff(inspect.getsource(a).splitlines(), inspect.getsource(b).splitlines(), lineterm="", n=0)
            if x[:1] in "+-" and not x.startswith(("+++", "---"))]


class Guard(unittest.TestCase):
    def test_seeds_and_machines(self):
        self.assertEqual(c6.SEEDS, (7801, 7802, 7803, 7804, 7805))
        self.assertEqual([s for s in c6.SEEDS if c6.MACHINE_OF[s] == "a"], [7801, 7802, 7803])
        self.assertEqual(c6.DELTA, F(1, 2))
        self.assertEqual([c6.noise_seed(7801, n) for n in (1, 2, 3)], [78011, 78012, 78013])
        self.assertEqual((c6.noise_seed(7805, 3), c6.noise_seed(7701, 1), c6.noise_seed(7706, 1)), (78053, 77011, 77061))
        with self.assertRaises(AssertionError):
            c6.noise_seed(7701, 2)

    def test_refusals(self):
        with tempfile.TemporaryDirectory() as d:
            out = kit_folder(d, "a-7801-cal-on")
            self.assertEqual(c6.guard_seed("7801", "M1", out), 7801)
            self.assertEqual(c6.guard_seed("7701", "RN", out), 7701)
            self.assertIsNone(c6.guard_seed("none", "RM1", out))
            self.assertIsNone(c6.guard_seed("none"))
            for text, stage in (("7800", "M1"), ("7806", "M1"), ("7710", "M1"), ("7601", "Q"), ("7701", "M1"), ("7701", "Q"),
                                ("7706", "RM1"), ("7801", "RN"), ("7801", "RM2"), ("7801", None), ("none", "M1"), ("none", "RN"),
                                ("7801", "M4")):
                with self.assertRaises(AssertionError, msg=(text, stage)):
                    c6.guard_seed(text, stage, out)
        with tempfile.TemporaryDirectory() as d:                                  # outside a launch of the kit
            with self.assertRaises(AssertionError):
                c6.guard_seed("7801", "M1", Path(d) / "x")

    def test_runners_refuse_before_any_simulation(self):
        """A seed outside c6's set is refused before batch6.cal, scan6's Driver or session4.play is reached."""
        boom = mock.Mock(side_effect=RuntimeError("a simulation started"))
        with tempfile.TemporaryDirectory() as d, mock.patch.object(batch6, "cal", boom), mock.patch.object(meas6, "Driver", boom), \
                mock.patch.object(net6.session4, "play", boom):
            out = kit_folder(d, "x")
            m1, m2, q, rn = (str(stage_file(d, s)) for s in ("M1", "M2", "Q", "RN"))
            for call in (lambda: meas6.cal(m1, out, "7710", "on", "ngspice", "pdk"),
                         lambda: meas6.cal(m1, out, "none-a", "on", "ngspice", "pdk"),
                         lambda: meas6.main(["scan", m2, str(out), "7710", "a", "pair", "inputs.json", "ngspice", "pdk"]),
                         lambda: meas6.scan_main([str(out), "7600", "a", "pair", "1/2", "0.001", "0.001", "ngspice", "pdk"], dict(stage="M2"), "7600"),
                         lambda: net6.network(q, out, "x", "7706", [4, 4, 4, 4], "skew", "none", 0, "ngspice", "pdk"),
                         lambda: net6.network(rn, out, "x", "7801", [4, 4, 4, 4], "skew", "none", 0, "ngspice", "pdk"),
                         lambda: net6.network(rn, out, "x", "7701", [4, 4, 4, 4], None, "device", 1, "ngspice", "pdk")):
                with self.assertRaises(AssertionError):
                    call()
        boom.assert_not_called()

    def test_stage_check(self):
        with tempfile.TemporaryDirectory() as d:
            st = c6.stage_check(stage_file(d, "M2"))
            self.assertEqual((st["stage"], st["governing_protocol"]["sha256"]), ("M2", c6.PROTOCOL_SHA256))
            bad = Path(d) / "STAGE_bad.md"
            bad.write_text(stages6.stage_file_text("M2").replace(c6.PROTOCOL_SHA256, "0" * 64))
            with self.assertRaises(AssertionError):
                c6.stage_check(bad)
            other = Path(d) / "STAGE_other.md"
            other.write_text(stages6.stage_file_text("M2").replace('"stage": "M2"', '"stage": "M9"'))
            with self.assertRaises(AssertionError):
                c6.stage_check(other)
            with mock.patch.object(c6, "PROTOCOL_SHA256", "1" * 64):        # the repository's file is not the one named
                with self.assertRaises(AssertionError):
                    c6.stage_check(stage_file(d, "M3"))

    def test_stage_check_amendment(self):
        """M2, M3, RM2, RM3 name amendment 1 with its SHA-256 as a second governing document; M1 does not need it."""
        with tempfile.TemporaryDirectory() as d:
            for stage in c6.AMENDED_STAGES:
                st = c6.stage_check(stage_file(d, stage))
                self.assertEqual(st["governing_amendment"]["sha256"], c6.AMENDMENT_SHA256)
            self.assertNotIn("governing_amendment", c6.stage_check(stage_file(d, "M1")))
            wrong = Path(d) / "STAGE_wrong.md"
            wrong.write_text(stages6.stage_file_text("M2").replace(c6.AMENDMENT_SHA256, "0" * 64))
            with self.assertRaises(AssertionError):
                c6.stage_check(wrong)
            missing = Path(d) / "STAGE_missing.md"
            missing.write_text(stages6.stage_file_text("M3").replace('"governing_amendment"', '"other"'))
            with self.assertRaises(AssertionError):
                c6.stage_check(missing)
            with mock.patch.object(c6, "AMENDMENT_SHA256", "1" * 64):        # the repository's file is not the one named
                with self.assertRaises(AssertionError):
                    c6.stage_check(stage_file(d, "RM2"))

    def test_header_records_the_running_machine(self):
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "STATE.json").write_text(json.dumps(dict(status="running", machine="b", records=[])))
            h = c6.run_header("7801", "a", "pair", dict(stage="M2"), Path(d) / "7801-scan-a-pair")
        self.assertEqual((h["machine"], h["instance_machine"], h["instance"]), ("b", "a", "7801"))
        self.assertEqual((c6.instance_machine("none-b"), c6.seed_text("none-b"), c6.seed_text("7804")), ("b", "none", "7804"))
        self.assertIsNone(c6.run_header("7801", None, "cal-on", dict(stage="M1"))["machine"])

    def test_batch_seeds_untouched(self):
        self.assertEqual(batch6.SEEDS, tuple(range(7701, 7711)))
        with self.assertRaises(AssertionError):
            batch6.guard_seed("7801")


class Copies(unittest.TestCase):
    def test_scan_main_is_scan6_main_but_three_lines(self):
        self.assertEqual(diff(scan6.main, meas6.scan_main), [
            "-def main(argv=None):", "+def scan_main(argv, stage, instance):",
            "-    seed = batch6.guard_seed(seed_text)", '+    seed = c6.guard_seed(seed_text, stage["stage"], out)',
            '+    (out / "noise.sha256").write_text(run4.trnoise_fingerprint(tr, c4.CELLS) + "\\n")',
            "-    rec = dict(batch6.run_header(seed, cell, kind), D_V=D,", "+    rec = dict(c6.run_header(instance, cell, kind, stage, out), D_V=D,"])

    def test_predict_batch_is_predict6s_but_seeds(self):
        self.assertEqual(diff(predict6.predict_batch, predicted6.predict_batch), [
            "-def predict_batch(batch_dir, out_dir, check=True):", "+def predict_batch(batch_dir, out_dir, seeds, machine_of, check=True):",
            "-    for seed in batch6.SEEDS:", "-        m = batch6.MACHINE_OF[seed]", "+    for seed in seeds:", "+        m = machine_of[seed]"])


class NetCopy(unittest.TestCase):
    """net6.network against run4.run's network branch, with a fake simulator: the same deck text and the same record,
    key for key, apart from id, stage, wall_s, peak_rss_MB and net6's one added key (campaign6). run4's guard and c6's
    are both bypassed here, only for the comparison; the guards are tested in Guard."""

    def fake_play(self, texts):
        import numpy as np
        net = net6.net

        def play(out, plan, text, ngspice, pdk, seed=None, guard_off=False, noise_id=None, shim=None):
            texts.append((text, seed, noise_id))
            out = Path(out)
            out.mkdir(parents=True)
            (out / "pdk").symlink_to("/nonexistent")
            for name in ("input.spice", "session.log", "trace.raw"):
                (out / name).write_text(f"{name}\n{text}\n{seed}\n{noise_id}\n")
            result = dict(horizon_s=plan["horizon"] * 1e-6, waveform_ends_s=plan["horizon"] * 1e-6 + 1, points=99)
            (out / "result.json").write_text(json.dumps(result) + "\n")
            tr = mock.Mock()
            tr.t = np.linspace(0, result["waveform_ends_s"], 3000)
            names = [v for c in c4.CELLS for v in [f"v(x{c}.nzm)"] + [f"v(x{c}.x{p}.{n})" for p in net.PORTS for n in ("nzo", "nzc")]]
            tr.v = {n: np.zeros(3000) for n in names}
            return result, tr
        return play

    def fake_shim(self, out):
        p = Path(out) / "shim.so"
        p.write_text("shim")
        return str(p), dict(path="shim.so")

    def test_network_is_run4s(self):
        import argparse
        import run4
        for control, noise, rnd in (("skew", "none", 0), ("none", "injected", 1), ("untrained", "none", 0)):
            texts = []
            with tempfile.TemporaryDirectory() as d, mock.patch.object(run4.session4, "play", self.fake_play(texts)), \
                    mock.patch.object(run4.noisemodel, "shim", self.fake_shim), mock.patch.object(run4, "guard", lambda *a, **k: None), \
                    mock.patch.object(c6, "guard_seed", lambda *a, **k: 7701), \
                    mock.patch.object(c6, "stage_check", lambda f: dict(stage="RN")):
                d = Path(d)
                args = argparse.Namespace(out=d / "run4", ngspice=Path("ngspice"), pdk=Path("pdk"), id="x", kind="network", seed="7701", instances=0,
                                          guard=None, cell=None, state=None, port="none", isolation=0, reuse_trip=0, needs="4,5,4,6", control=control,
                                          noise=noise, round=rnd, extraction=None, extraction_sha256=None, scale="1", stage=None)
                run4.run(args)
                net6.network("STAGE_RN.md", d / "net6", "x", "7701", [4, 5, 4, 6], None if control == "none" else control, noise, rnd, Path("ngspice"), Path("pdk"))
                r4, r6 = (json.loads((d / k / "record.json").read_text()) for k in ("run4", "net6"))
            self.assertEqual(texts[0], texts[1], control)
            drop = lambda r: {k: v for k, v in r.items() if k not in ("id", "stage", "wall_s", "peak_rss_MB", "campaign6")}
            self.assertEqual(drop(r4), drop(r6), control)
            self.assertEqual(list(r6)[:-1], list(r4), control)
            self.assertEqual(list(r6)[-1], "campaign6")
            self.assertEqual(r6["stage"], dict(stage="RN"))                 # safeguard (i)'s check, where run4 records its own


def instances_for(eligible):
    xs = []
    for s in c6.SEEDS:
        ok = s in eligible
        xs.append(dict(seed=s, measured=True, eligible=ok, gate_K0=ok, needs=dict(a=4, b=4, c1=4, c2=4),
                       counts_N_out=dict(a=False, b=False, c=False), learning_ports={}))
    return xs


class Stages(unittest.TestCase):
    def test_measure_stages_and_their_cost(self):
        allow = dict(instances={str(s): {} for s in c6.SEEDS})
        st = [stages6.measure_runs("M1"), stages6.measure_runs("M2", allow), stages6.measure_runs("M3", allow)]
        self.assertEqual([(sum(r["machine"] == "a" for r in x), sum(r["machine"] == "b" for r in x)) for x in st], [(6, 4), (13, 12), (5, 5)])
        self.assertEqual([r["id"] for r in st[1][:6]], ["7801-scan-a-pair", "7801-scan-b-pair", "7801-scan-c-line1", "7801-scan-c-line2",
                                                        "7801-bothfire-c", "7802-scan-a-pair"])
        self.assertEqual([r["machine"] for r in st[1][:6]], ["a", "b", "a", "b", "a", "b"])
        self.assertEqual([len(x) for x in st], [10, 25, 10])
        self.assertAlmostEqual(stages6.expected_compute(st), 7084.9, delta=0.05)
        self.assertEqual([round(stages6.stage_cap(x), 1) for x in st], [6902.5, 6987.5, 2025.0])
        for runs in st:
            stages6.kit_checks(dict(runs=[stages6.entry("M2", r, "x.json") for r in runs], scenario_order=["stage"], jobs=4,
                                    budget_s=int(stages6.stage_cap(runs)) + 1))
        self.assertEqual({r["machine"] for r in st[0] if r["instance"] in ("7801", "7802", "7803")}, {"a"})
        self.assertEqual({r["machine"] for r in st[0] if r["instance"] in ("7804", "7805")}, {"b"})

    def test_amendment_1_two_shards(self):
        """Amendment 1: only machine a's instances complete, yet M2 and M3 have runs on both machines; one instance
        alone gives both machines runs too; a stage with no run is empty; a one-machine stage is an impossible case."""
        only_a = dict(instances={str(s): ({} if c6.MACHINE_OF[s] == "a" else dict(why_not="x")) for s in c6.SEEDS})
        for stage in ("M2", "M3"):
            self.assertEqual({r["machine"] for r in stages6.measure_runs(stage, only_a)}, {"a", "b"})
        one = dict(instances={str(s): ({} if s == 7804 else dict(why_not="x")) for s in c6.SEEDS})
        self.assertEqual([r["machine"] for r in stages6.measure_runs("M3", one)], ["a", "b"])
        none = dict(instances={k: dict(why_not="x") for k in only_a["instances"]})
        self.assertEqual(stages6.measure_runs("M3", none), [])
        with mock.patch.object(stages6, "two_shard", lambda runs: [dict(r, machine="a") for r in runs]):
            with self.assertRaises(stages6.MeasureStageOneShard):
                stages6.measure_runs("M3", only_a)

    def test_two_shard_rule_every_case(self):
        """PREDICTION.md 4: the stage plan for 0 to 5 eligible instances, through the kit's own checks."""
        measures = 7084.9
        want = {0: (0, None, 0.0), 1: (2, [(1, 1), (2, 1)], 4000.0), 2: (4, [(2, 1), (1, 1), (1, 1), (1, 1)], 9869.0),
                3: (4, [(2, 2), (2, 1), (2, 1), (2, 1)], 11098.5), 4: (4, [(3, 2), (2, 2), (2, 2), (2, 2)], 12328.0),
                5: (4, [(3, 3), (3, 2), (3, 2), (3, 2)], 13557.5)}
        totals = {1: 11084.9, 2: 16953.9, 3: 18183.4, 4: 19412.9, 5: 20642.4}
        for e, (n, shape, net_e) in want.items():
            runs = predicted6.network_runs(instances_for(set(c6.SEEDS[:e])))
            st = stages6.network_stages(runs)
            self.assertEqual(len(st), n, e)
            if not n:
                continue
            self.assertEqual([(sum(r["machine"] == "a" for r in x), sum(r["machine"] == "b" for r in x)) for _, x in st], shape, e)
            self.assertEqual([name for name, _ in st], ["Q", "N"] if e == 1 else ["Q", "N1", "N2", "N3"])
            self.assertAlmostEqual(stages6.expected_compute([x for _, x in st]), net_e, places=2)
            self.assertAlmostEqual(measures + stages6.expected_compute([x for _, x in st]), totals[e], places=1)
            for name, x in st:
                stages6.kit_checks(dict(runs=[stages6.entry(name, r) for r in x], scenario_order=["stage"], jobs=4,
                                        budget_s=int(stages6.stage_cap(x)) + 1))
                self.assertLessEqual(stages6.stage_cap(x), 14400)

    def test_need7_bound(self):
        xs = instances_for(set(c6.SEEDS))
        for x in xs:
            x["needs"] = dict(a=7, b=7, c1=7, c2=7)
        st = stages6.network_stages(predicted6.network_runs(xs))
        self.assertAlmostEqual(max(stages6.stage_cap(x) for _, x in st), 11602.5, places=1)
        self.assertEqual({r["timeout_s"] for _, x in st for r in x if r["noise"] == "injected"}, {3560})
        self.assertEqual({r["timeout_s"] for _, x in st for r in x if r["scenario"] == "quiet"}, {1810})

    def test_limits(self):
        self.assertEqual({k: c6.limit(v) for k, v in c6.MEASURE_S.items()},
                         {"cal-on": 1610, "cal-off": 1300, "pair": 990, "line": 940, "bothfire": 80, "onesided": 440})
        self.assertEqual([c6.limit(x) for x in (c6.QUIET_SKEW_NEED4_S, c6.NOISY_NEED4_S, c6.UNTRAINED_S)], [1440, 2800, 270])

    def test_rehearsal(self):
        allow = dict(instances={"none-a": {}, "none-b": {}})
        rm = [stages6.measure_runs("RM1"), stages6.measure_runs("RM2", allow), stages6.measure_runs("RM3", allow)]
        self.assertAlmostEqual(stages6.expected_compute(rm), 4200.6, delta=0.05)
        preds = dict(instances=[dict(seed=7701, eligible=True, gate_K0=True, needs=dict(a=4, b=4, c1=4, c2=4)),
                                dict(seed=7706, eligible=True, gate_K0=True, needs=dict(a=4, b=4, c1=4, c2=4))])
        rn = stages6.rehearsal_network_runs(preds)
        self.assertEqual(sorted((r["id"], r["machine"]) for r in rn),
                         [("7701-n1", "a"), ("7701-quiet", "a"), ("7701-untrained", "a"), ("7706-n1", "b"), ("7706-quiet", "b")])
        self.assertAlmostEqual(stages6.expected_compute([rn]), 3192.0, places=1)
        self.assertAlmostEqual(stages6.stage_cap(rn), 7820.0, places=1)


class Network(unittest.TestCase):
    def test_runs_of_eligible_only(self):
        xs = instances_for({7802, 7804})
        xs[0]["eligible"] = True                                   # 7801: Python-eligible, but its gate failed: no runs
        runs = predicted6.network_runs(xs)
        self.assertEqual({r["seed"] for r in runs}, {7802, 7804})
        self.assertEqual([r["id"] for r in runs if r["noise"] == "none"], ["7802-quiet", "7802-untrained", "7804-quiet"])
        self.assertEqual([r["noise_seed"] for r in runs if r["noise"] != "none"], [78021, 78041, 78022, 78042, 78023, 78043])
        self.assertEqual(predicted6.network_runs(instances_for(set())), [])


class Adapter(unittest.TestCase):
    def test_eligible_mapping(self):
        p = dict(instances=[dict(seed=1, measured=True, eligible=True, gate_K0=False), dict(seed=2, measured=True, eligible=True, gate_K0=True),
                            dict(seed=3, measured=False, eligible=False)])
        q = analyze6.mapped(p)
        self.assertEqual([x["eligible"] for x in q["instances"]], [False, True, False])
        self.assertEqual([x["eligible_python"] for x in q["instances"]], [True, True, False])
        self.assertTrue(p["instances"][0]["eligible"])                # the record itself is not changed

    def test_minimum_of_two(self):
        self.assertEqual([analyze6.minimum("held", n) for n in (0, 1, 2, 5)], ["not established", analyze6.HELD_ON_ONE, "held", "held"])
        self.assertEqual([analyze6.minimum(v, 1) for v in ("refuted", "not established")], ["refuted", "not established"])
        res = dict(claims={"primary": dict(instances=[7801], verdict="held"), "N-out": {c: dict(verdict="held") for c in c4.CELLS},
                           "N-own": dict(verdict="refuted"), "N-word": dict(verdict="held")})
        counted = {"primary": [7801], "N-out:a": [7801, 7802], "N-out:b": [], "N-out:c": [7801], "N-own": [7801], "N-word": [7801, 7804]}
        out = analyze6.apply_minimum(res, counted)["claims"]
        self.assertEqual(out["primary"]["verdict"], analyze6.HELD_ON_ONE)
        self.assertEqual([out["N-out"][c]["verdict"] for c in c4.CELLS], ["held", "not established", analyze6.HELD_ON_ONE])
        self.assertEqual((out["N-own"]["verdict"], out["N-word"]["verdict"]), ("refuted", "held"))


class AdapterEnforcement(unittest.TestCase):
    def test_raw_record_not_reproduced_means_not_established(self):
        """The pushed record differs from the regenerated one only in `eligible` (a Python-eligible instance whose gate
        failed), which the mapping overwrites. The mapping keeps the original beside it, so the mapped records still
        differ; and even if analyze.main reported the record reproduced (mocked here), every claim is not established."""
        base = dict(what="w", protocol="p", constants={}, network_runs=[], instances=[dict(seed=7801, measured=True, eligible=False, gate_K0=False)])
        pushed = json.loads(json.dumps(base))
        pushed["instances"][0]["eligible"] = True                     # a Python-eligible instance whose gate failed
        self.assertEqual([x["eligible"] for x in analyze6.mapped(pushed)["instances"]], [x["eligible"] for x in analyze6.mapped(base)["instances"]])
        self.assertNotEqual(analyze6.mapped(pushed), analyze6.mapped(base))           # eligible_python keeps the difference
        held = dict(predicted_is_reproduced=True, missing=[], claims={k: dict(verdict="held", instances=[7801, 7802]) for k in ("primary", "G", "U", "S")})
        held["claims"]["N-out"] = {c: dict(verdict="held") for c in c4.CELLS}
        held["claims"]["N-own"] = held["claims"]["N-word"] = dict(verdict="held")
        with tempfile.TemporaryDirectory() as d, mock.patch.object(predicted6, "predictions", lambda *a, **k: base), \
                mock.patch.object(analyze6.analyze, "main", lambda *a, **k: json.loads(json.dumps(held))):
            f = Path(d) / "PREDICTED.json"
            f.write_text(predicted6.text(pushed))
            res = analyze6.run(d, f, d, d, d, d, check=False)
        self.assertFalse(res["predicted6_is_reproduced"])
        self.assertEqual(set(res["claims"].values()), {"not established"})

    def test_counted_instances_follow_analyze_counts(self):
        """A noisy run that analyze.py does not count (its kit record not complete) brings no instance."""
        xs = instances_for({7801, 7802})
        for x in xs:
            x["counts_N_out"] = dict(a=True, b=True, c=False)
            x["learning_ports"] = {"a1": dict(own_room=False, room_up_to=True)}
        p = dict(instances=xs, network_runs=predicted6.network_runs(xs))
        with tempfile.TemporaryDirectory() as d:
            recs = {}
            for r in p["network_runs"]:
                f = Path(d) / r["id"]
                f.mkdir()
                (f / "record.json").write_text(json.dumps(dict(reached_its_last_date=True)))
                recs[r["id"]] = dict(status="complete", folder=str(f))
            for k in (1, 2, 3):
                recs[f"7802-n{k}"]["status"] = "missing (limit)"
            res = dict(claims={"primary": dict(instances=[7801, 7802], verdict="held")})
            counted = analyze6.counted_instances(p, res, recs)
        self.assertEqual(counted["N-out:a"], [7801])
        self.assertEqual(counted["N-out:c"], [])
        self.assertEqual(counted["N-word"], [7801])
        self.assertEqual(counted["N-own"], [])
        self.assertEqual(analyze6.minimum("held", len(counted["N-out:a"])), analyze6.HELD_ON_ONE)

    def test_same_serialization_as_analyze(self):
        import inspect as ins
        import analyze
        self.assertIn('json.dumps(again, indent=1, default=str) + "\\n" == raw', ins.getsource(analyze.main))
        self.assertEqual(predicted6.text(dict(a=1)), json.dumps(dict(a=1), indent=1, default=str) + "\n")


class Inputs(unittest.TestCase):
    def test_complete(self):
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "r"
            f.mkdir()
            self.assertFalse(inputs6.complete(dict(status="complete", folder=str(f))))            # no record
            (f / "record.json").write_text(json.dumps(dict(result={})))
            self.assertTrue(inputs6.complete(dict(status="complete", folder=str(f))))             # a scan's record
            (f / "record.json").write_text(json.dumps(dict(reached_its_last_date=False)))
            self.assertFalse(inputs6.complete(dict(status="complete", folder=str(f))))
            self.assertFalse(inputs6.complete(dict(status="missing (limit)", folder=str(f))))

    def test_m3_bounds_need_both_pair_scans(self):
        with tempfile.TemporaryDirectory() as d:
            d = Path(d)
            recs = []
            for inst, consistent in (("7801", True), ("7804", False)):
                for c in ("a", "b"):
                    rid = f"{inst}-scan-{c}-pair"
                    (d / rid).mkdir()
                    res = dict(consistent=consistent or c == "a", s_star="861/256", half_bracket="1/256")
                    (d / rid / "record.json").write_text(json.dumps(dict(result=res)))
                    recs.append(dict(id=rid, status="complete"))
            (d / "STATE.json").write_text(json.dumps(dict(records=recs)))
            m2 = dict(stage="M2", instances={"7801": dict(D_V={"a": ["1", "1"], "b": ["1", "1"], "c": ["1", "1"]}),
                                             "7804": dict(D_V={"a": ["1", "1"], "b": ["1", "1"], "c": ["1", "1"]}),
                                             "7802": dict(why_not="a calibration deck did not complete")})
            out = inputs6.m3_inputs("M3", m2, [d])["instances"]
        self.assertEqual(out["7801"]["bounds"], {c: str(predict6.layer1_bounds({"a": F(861, 256), "b": F(861, 256)},
                                                                               {"a": F(1, 256), "b": F(1, 256)})[c]) for c in ("a", "b")})
        self.assertEqual(out["7804"]["why_not"], "the pair scan of b has no consistent bracket")
        self.assertEqual(out["7802"]["why_not"], "a calibration deck did not complete")
        self.assertEqual(inputs6.instances("M2"), ["7801", "7802", "7803", "7804", "7805"])
        self.assertEqual(inputs6.instances("RM3"), ["none-a", "none-b"])


class Frozen(unittest.TestCase):
    def test_frozen_list(self):
        f = stages6.frozen()
        for need in ("research/learned-dnf-circuit-campaign-6/campaign6/meas6.py", "research/learned-dnf-circuit-campaign-6/batch/scan6.py",
                     "research/sky130-supervisor-closure/launchkit/launch.py", "research/sky130-supervisor-closure/runtime/spinit",
                     "research/circuit/cell.spice", ".github/workflows/learned-dnf-circuit-campaign-6.yml"):
            self.assertIn(need, f)
        self.assertNotIn(".github/workflows/learned-dnf-circuit-campaign-5.yml", f)
        for need in stages6.C5_SMOKE + [c6.AMENDMENT, stages6.REHEARSAL_PREDICTIONS]:
            self.assertIn(need, f)
        missing = [x for x in f if not (stages6.ROOT / x).exists()]
        self.assertEqual(missing, [])


class Claims(unittest.TestCase):
    """The kit's claim key (launch.claim_ref: the protocol's SHA-256 and the machine) is distinct for every stage. The
    first rehearsal named PREDICTION.md as every stage's protocol, so RM1's claims refused RM2 (2026-11-19)."""
    STAGES = ("RM1", "RM2", "RM3", "RN", "M1", "M2", "M3", "Q", "N1", "N2", "N3", "N")
    # claim refs that exist on the remote for ever: campaign 6's first rehearsal (PREDICTION.md) and campaign 5's four
    TAKEN = ("8e7392c5654975049de3d25adf8a511105fba425fdb07b4d841a12fdc6342240",
             "05c8416189d0ef18c83e65e8b77b44c573800470ce1b740c8277b3c3e3bfa7b1",
             "223f0c6d996fd56854387874ee30299ee717058d08b0d6cd1300678c8a7ab4d8",
             "27989a36013709de4fe77e1c8baa5fbdf168c4b4662cd38fec3583af9b72cab5",
             "31bb3782c6f45ce5269c57a6ca5443c1dcf77fa8a4bf712bdce38c0de3559330")

    @staticmethod
    def launch_module(root):
        import importlib.util
        spec = importlib.util.spec_from_file_location(f"launch_{abs(hash(str(root)))}", Path(root) / stages6.CLOSURE / "launchkit/launch.py")
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod

    def refs(self):
        import hashlib
        launch = self.launch_module(stages6.ROOT)
        return {(s, x): launch.claim_ref(dict(protocol_sha256=hashlib.sha256(stages6.stage_file_text(s).encode()).hexdigest()), x)
                for s in self.STAGES for x in "ab"}

    def test_a_claim_refs_distinct(self):
        refs = self.refs()
        self.assertEqual(len(set(refs.values())), 2 * len(self.STAGES), refs)
        for s in self.STAGES:
            self.assertEqual(stages6.stage_path(s), f"{c6.BASE}/stages/STAGE_{s}.md")

    def test_b_no_taken_claim_ref(self):
        launch = self.launch_module(stages6.ROOT)
        taken = {launch.claim_ref(dict(protocol_sha256=h), x) for h in self.TAKEN for x in "ab"}
        self.assertIn("refs/heads/owner-launch/protocol-" + self.TAKEN[0] + "/a", taken)
        self.assertEqual(set(self.refs().values()) & taken, set())

    def test_c_manifest_passes_read_manifest(self):
        """In a throwaway worktree (never pushed): the stage file alone in one commit, the run list in a later one; the
        manifest passes the kit's read_manifest. The stage file and its run list in one commit is refused, and so is a run
        list that differs from the stage's runs."""
        import subprocess
        def git(repo, *a):
            return subprocess.run(["git", "-C", str(repo), *a], check=True, capture_output=True, text=True).stdout.strip()
        ident = ["-c", "user.name=test", "-c", "user.email=test@invalid"]
        with tempfile.TemporaryDirectory() as tmp:
            wt = Path(tmp) / "wt"
            git(stages6.ROOT, "worktree", "add", "-q", "--detach", str(wt), "HEAD")
            try:
                runs = stages6.stage_runs("RM1")
                (wt / stages6.STAGES_DIR).mkdir(parents=True, exist_ok=True)
                (wt / stages6.stage_path("RM1")).write_text(stages6.stage_file_text("RM1"))
                git(wt, "add", stages6.STAGES_DIR)
                git(wt, *ident, "commit", "-q", "-m", "test: stage file (never pushed)")
                proto = git(wt, "rev-parse", "HEAD")
                (wt / stages6.runs_path("RM1")).write_text(stages6.runs_text("RM1", runs))
                git(wt, "add", stages6.STAGES_DIR)
                git(wt, *ident, "commit", "-q", "-m", "test: run list (never pushed)")
                src = git(wt, "rev-parse", "HEAD")
                m = stages6.manifest("RM1", runs, src, root=wt)
                self.assertEqual((m["protocol_commit"], m["protocol_path"]), (proto, stages6.stage_path("RM1")))
                self.assertNotEqual(m["protocol_sha256"], c6.PROTOCOL_SHA256)
                self.assertIn(stages6.runs_path("RM1"), m["source_sha256"])
                path = wt / stages6.STAGES_DIR / "CAMPAIGN_RM1.json"
                path.write_text(json.dumps(m, indent=1) + "\n")
                launch = self.launch_module(wt)
                got, _, name = launch.read_manifest(wt, path)
                self.assertEqual(name, f"{stages6.STAGES_DIR}/CAMPAIGN_RM1.json")
                self.assertEqual(launch.claim_ref(got, "a"), self.refs()[("RM1", "a")])
                with self.assertRaises(AssertionError):                       # a run list that is not the stage's runs
                    stages6.manifest("RM1", runs[:2] + runs[3:], src, root=wt)
                # the stage file and the run list in one commit: refused (protocol must precede the source commit)
                git(wt, "checkout", "-q", "--detach", proto + "~1")
                (wt / stages6.STAGES_DIR).mkdir(parents=True, exist_ok=True)
                (wt / stages6.stage_path("RM1")).write_text(stages6.stage_file_text("RM1"))
                (wt / stages6.runs_path("RM1")).write_text(stages6.runs_text("RM1", runs))
                git(wt, "add", stages6.STAGES_DIR)
                git(wt, *ident, "commit", "-q", "-m", "test: both in one commit (never pushed)")
                with self.assertRaises(AssertionError):
                    stages6.manifest("RM1", runs, git(wt, "rev-parse", "HEAD"), root=wt)
            finally:
                git(stages6.ROOT, "worktree", "remove", "--force", str(wt))
                git(stages6.ROOT, "worktree", "prune")


if __name__ == "__main__":
    unittest.main()
