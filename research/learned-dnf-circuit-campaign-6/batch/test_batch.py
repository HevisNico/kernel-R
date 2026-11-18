"""Tests of the development batch's code without a simulator (BATCH_SPEC.md). The table of the tests is campaign 5's
nominal table (`cases.nominal()`, CALIBRATION.json of #172), with synthetic scans; no run of the batch is read.

  python -B -m unittest test_batch        (from this folder, with the pinned venv)
"""
from fractions import Fraction as F
import copy
import json
import subprocess
from pathlib import Path
import sys
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import batch6                                           # noqa: E402
import predict6                                         # noqa: E402
import report6                                          # noqa: E402
import scan6                                            # noqa: E402
import c4                                               # noqa: E402
import cases                                            # noqa: E402
import predicted as P                                   # noqa: E402


def nominal_scans(L=None, s_star="7/2", half="1/64"):
    L = L or {}
    out = {}
    for key in predict6.CROSSINGS:
        out[key] = dict(crossing=True, consistent=True, contradictory=False, s_star=s_star, half_bracket=half,
                        bracket=[str(F(s_star) - F(half)), str(F(s_star) + F(half))], L=L.get(key, 100000))
    return out


def ones_for(t, scans, silent=True):
    """One-sided sets run at exactly the bounds predict6 recomputes (from the pair scan's theta_x and H_x)."""
    out = {}
    for c in ("a", "b"):
        r = scans[(c, "pair")]
        theta = int(r["L"])
        t2 = {k: dict(v, Z=predict6.scale(v["Z"], theta)) for k, v in t.items() if k[0] == c}
        H = -(-F(r["half_bracket"]) * predict6.steps(t2, c)["both"] // 1)
        b = predict6.one_sided_bounds(t2, c, H)
        out[c] = dict(all_silent=silent, silent={"1": silent, "2": silent}, bounds={str(p): str(v) for p, v in b.items()})
    return out
STATUSES = {f"7701-{x}": "complete" for x in ("cal-on", "cal-off")}


class Guards(unittest.TestCase):
    def test_seeds(self):
        self.assertEqual(batch6.SEEDS, tuple(range(7701, 7711)))
        self.assertEqual([s for s in batch6.SEEDS if batch6.MACHINE_OF[s] == "a"], [7701, 7702, 7703, 7704, 7705])
        self.assertIsNone(batch6.guard_seed("none"))
        self.assertEqual(batch6.guard_seed("7710"), 7710)
        for bad in ("7700", "7711", "7601", "7692", "7801"):
            with self.assertRaises(AssertionError):
                batch6.guard_seed(bad)

    def test_limits(self):
        self.assertEqual((batch6.limit_s("cal"), batch6.limit_s("scan"), batch6.limit_s("onesided")), (2780, 2360, 750))
        self.assertEqual(batch6.DELTAS, (F(1, 4), F(1, 2)))


class Wrapper(unittest.TestCase):
    def setUp(self):
        self.t, self.dose = cases.nominal()

    def test_fire_bit_entries_replaced(self):
        bad = ["FIRE bit False and Z = 100673 disagree at ('b', 3, 'both')", "missing read ('c', 2, 'empty')"]
        with mock.patch.object(P, "load", return_value=([], [])), mock.patch.object(P, "table", return_value=({}, {}, list(bad))):
            _, _, kept = predict6.table("on", "off")
        self.assertEqual(kept, ["missing read ('c', 2, 'empty')"])

    def test_own_level_test(self):
        why, _ = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], nominal_scans(), ones_for(self.t, nominal_scans()))
        self.assertEqual(why, [])
        # a level of a's pair read above every firing pair read of the deck: the deck's FIRE bits now disagree with it
        why, _ = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], nominal_scans({("a", "pair"): 100000, ("c", "both"): 200000}), ones_for(self.t, nominal_scans()))
        self.assertTrue(any("disagree with the cell's own level" in w and "'c'" in w for w in why), why)

    def test_question_1_in_measured(self):
        why, data = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], nominal_scans(s_star="9/2"), ones_for(self.t, nominal_scans(s_star="9/2")))
        self.assertTrue(any(w.startswith("question 1: need a:") for w in why))
        self.assertEqual(data["question_1"]["a"], dict(predicted=5, observed=4, agree=False))

    def test_causes(self):
        sc = nominal_scans()
        sc[("c", "line2")] = dict(crossing=False, why="no crossing below 8")
        why, _ = predict6.measure_instance(7701, dict(STATUSES, **{"7701-scan-a-pair": "missing (limit)"}), self.t, self.dose, [], sc, ones_for(self.t, nominal_scans()))
        self.assertIn("run 7701-scan-a-pair did not complete: missing (limit)", why)
        self.assertIn("scan ('c', 'line2'): no crossing below 8", why)
        ones = ones_for(self.t, nominal_scans())
        ones["b"] = dict(ones["b"], all_silent=False)
        why, _ = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], nominal_scans(), ones)
        self.assertTrue(any(w.startswith("one-sided set of b") for w in why))

    def test_rescaling(self):
        self.assertEqual(predict6.scale(100000, 100000), 100000)
        self.assertEqual(predict6.scale(99000, 99000), 100000)
        self.assertEqual(predict6.scale(1, 200000), 0)                  # 0.5, to the even
        self.assertEqual(predict6.scale(3, 200000), 2)                  # 1.5, to the even
        _, data = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], nominal_scans({("a", "pair"): 99000}), ones_for(self.t, nominal_scans({("a", "pair"): 99000})))
        self.assertEqual(data["theta"]["a"], 99000)
        self.assertEqual(data["t2"][("a", 4, "both")]["Z"], round(F(self.t[("a", 4, "both")]["Z"]) * 100000 / 99000))
        self.assertEqual(data["t2"][("b", 4, "both")]["Z"], self.t[("b", 4, "both")]["Z"])

    def test_errors_and_room(self):
        L = {("c", "line1"): 100000, ("c", "line2"): 100040, ("c", "both"): 100020}
        why, data = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], nominal_scans(L), ones_for(self.t, nominal_scans(L)))
        self.assertEqual(why, [])
        self.assertEqual(data["S"], dict(a=0, b=0, c=40))
        for c in c4.CELLS:
            st = predict6.steps(data["t2"], c)
            want = max(-(-F(1, 64) * st[predict6.DECK_READ[k]] // 1) for (cc, k) in predict6.CROSSINGS if cc == c)
            self.assertEqual(data["H"][c], want)
        x0 = P.instance(7701, data["t2"], self.dose, [], c4.DECISION5)
        x = predict6.augmented(x0, data["H"], data["S"], data["t2"])
        for K in ("K0", "K3"):
            for c in c4.CELLS:
                for side in ("training", "testing"):
                    self.assertEqual(x["budgets"][K][c][side], x0["budgets"][K][c][side] + data["H"][c] + data["S"][c])
        z = predict6.augmented(x0, {c: 0 for c in c4.CELLS}, {c: 0 for c in c4.CELLS}, data["t2"])
        self.assertEqual((z["room"], z["eligible"], z["room_at_K3"]), (x0["room"], x0["eligible"], x0["room_at_K3"]))
        big = predict6.augmented(x0, {c: 10 ** 5 for c in c4.CELLS}, {c: 0 for c in c4.CELLS}, data["t2"])
        self.assertFalse(big["eligible"])

    def test_one_sided_bounds(self):
        t = {("a", k, f"port {p}"): dict(Z=40000 + 10000 * k) for k in range(8) for p in (1, 2)}
        self.assertEqual(predict6.one_sided_bounds(t, "a", 0), {1: F(6), 2: F(6)})
        self.assertEqual(predict6.one_sided_bounds(t, "a", 5000), {1: F(13, 2), 2: F(13, 2)})
        self.assertEqual(predict6.one_sided_bounds(t, "a", 60000), {1: F(8), 2: F(8)})


class Scan(unittest.TestCase):
    def test_majority_and_consistency(self):
        reads = [dict(s="1", fire=False), dict(s="2", fire=True), dict(s="3/2", fire=True), dict(s="5/4", fire=False), dict(s="11/8", fire=False)]
        self.assertFalse(scan6.contradictory(reads))
        reads += [dict(s="13/8", fire=False)]                         # silent above a fired state
        self.assertTrue(scan6.contradictory(reads))
        states, ok = scan6.verdicts(reads + [dict(s="13/8", fire=True), dict(s="13/8", fire=True)])
        self.assertTrue(states[F(13, 8)])
        self.assertTrue(ok)
        states, ok = scan6.verdicts(reads + [dict(s="13/8", fire=False), dict(s="13/8", fire=True)])
        self.assertFalse(states[F(13, 8)])                            # silent by the majority, above the fired 3/2
        self.assertFalse(ok)


class Choice(unittest.TestCase):
    def costs(self, b, c):
        return {"1/4": dict(pair=b, line=b, both=b, onesided=F(250) / F(151, 100)), "1/2": dict(pair=c, line=c, both=c, onesided=F(250) / F(151, 100))}

    def test_rule(self):
        tie = report6.choose(self.costs(F(785) / F(151, 100), F(785) / F(151, 100)))
        self.assertEqual((tie["B"]["least_k"], tie["C"]["least_k"], tie["choice"], tie["delta"]), (4, 4, "B", "1/4"))
        c = report6.choose(self.costs(F(785) / F(151, 100), F(685) / F(151, 100)))
        self.assertEqual((c["B"]["least_k"], c["C"]["least_k"], c["choice"], c["delta"]), (4, 3, "C", "1/2"))


class StoppingRule(unittest.TestCase):
    MEANS = dict(report6.RM_CAL, pair=F(785), line=F(785), both=F(785), onesided=F(250))

    def test_table(self):
        d3, d4 = report6.decision(3, self.MEANS), report6.decision(4, self.MEANS)
        self.assertEqual((d3["I"], round(float(d3["E"]), 1), d3["go"]), (10, 31319.1, False))
        self.assertEqual((d4["I"], round(float(d4["E"]), 1), d4["go"]), (8, 28504.5, True))
        self.assertFalse(report6.decision(1, self.MEANS)["go"])
        self.assertEqual(report6.least_k(self.MEANS), 4)

    def test_report(self):
        recs = [dict(id=f"x{i}-{k}", machine="a", cost_kind=k, status="complete", wall_s=float(v)) for i in range(2) for k, v in self.MEANS.items()]
        xs = [dict(seed=7701 + i, measured=True, eligible=i < 4, gate_K0=i < 4, question_1={}) for i in range(10)]
        out = report6.report(xs, recs)
        self.assertEqual(out["k"], 4)
        self.assertEqual(out["decision"]["go"], "True")
        self.assertEqual(out["decision"]["I"], "8")


class Equivalence(unittest.TestCase):
    """batch6.cal against run4.run's cal branch, for the nominal cell: the same deck text and the same record, key for
    key, apart from what run4 sets from the kit or measures of itself (id, stage, wall_s, peak_rss_MB) and batch6's
    one added key (batch). session4.play is replaced by a fake that writes the evidence from the deck text."""

    def fake_play(self, texts):
        import numpy as np
        import session4
        net = session4.net

        def play(out, plan, text, ngspice, pdk, seed=None, guard_off=False, noise_id=None, shim=None):
            texts.append(text)
            out = Path(out)
            out.mkdir(parents=True)
            (out / "pdk").symlink_to("/nonexistent")
            for name in ("input.spice", "session.log", "trace.raw"):
                (out / name).write_text(f"{name}\n{text}\n{seed}\n{guard_off}\n")
            result = dict(horizon_s=0.01, waveform_ends_s=0.0101, points=1234)
            (out / "result.json").write_text(json.dumps(result) + "\n")
            tr = mock.Mock()
            tr.t = np.linspace(0, 0.0101, 2000)
            names = [v for c in c4.CELLS for v in [f"v(x{c}.nzm)"] + [f"v(x{c}.x{p}.{n})" for p in net.PORTS for n in ("nzo", "nzc")]]
            tr.v = {n: np.zeros(2000) for n in names}
            return result, tr
        return play

    def test_cal_is_run4s(self):
        import argparse
        import tempfile
        import run4
        import session4
        texts = []
        with tempfile.TemporaryDirectory() as d, mock.patch.object(session4, "play", self.fake_play(texts)):
            d = Path(d)
            args = argparse.Namespace(out=d / "run4", ngspice=Path("ngspice"), pdk=Path("pdk"), id="x", kind="cal", seed="none", instances=0,
                                      guard="on", cell=None, state=None, port="none", isolation=0, reuse_trip=0, needs=None, control="none",
                                      noise="none", round=0, extraction=None, extraction_sha256=None, scale="1", stage=None)
            r4 = run4.run(args)
            r6 = batch6.cal(d / "batch", None, "on", Path("ngspice"), Path("pdk"))
            on4, on6 = json.loads((d / "run4" / "record.json").read_text()), json.loads((d / "batch" / "record.json").read_text())
        self.assertEqual(texts[0], texts[1])
        drop = lambda r: {k: v for k, v in r.items() if k not in ("id", "stage", "wall_s", "peak_rss_MB", "batch")}
        self.assertEqual(drop(on4), drop(on6))
        self.assertEqual(list(on6)[:-1], list(on4))            # the same keys in the same order, then `batch`
        self.assertEqual(list(on6)[-1], "batch")
        self.assertEqual(drop(r4), drop(r6))


class Marker(unittest.TestCase):
    def test_refused_without_marker(self):
        import schedule6
        with mock.patch.object(schedule6, "git", side_effect=subprocess.CalledProcessError(128, "git show")):
            with self.assertRaises(subprocess.CalledProcessError):
                schedule6.main(["batch", "a", "/tmp/never", "1/4", "ngspice", "pdk"])

    def fake(self, m, check):
        import schedule6

        def git(*args):
            if args[0] == "show" and args[1] == f"FETCH_HEAD:{schedule6.MARKER}":
                return json.dumps(m).encode()
            if args[0] == "show" and args[1] == f"FETCH_HEAD:{schedule6.CHECK_FILE}":
                return check
            if args[0] == "show":
                return (schedule6.REPO / args[1].split(":", 1)[1]).read_bytes()
            return b""
        return git

    def test_marker_rules(self):
        import hashlib
        import schedule6
        files = {f: hashlib.sha256((schedule6.REPO / f).read_bytes()).hexdigest() for f in schedule6.imported_files()}
        self.assertEqual(sum(1 for f in files if "campaign-5/" in f), 38)
        self.assertIn(str((HERE / "check7692.py").relative_to(schedule6.REPO)), files)
        check = json.dumps(dict(all_within=True)).encode()
        good = dict(code_commit="c" * 40, delta="1/4", files=dict(files), check7692=dict(sha256=hashlib.sha256(check).hexdigest(), all_within=True))
        with mock.patch.object(schedule6, "git", side_effect=self.fake(good, check)):
            self.assertEqual(schedule6.marker_check()["delta"], "1/4")
        bad = copy.deepcopy(good)
        bad["files"][str((HERE / "batch6.py").relative_to(schedule6.REPO))] = "0" * 64
        missing = copy.deepcopy(good)
        del missing["files"]["research/learned-dnf-circuit-campaign-5/predicted.py"]
        notwithin = copy.deepcopy(good)
        notwithin["check7692"]["all_within"] = False
        for m, chk in ((bad, check), (missing, check), (notwithin, check), (good, json.dumps(dict(all_within=False)).encode())):
            with mock.patch.object(schedule6, "git", side_effect=self.fake(m, chk)):
                with self.assertRaises(AssertionError):
                    schedule6.marker_check()


class SmokeCosts(unittest.TestCase):
    def test_costs_table(self):
        runs = [dict(cost_kind=f"{k}@{s}", status="complete", wall_s=w) for k in ("pair", "line", "both") for s, w in (("1/4", 500.0), ("1/2", 450.0))]
        runs.append(dict(cost_kind="onesided", status="complete", wall_s=150.0))
        c = report6.smoke_costs(runs)
        self.assertEqual(c["1/2"], dict(pair=F(450), line=F(450), both=F(450), onesided=F(150)))
        runs += [dict(cost_kind="pair@1/4", status="complete", wall_s=700.0), dict(cost_kind="onesided", status="complete", wall_s=250.0)]
        c = report6.smoke_costs(runs)
        self.assertEqual((c["1/4"]["pair"], c["1/4"]["onesided"], c["1/2"]["onesided"]), (F(600), F(200), F(200)))   # means, not the last
        self.assertIn(report6.choose(c)["choice"], ("B", "C"))


class ReviewDefects(unittest.TestCase):
    def setUp(self):
        self.t, self.dose = cases.nominal()

    def test_one_sided_bounds_rechecked(self):
        sc = nominal_scans()
        ones = ones_for(self.t, sc)
        why, _ = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], sc, ones)
        self.assertEqual(why, [])
        ones["a"] = dict(ones["a"], bounds=dict(ones["a"]["bounds"], **{"1": str(F(ones["a"]["bounds"]["1"]) + F(1, 1000))}))
        why, _ = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], sc, ones)
        self.assertTrue(any(w.startswith("one-sided set of a: its bounds") for w in why), why)

    def test_runs_at_their_limit_in_the_means(self):
        recs = [dict(id="1", cost_kind="pair", status="complete", wall_s=800.0), dict(id="2", cost_kind="pair", status="missing (limit)", wall_s=None),
                dict(id="3", cost_kind="pair", status="failed (exit 1)", wall_s=None), dict(id="4", cost_kind="onesided", status="missing (limit)", wall_s=None)]
        m = report6.mean_walls(recs)
        self.assertEqual(m["pair"], (F(800) + 2360) / 2)
        self.assertEqual(m["onesided"], F(750))

    def test_merge(self):
        import schedule6
        import tempfile
        ids = sorted(schedule6.expected_ids())
        self.assertEqual(len(ids), 90)
        with tempfile.TemporaryDirectory() as d:
            d = Path(d)
            for m in ("a", "b"):
                (d / m).mkdir()
                mine = [dict(id=i, machine=m, cost_kind="x", status="complete" if i.endswith("on") else "missing (limit)", wall_s=1.0)
                        for i in ids if batch6.MACHINE_OF[int(i.split("-")[0])] == m]
                (d / m / "RUNS.json").write_text(json.dumps(mine))
            runs = schedule6.merge(d)
            self.assertEqual(sorted(r["id"] for r in runs), ids)
            self.assertEqual({r["id"]: r["status"] for r in runs}, {r["id"]: r["status"] for r in json.loads((d / "RUNS.json").read_text())})
            part = json.loads((d / "b" / "RUNS.json").read_text())
            (d / "b" / "RUNS.json").write_text(json.dumps(part + part[:1]))
            with self.assertRaises(AssertionError):
                schedule6.merge(d)
            (d / "b" / "RUNS.json").write_text(json.dumps(part[1:]))
            with self.assertRaises(AssertionError):
                schedule6.merge(d)

    def test_u0_against_the_own_deck(self):
        sc = nominal_scans()
        deck = {(c, p): F(3895, 10000) for c in c4.CELLS for p in (1, 2)}
        for v in sc.values():
            v["u0_V"] = {"1": "0.3895", "2": "0.389519"}                 # 19 uV
        ones = ones_for(self.t, sc)
        for v in ones.values():
            v["u0_V"] = {"1": "0.3895", "2": "0.3895"}
        why, _ = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], sc, ones, deck)
        self.assertEqual(why, [])
        sc[("c", "both")]["u0_V"] = {"1": "0.3895", "2": "0.389521"}     # 21 uV
        why, _ = predict6.measure_instance(7701, STATUSES, self.t, self.dose, [], sc, ones, deck)
        self.assertTrue(any("('c', 'both'): u(0) of port 2 differs" in w for w in why), why)


if __name__ == "__main__":
    unittest.main()
