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


S_NOMINAL = {("a", "pair"): "861/256", ("b", "pair"): "859/256", ("c", "line1"): "917/256", ("c", "line2"): "917/256"}


def nominal_scans(s=None, half="1/256"):
    """Synthetic scans in the nominal smoke's range (s* between stages 3 and 4, so need 4)."""
    s = {**S_NOMINAL, **(s or {})}
    return {key: dict(crossing=True, consistent=True, contradictory=False, s_star=s[key], half_bracket=half,
                      bracket=[str(F(s[key]) - F(half)), str(F(s[key]) + F(half))], L=100000) for key in predict6.CROSSINGS}


def nominal_w(t, wobble=F(0)):
    """w_p of every deck read: k doses before a read of stage k (the deck's joint doses come at the end of each stage),
    plus an optional variation per stage."""
    return {key: {p: key[1] + (wobble if key[1] % 2 else 0) for p in (1, 2)} for key in t}


def ones_for(scans, silent=True):
    """One-sided sets run at exactly the bounds of MAPPING_U.md 2 (W_x + h_x)."""
    S = {x: F(scans[(x, "pair")]["s_star"]) for x in ("a", "b")}
    h = {x: F(scans[(x, "pair")]["half_bracket"]) for x in ("a", "b")}
    b = predict6.layer1_bounds(S, h)
    return {c: dict(all_silent=silent, silent={"1": silent, "2": silent}, bounds={"1": str(b[c]), "2": str(b[c])}) for c in ("a", "b")}


def run(t, dose, scans, ones=None, both=None, w=None, statuses=None, deck_u=None):
    return predict6.measure_instance(7701, statuses or STATUSES, t, dose, [], scans, ones_for(scans) if ones is None else ones, deck_u,
                                     dict(kind="bothfire", fired=True) if both is None else both, nominal_w(t) if w is None else w)


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

    def test_nominal_measured_and_decoded(self):
        why, data = run(self.t, self.dose, nominal_scans())
        self.assertEqual(why, [])
        t2 = data["t2"]
        for k in range(8):                     # the decoder holds on every deck read, by construction of the nominal case
            self.assertEqual(t2[("a", k, "both")]["Z"] >= 100000, k >= 4)
            self.assertLess(t2[("a", k, "port 1")]["Z"], 100000)
            self.assertEqual(t2[("a", k, "empty")]["Z"], 0)

    def test_decoder_disagreement(self):
        t = copy.deepcopy(self.t)
        t[("a", 2, "both")]["fire"] = True                           # a FIRE where the u axis says silent
        why, _ = run(t, self.dose, nominal_scans())
        self.assertTrue(any("('a', 2, 'both')" in w and "disagree (Z >= THETA)" in w for w in why), why)
        t = copy.deepcopy(self.t)
        t[("c", 6, "port 2")]["fire"] = False                        # a silence where it says FIRE
        why, _ = run(t, self.dose, nominal_scans())
        self.assertTrue(any("('c', 6, 'port 2')" in w for w in why), why)

    def test_question_1_in_measured(self):
        why, data = run(self.t, self.dose, nominal_scans({("a", "pair"): "9/2"}))
        self.assertTrue(any(w.startswith("question 1: need a:") for w in why))
        self.assertEqual(data["question_1"]["a"], dict(predicted=5, observed=4, agree=False))

    def test_causes(self):
        sc = nominal_scans()
        sc[("c", "line2")] = dict(crossing=False, why="no crossing below 8")
        why, _ = run(self.t, self.dose, sc, ones={}, statuses=dict(STATUSES, **{"7701-scan-a-pair": "missing (limit)"}))
        self.assertIn("run 7701-scan-a-pair did not complete: missing (limit)", why)
        self.assertIn("scan ('c', 'line2'): no crossing below 8", why)
        sc = nominal_scans()
        ones = ones_for(sc)
        ones["b"] = dict(ones["b"], all_silent=False)
        why, _ = run(self.t, self.dose, sc, ones)
        self.assertTrue(any(w.startswith("one-sided set of b: a port alone fired") for w in why))

    def test_errors_and_room(self):
        why, data = run(self.t, self.dose, nominal_scans())
        an = predict6.anchors({k: F(v) for k, v in S_NOMINAL.items()})
        self.assertEqual(data["H"], dict(a=-(-F(1, 256) * 2 * an["d"] // 1), b=-(-F(1, 256) * 2 * an["d"] // 1), c=-(-F(1, 256) * an["d_c"] // 1)))
        self.assertEqual(data["S"], dict(a=0, b=0, c=0))
        x0 = P.instance(7701, data["t2"], self.dose, [], c4.DECISION5)
        x = predict6.augmented(x0, data["H"], data["S"], data["t2"])
        for K in ("K0", "K3"):
            for c in c4.CELLS:
                for side in ("training", "testing"):
                    self.assertEqual(x["budgets"][K][c][side], x0["budgets"][K][c][side] + data["H"][c])
        self.assertTrue(x["eligible"], x.get("why_not_eligible"))   # the u axis on a linear training: the nominal shape passes
        self.assertLess(max(x0["epsilon"].values()), 10)             # epsilon is only the rounding when w = k exactly
        z = predict6.augmented(x0, {c: 0 for c in c4.CELLS}, {c: 0 for c in c4.CELLS}, data["t2"])
        self.assertEqual((z["room"], z["eligible"]), (x0["room"], x0["eligible"]))


class Anchors(unittest.TestCase):
    """MAPPING_U.md 1 and 2: the anchors on given s*, every deck alone read silent, the both lines at THETA, rounding."""

    def check(self, sa, sb, s1, s2):
        S = {("a", "pair"): F(sa), ("b", "pair"): F(sb), ("c", "line1"): F(s1), ("c", "line2"): F(s2)}
        an = predict6.anchors(S)
        K = max(max(8 - F(x), F(x)) for x in (sa, sb))
        self.assertEqual(an["K"], K)
        self.assertEqual(an["d"], round(F(100000) / (2 * K)))
        for x, s in (("a", F(sa)), ("b", F(sb))):
            g = an["gain"][(x, 1)]
            self.assertEqual(g, an["gain"][(x, 2)])
            self.assertGreaterEqual(g, 0)
            self.assertEqual(an["W"][x], s + K)
            self.assertGreaterEqual(an["W"][x], 8)
            self.assertGreaterEqual(an["W"][x], 2 * s)
            cross = (F(100000) - 2 * g) / (2 * an["d"])                    # rounding: the pair still crosses at s*
            self.assertLessEqual(abs(cross - s), (K + 1) / (2 * an["d"]))
            for k in range(8):                                             # every deck alone read predicted silent
                self.assertLess(g + an["d"] * k, 100000)
        both0 = an["gain"][("c", 1)] + an["gain"][("c", 2)]                 # c's both lines at the preset: THETA, to the
        self.assertLessEqual(abs(both0 - 100000), (F(s1) + F(s2)) / 2 + 1)    # rounding of d_c (at most (s*_1 + s*_2) / 2)
        for p, s in ((1, F(s1)), (2, F(s2))):
            cross = (F(100000) - an["gain"][("c", p)]) / an["d_c"]
            self.assertLessEqual(abs(cross - s), F(1, an["d_c"]))
        self.assertTrue(all(g < 10 * 100000 for g in an["gain"].values()))  # the rail
        return an

    def test_nominal_range(self):
        an = self.check("861/256", "859/256", "917/256", "917/256")
        self.assertEqual(an["K"], 8 - F(859, 256))

    def test_near_five(self):
        an = self.check("5", "3", "9/2", "4")
        self.assertEqual((an["K"], an["W"]["a"], an["W"]["b"], an["gain"][("a", 1)]), (5, 10, 8, 0))
        self.check("1", "1", "1", "2")
        self.check("19/4", "4", "1/2", "5")


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
        return {"1/4": dict(pair=b, line=b, bothfire=F(36), onesided=F(250) / F(151, 100)), "1/2": dict(pair=c, line=c, bothfire=F(36), onesided=F(250) / F(151, 100))}

    def test_rule(self):
        k = F(151, 100)
        tie = report6.choose(self.costs(F(785) / k, F(785) / k))
        self.assertEqual((tie["B"]["least_k"], tie["C"]["least_k"], tie["choice"], tie["delta"]), (3, 3, "B", "1/4"))
        c = report6.choose(self.costs(F(1000) / k, F(785) / k))
        self.assertEqual((c["B"]["least_k"], c["C"]["least_k"], c["choice"], c["delta"]), (5, 3, "C", "1/2"))
        b = report6.choose(self.costs(F(785) / k, F(1000) / k))
        self.assertEqual((b["B"]["least_k"], b["C"]["least_k"], b["choice"]), (3, 5, "B"))


class StoppingRule(unittest.TestCase):
    MEANS = dict(report6.RM_CAL, pair=F(785), line=F(785), bothfire=F(785), onesided=F(250))

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
        self.assertEqual(sum(1 for f in files if "campaign-6/" not in f), 66)
        for f in ("research/network-circuit/net.py", "research/circuit/cell.spice", "research/learned-dnf-circuit/dnf.py",
                  "research/sky130-supervisor-closure/sim.py", "research/learned-coincidence/MonotonePremiseSoundness.lean"):
            self.assertIn(f, files)
        self.assertNotIn(".github/workflows/learned-dnf-circuit-campaign-5.yml", files)
        self.assertIn(str((HERE / "check7692.py").relative_to(schedule6.REPO)), files)
        check = json.dumps(dict(all_within=True)).encode()
        good = dict(code_commit="c" * 40, delta="1/4", files=dict(files), check7692=dict(sha256=hashlib.sha256(check).hexdigest(), all_within=True))
        with mock.patch.object(schedule6, "git", side_effect=self.fake(good, check)):
            self.assertEqual(schedule6.marker_check()["delta"], "1/4")
        bad = copy.deepcopy(good)
        bad["files"][str((HERE / "batch6.py").relative_to(schedule6.REPO))] = "0" * 64
        missing = copy.deepcopy(good)
        del missing["files"]["research/learned-dnf-circuit-campaign-5/predicted.py"]
        outside = copy.deepcopy(good)
        outside["files"]["research/network-circuit/net.py"] = "0" * 64       # a file outside campaign 5's folder changed
        notwithin = copy.deepcopy(good)
        notwithin["check7692"]["all_within"] = False
        for m, chk in ((bad, check), (missing, check), (outside, check), (notwithin, check), (good, json.dumps(dict(all_within=False)).encode())):
            with mock.patch.object(schedule6, "git", side_effect=self.fake(m, chk)):
                with self.assertRaises(AssertionError):
                    schedule6.marker_check()


class SmokeCosts(unittest.TestCase):
    def test_costs_table(self):
        runs = [dict(cost_kind=f"{k}@{s}", status="complete", wall_s=w) for k in ("pair", "line") for s, w in (("1/4", 500.0), ("1/2", 450.0))]
        runs += [dict(cost_kind="onesided", status="complete", wall_s=150.0), dict(cost_kind="bothfire", status="complete", wall_s=36.0)]
        c = report6.smoke_costs(runs)
        self.assertEqual(c["1/2"], dict(pair=F(450), line=F(450), bothfire=F(36), onesided=F(150)))
        runs += [dict(cost_kind="pair@1/4", status="complete", wall_s=700.0), dict(cost_kind="onesided", status="complete", wall_s=250.0)]
        c = report6.smoke_costs(runs)
        self.assertEqual((c["1/4"]["pair"], c["1/4"]["onesided"], c["1/2"]["onesided"]), (F(600), F(200), F(200)))   # means, not the last
        self.assertIn(report6.choose(c)["choice"], ("B", "C"))


class ReviewDefects(unittest.TestCase):
    def setUp(self):
        self.t, self.dose = cases.nominal()

    def test_one_sided_bounds_rechecked(self):
        sc = nominal_scans()
        ones = ones_for(sc)
        why, _ = run(self.t, self.dose, sc, ones)
        self.assertEqual(why, [])
        ones["a"] = dict(ones["a"], bounds={"1": str(F(ones["a"]["bounds"]["1"]) - F(1, 1000)), "2": ones["a"]["bounds"]["2"]})
        why, _ = run(self.t, self.dose, sc, ones)
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
        ones = ones_for(sc)
        for v in ones.values():
            v["u0_V"] = {"1": "0.3895", "2": "0.3895"}
        both = dict(kind="bothfire", fired=True, u0_V={"1": "0.3895", "2": "0.3895"})
        why, _ = run(self.t, self.dose, sc, ones, both, deck_u=deck)
        self.assertEqual(why, [])
        sc[("c", "line2")]["u0_V"] = {"1": "0.3895", "2": "0.389521"}    # 21 uV
        why, _ = run(self.t, self.dose, sc, ones, both, deck_u=deck)
        self.assertTrue(any("('c', 'line2'): u(0) of port 2 differs" in w for w in why), why)


class BothLines(unittest.TestCase):
    """v9: c's both lines are predicted to FIRE only; their FIRE check at s = 0, and the deck's monotonicity."""

    def setUp(self):
        self.t, self.dose = cases.nominal()

    def test_check_and_deck(self):
        sc = nominal_scans()
        self.assertEqual(sorted(sc), [("a", "pair"), ("b", "pair"), ("c", "line1"), ("c", "line2")])
        why, data = run(self.t, self.dose, sc)
        self.assertEqual(why, [])
        z0 = data["t2"][("c", 0, "both")]["Z"]                                          # at THETA at s = 0, to the rounding,
        self.assertLessEqual(abs(z0 - 100000), 5)                                       # inside the H band
        self.assertLessEqual(abs(z0 - 100000), data["H"]["c"])
        why, _ = run(self.t, self.dose, sc, both=dict(fired=False))
        self.assertIn("the both-lines FIRE check of c: both lines did not fire at the preset (s = 0)", why)
        w = nominal_w(self.t)
        w[("c", 5, "both")] = {1: F(-1, 10), 2: F(-1, 10)}                              # below stage 0: not monotone
        t = copy.deepcopy(self.t)
        t[("c", 6, P.SKEWED)]["fire"] = False
        why, _ = run(t, self.dose, sc, w=w)
        self.assertTrue(any("('c', 5, 'both')" in x and "monotonicity" in x for x in why), why)
        self.assertTrue(any("('c', 6, 'both, second 0.3 late')" in x and "did not fire" in x for x in why), why)

    def test_wave_3_waits_for_both_pair_scans(self):
        import schedule6
        import tempfile
        jobs = schedule6.instance_jobs(7701, F(1, 2))
        j = next(x for x in jobs if x["id"] == "7701-onesided-a")
        self.assertEqual(sorted(x["id"] for x in schedule6.wave_deps(j, jobs)),
                         ["7701-cal-off", "7701-cal-on", "7701-scan-a-pair", "7701-scan-b-pair"])
        sc = nominal_scans()
        with tempfile.TemporaryDirectory() as d, mock.patch.object(predict6, "table", return_value=(self.t, self.dose, [])):
            d = Path(d)
            for x in ("a", "b"):
                (d / f"7701-scan-{x}-pair").mkdir()
                (d / f"7701-scan-{x}-pair" / "record.json").write_text(json.dumps(dict(result=sc[(x, "pair")])))
            cmd, why = schedule6.command(j, d, ("on", "off"), Path("ngspice"), Path("pdk"))
            b = predict6.layer1_bounds({x: F(sc[(x, "pair")]["s_star"]) for x in "ab"}, {x: F(1, 256) for x in "ab"})["a"]
            self.assertIsNone(why)
            self.assertEqual(cmd[cmd.index("onesided") + 1:cmd.index("onesided") + 3], [str(b), str(b)])
            (d / "7701-scan-b-pair" / "record.json").write_text(json.dumps(dict(result=dict(crossing=True, consistent=False))))
            cmd, why = schedule6.command(j, d, ("on", "off"), Path("ngspice"), Path("pdk"))
            self.assertIsNone(cmd)
            self.assertEqual(why, "the pair scan of b has no consistent bracket")
            (d / "7701-scan-b-pair" / "record.json").unlink()
            cmd, why = schedule6.command(j, d, ("on", "off"), Path("ngspice"), Path("pdk"))
            self.assertEqual(why, "the pair scan of b did not complete")

    def test_runs_per_instance(self):
        import schedule6
        jobs = schedule6.instance_jobs(7701, F(1, 4))
        self.assertEqual(len(jobs), 9)
        self.assertEqual(sorted(j["cost_kind"] for j in jobs), sorted(["cal-on", "cal-off", "pair", "pair", "line", "line", "bothfire", "onesided", "onesided"]))
        self.assertEqual(sum(n for _, n in report6.KINDS), 9)


class Serialization(unittest.TestCase):
    def test_instance_data_is_json(self):
        """Every field predict_instance adds to an instance can be written to PREDICTIONS.json (no tuple key): the
        smoke at 5618699 stopped there on the scans' L, keyed by (cell, kind)."""
        t, dose = cases.nominal()
        sc = nominal_scans()
        why, data = run(t, dose, sc)
        self.assertEqual(why, [])
        x = P.instance(7701, data["t2"], dose, [], c4.DECISION5)
        x = predict6.augmented(x, data["H"], data["S"], data["t2"])
        x.update(machine="a", **{k: v for k, v in data.items() if k != "t2"})
        x.update(predict6.questions(sc, dose, P.needs(t)))
        json.dumps(dict(instances=[x]), default=str)
        self.assertEqual(x["L"]["a-pair"], 100000)

if __name__ == "__main__":
    unittest.main()
