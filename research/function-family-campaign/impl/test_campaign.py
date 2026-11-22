"""Tests of the family campaign's new code, with no simulation.

  PYTHONPATH=FUP/dev:PREP/dev:FF/dev:. python -B test_campaign.py REPO GEN [TOPUP_EV]

TOPUP_EV (optional): the extracted top-up evidence (M1, M3 folders), for the duplicate check on the real pair.
"""
from fractions import Fraction as F
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

REPO, GEN = sys.argv.pop(1), sys.argv.pop(1)
EV = Path(sys.argv.pop(1)) if len(sys.argv) > 1 and not sys.argv[1].startswith("-") else None
import campaign_common as CC                                     # noqa: E402
import family_predict as FP                                      # noqa: E402
FP.paths(REPO, GEN)
predict6, P, spec, mirror, emit = FP.mods()
import analysis as A                                             # noqa: E402
import campaign_measure as CM                                    # noqa: E402
import campaign_predict as CP                                    # noqa: E402
import dupcheck as DC                                            # noqa: E402
import manifests as MF                                           # noqa: E402
import comparisons as C                                          # noqa: E402

sys.argv[1:] = [REPO, GEN]
import test_family_predict as TFP                                # noqa: E402  (the frozen synthetic chains)


class Tables(unittest.TestCase):
    """Every number of campaign_common against PREDICTION.md (385c33bf)."""

    def test_draw_and_machines(self):
        d = CC.draw()
        self.assertEqual({m: [s for s in CC.SEEDS if d[s] == m] for m in CC.MEMBERS},
                         dict(X1=[8501, 8504, 8512], X2=[8502, 8508, 8513], F4=[8505, 8507, 8514], F2=[8506, 8510, 8515], F3=[8503, 8509, 8511]))
        self.assertEqual(sorted(s for ss in CC.MACHINES.values() for s in ss), list(CC.SEEDS))
        self.assertEqual([len(v) for v in CC.MACHINES.values()], [3, 3, 3, 2, 2, 2])

    def test_costs(self):
        self.assertEqual({m: CC.expected_measure_s(m) for m in CC.MEMBERS}, dict(X1=9645, X2=5346, F4=11622, F2=6476, F3=10775))
        d = CC.draw()
        per = {m: sum(CC.expected_measure_s(d[s]) for s in ss) for m, ss in CC.MACHINES.items()}
        self.assertEqual(per, dict(M1=25766, M2=27743, M3=27743, M4=17251, M5=14991, M6=18098))
        self.assertEqual(sum(per.values()), 131592)

    def test_limits_and_seeds(self):
        self.assertEqual({k: CC.limit_s(k) for k in CC.MEANS},
                         {"cal-on": 3330, "cal-off": 2420, "pair": 1410, "line": 1200, "bothfire": 110, "onesided": 960,
                          "cal-on-unary": 4160, "cal-off-unary": 2760, "unary-scan": 1270, "preset": 110})
        self.assertEqual((CC.noise_seed(8501, 1), CC.noise_seed(8515, 3)), (85011, 85153))
        self.assertEqual(sorted(CC.REHEARSAL_NOISE.values()), list(range(83031, 83037)) + list(range(83061, 83067)))
        with self.assertRaises(AssertionError):
            CC.noise_seed(8303, 1)

    def test_runs_match_frozen_code(self):
        """The run ids are the ones family_predict reads (b2_run_ids, tu_run_ids), plus O1's pair scans and both
        ports' unary scans."""
        for m in CC.MEMBERS:
            ids = {r for r, _, _ in CC.measure_runs(8501, m)}
            up = {c: 1 for c, k in CC.KINDS[m].items() if k == "unary"}
            self.assertTrue(set(FP.b2_run_ids(8501, m)) <= ids, m)
            self.assertTrue(set(FP.tu_run_ids(8501, m, up)) <= ids, m)
            self.assertEqual(CC.KINDS[m], FP.kinds(m))

    def test_network_runs(self):
        xs = [dict(seed=8501, member="X1", eligible=True, room_K3=True), dict(seed=8504, member="X1", eligible=True, room_K3=False),
              dict(seed=8502, member="X2", eligible=False, room_K3=False)]
        r = CC.network_runs(xs)
        ids = [x["id"] for x in r]
        self.assertEqual(ids, ["8501-X1-quiet", "8501-X1-n1", "8501-X1-n2", "8501-X1-n3", "8504-X1-quiet", "8501-X1-untrained"])
        self.assertEqual([x.get("noise_seed") for x in r if x["noise"] == "injected"], [85011, 85012, 85013])


class Manifests(unittest.TestCase):
    def test_plan(self):
        p = MF.plan("REPO", "RUNS", "NG", "PDK")
        d = CC.draw()
        for m, st in p.items():
            want = [r for s in CC.MACHINES[m] for r in CC.measure_runs(s, d[s])]
            for name in CC.STAGES:
                got = [j["id"] for j in st[name] if j["id"] != "8501-cal-on-unary-dup"]
                self.assertEqual(got, [r for r, _, stg in want if stg == name], (m, name))
            for j in st["D"] + st["S"] + st["O"]:
                self.assertEqual(j["limit_s"], CC.limit_s(j["kind"]))
                self.assertTrue(j["argv"][2].endswith("campaign_measure.py") and j["argv"][3] == j["kind"])
        dup = [j for j in p["M5"]["D"] if j["id"] == "8501-cal-on-unary-dup"]
        self.assertEqual(len(dup), 1)
        self.assertTrue(dup[0]["argv"][5].endswith("DUP/8501-cal-on-unary-dup") and dup[0]["argv"][6] == "8501")
        self.assertFalse(any(j["id"].endswith("-dup") for m in p if m != "M5" for j in p[m]["D"]))

    def test_bounds(self):
        ok = lambda s, h: dict(crossing=True, consistent=True, s_star=s, half_bracket=h)
        b = MF.bounds_of(dict(a=ok("781/512", "1/512"), b=ok("1001/512", "1/512")))
        K = max(8 - F(781, 512), F(781, 512), 8 - F(1001, 512), F(1001, 512))
        self.assertEqual(b, dict(a=str(F(781, 512) + K + F(1, 512)), b=str(F(1001, 512) + K + F(1, 512))))
        self.assertEqual(MF.bounds_of(dict(a=ok("3/2", "1/512"), b=dict(crossing=True, consistent=False))), dict(a=str(F(3, 2) + 8 - F(3, 2) + F(1, 512))))
        an = FP.anchors("X2", {}, {("a", "pair"): F(3, 2), ("c", "line1"): F(2)}, dict(a=True, b=False), P.THETA)
        self.assertEqual(F(MF.bounds_of(dict(a=ok("3/2", "1/512"), b=None))["a"]), an["W"]["a"] + F(1, 512))

    def test_stage_S_needs_doses(self):
        jobs, ns = MF.stage_S("R", "RUNS", "M1", "NG", "PDK", {}, {})
        self.assertEqual(jobs, [])
        self.assertTrue(all("gave no doses" in x["why"] for x in ns) and len(ns) > 0)


class Guard(unittest.TestCase):
    def test_guard(self):
        self.assertEqual(CM.guard_seed("8501"), 8501)
        for bad in ("8301", "8516", "none", "08501"):
            with self.assertRaises((AssertionError, ValueError)):
                CM.guard_seed(bad)
        with self.assertRaises(AssertionError):
            CM.run("cal-on", REPO, "/nonexistent/x", "8303", [], "ng", "pdk")


class Duplicate(unittest.TestCase):
    def raw(self, d, date, data=b"\x00\x01\x02"):
        p = Path(d) / "trace.raw"
        p.write_bytes(b"Title: t\n" + date + b"Plotname: Transient Analysis\nVariables:\n\t0\ttime\ttime\nBinary:\n" + data)
        return p

    def test_date_only(self):
        with tempfile.TemporaryDirectory() as t1, tempfile.TemporaryDirectory() as t2:
            a = DC.trace_without_date(self.raw(t1, b"Date: Sat Nov 21 09:46:52  2026\n"))
            b = DC.trace_without_date(self.raw(t2, b"Date: Sat Nov 21 11:17:25  2026\n"))
            self.assertEqual(a, b)
            self.assertEqual(a[1], 1)
            c = DC.trace_without_date(self.raw(t2, b"Date: Sat Nov 21 11:17:25  2026\n", b"\x00\x01\x03"))
            self.assertNotEqual(a[0], c[0])                            # one data byte differs: not identical
            d = DC.trace_without_date(self.raw(t2, b"Date: x\nDate: y\n"))
            self.assertEqual(d[1], 2)                                  # two Date lines: hashed as is, and flagged

    @unittest.skipIf(EV is None, "no top-up evidence given")
    def test_topup_pair(self):
        r = DC.compare(EV / "M1" / "8301-cal-on-unary", EV / "M3" / "DUP" / "8301-cal-on-unary-dup")
        self.assertTrue(r["identical"])
        self.assertFalse(r["trace_raw_full_equal"])
        self.assertTrue(r["fields"]["trace_raw"]["first"].startswith("d6195367"))


def synthetic_instance(member, seed, up, room=True):
    x, _ = TFP.Synthetic("chain").chain(member, up)
    kd = FP.kinds(member)
    uport = {c: up[c] for c, k in kd.items() if k == "unary"}
    n = {c: 3 for c in kd}
    n.update({f"c{p}": 3 for p in range(1, len(kd) + 1)})
    return dict(seed=seed, member=member, eligible=True, room_K3=room, needs=n, unary_ports=uport,
                predicted=CP.predicted_words(member, uport, x["observation"]), observation=x["observation"])


class Predicted(unittest.TestCase):
    def test_words(self):
        x = synthetic_instance("F3", 8503, {"a": 2})
        p = x["predicted"]
        self.assertEqual(set(p["words"]), {"a2", "b1", "b2", "c1", "c2"})
        self.assertEqual(p["words"]["a2"], "sssFFF")                    # need 3, Q1 = 5: rounds 0..5
        self.assertEqual(p["words"]["c1"], "sssFFF")
        self.assertEqual({k: v["c"] for k, v in p["tests"].items()},
                         {k: ("A" in k) or ("B" in k and "C" in k) for k in p["tests"]})
        self.assertEqual(p["skew"], {"BC": {"b": False}})
        y = synthetic_instance("X1", 8501, {"a": 1})["predicted"]
        self.assertEqual(set(y["words"]), {"a1", "c1"})
        self.assertEqual({k: v["c"] for k, v in y["tests"].items()}, {"-": False, "A": True})

    def test_rehearsal_runs(self):
        xs = [dict(seed=s, member=m, eligible=True, room_K3=True) for s in (8303, 8306) for m in CC.MEMBERS]
        ids = [r["id"] for r in CP.rehearsal_runs(xs)]
        self.assertEqual(sum(i.endswith("-quiet") for i in ids), 5)
        self.assertEqual(sum(i.endswith("-untrained") for i in ids), 5)
        self.assertEqual(sorted(r["noise_seed"] for r in CP.rehearsal_runs(xs) if r["noise"] == "injected"), sorted(CC.REHEARSAL_NOISE.values()))


class Analysis(unittest.TestCase):
    """End to end on synthetic network records: every run as predicted, then with one change."""

    def setUp(self):
        d = CC.draw()
        ups = [{"a": 1, "b": 1}, {"a": 2, "b": 1}, {"a": 1, "b": 2}]
        xs = []
        for m in CC.MEMBERS:
            for i, s in enumerate(sorted(s for s in CC.SEEDS if d[s] == m)):
                xs.append(synthetic_instance(m, s, ups[i], room=(m in ("X1", "X2") or i == 0)))
        self.pred = dict(instances=xs, network_runs=CC.network_runs(xs))
        self.runs = {}
        for r in self.pred["network_runs"]:
            x = next(y for y in xs if y["seed"] == r["seed"])
            p = x["predicted"]
            if r["control"] == "untrained":
                self.runs[r["id"]] = dict(counts=True, words={}, tests={k: {c: False for c in v} for k, v in p["tests"].items()}, skew={})
            else:
                self.runs[r["id"]] = dict(counts=True, words=dict(p["words"]), tests=json.loads(json.dumps(p["tests"])),
                                          skew=json.loads(json.dumps(p["skew"])) if r["control"] == "skew" else {}, G=[])

    def test_all_as_predicted(self):
        r = A.analysis(self.pred, self.runs)
        self.assertEqual(r["claims"]["primary"]["family"], "established for the family")
        self.assertTrue(all(v["verdict"] == "established" for v in r["claims"]["primary"]["per_member"].values()))
        self.assertTrue(r["claims"]["N-out"]["verdict"].startswith("established, pooled over"))
        self.assertEqual(r["claims"]["N-out"]["per_member"]["X1"], "established")
        self.assertEqual(r["claims"]["N-out"]["per_member"]["F2"], "held on one instance, not established")
        self.assertTrue(r["claims"]["N-own"]["verdict"].startswith("established"))
        self.assertTrue(all(v["verdict"] == "held" for v in r["claims"]["U"].values()))
        self.assertEqual(r["claims"]["S"]["verdict"], "held")
        self.assertEqual(r["missing"], [])

    def test_one_letter_refutes(self):
        rid = "8506-F2-quiet"
        self.runs[rid]["words"]["a1"] = "s" + self.runs[rid]["words"]["a1"][1:].replace("F", "s", 1)
        r = A.analysis(self.pred, self.runs)
        self.assertEqual(r["claims"]["primary"]["per_member"]["F2"]["verdict"], "refuted")
        self.assertTrue(r["claims"]["primary"]["family"].startswith("refuted (F2)"))

    def test_one_output_refutes_noise(self):
        rid = "8501-X1-n2"
        self.runs[rid]["tests"]["A"]["c"] = False
        r = A.analysis(self.pred, self.runs)
        self.assertEqual(r["claims"]["N-out"]["verdict"], "refuted")
        self.assertEqual(r["claims"]["N-out"]["by"]["c"]["failures"], [rid])

    def test_missing_and_minimum(self):
        for rid in [k for k in self.runs if k.startswith(("8510-", "8515-")) and "quiet" in k]:
            self.runs[rid]["counts"] = False
        r = A.analysis(self.pred, self.runs)
        self.assertEqual(r["claims"]["primary"]["per_member"]["F2"]["verdict"], "held on one instance, not established")
        self.assertTrue(r["claims"]["primary"]["family"].startswith("established on the members"))
        self.assertIn("for F2: held on one instance, not established", r["claims"]["primary"]["family"])
        self.assertIn("8510-F2-quiet", r["missing"])

    def test_skew_and_untrained(self):
        self.runs["8503-F3-quiet"]["skew"]["BC"]["b"] = True
        self.runs["8501-X1-untrained"]["tests"]["A"]["c"] = True
        r = A.analysis(self.pred, self.runs)
        self.assertEqual(r["claims"]["S"]["verdict"], "refuted")
        self.assertEqual(r["claims"]["U"]["X1"]["verdict"], "refuted")
        self.assertEqual(r["claims"]["U"]["X2"]["verdict"], "held")

    def test_noisy_run_without_room_is_refused(self):
        x = next(y for y in self.pred["instances"] if y["seed"] == 8501)
        x["room_K3"] = False
        with self.assertRaises(AssertionError):
            A.analysis(self.pred, self.runs)


TU = 1 / 50000


def synthetic_rows(x, u0=100.0, narrow=False):
    """A run's rows and result exactly as the instance predicts (reads4.network_reads' form), every arrival routed."""
    m, cells = x["member"], list(CC.KINDS[x["member"]])
    p, terms = x["predicted"], FP.MEMBERS[x["member"]]["terms"]
    rows, occ, fires = [], [], []
    date = lambda k: 1e-4 + 22 * k * TU
    port = lambda c, i, letter: {"1": dict(writes=int(letter == "s"), writes_prime=int(letter == "s"), u_before_mV=u0 + i, move_mV=0.0,
                                           rises=[dict(rise_s=date(i) + TU, width_s=5e-7 if narrow and i == 0 else 2e-6)] if letter == "s" else []),
                                 "2": dict(writes=int(letter == "s"), writes_prime=int(letter == "s"), u_before_mV=u0 + i, move_mV=0.0, rises=[])}
    read = lambda k, c, f, i, letter: dict(fire=f, latency=0.5 if f else None, start_s=date(k), gated=False, late_fires=0, ports=port(c, i, letter),
                                           fire_date_s=date(k) + 0.5 * TU if f else None)

    def c_read(k, firing, f):
        arr = []
        for a in firing:
            fd = date(k) + 0.5 * TU
            fires.append(dict(cell=a, date_s=fd))
            arr.append(dict(port=C.LINE_PORT[a], date_s=fd + 1.5 * TU, fire_date_s=fd, origin=a))
            occ.append(dict(cell="c", port=C.LINE_PORT[a], date_s=fd + 1.5 * TU, delivered=True))
        r = read(k, "c", f, k, "F" if f else "s")
        r.update(arrivals=arr, skew_units=0.0, start_s=arr[0]["date_s"] if arr else date(k), q_peak=0.0,
                 fire_date_s=arr[-1]["date_s"] + 0.4 * TU if f else None)
        return r
    k = 0
    w1 = {c: next(v for q, v in p["words"].items() if q[0] == c) for c in cells}
    for i in range(len(w1[cells[0]])):
        reads = {c: read(k, c, w1[c][i] == "F", i, w1[c][i]) for c in cells}
        for c in cells:
            occ.append(dict(cell=c, port=1, date_s=date(k), delivered=True))
            if reads[c]["fire"]:
                fires.append(dict(cell=c, date_s=reads[c]["fire_date_s"]))
        rows.append(dict(slot=k, stage="layer 1", date=k * 22, pattern=None, reads=reads))
        k += 1
    nr = len(p["words"]["c1"])
    for i in range(nr):
        for a in cells:
            letter = p["words"][f"c{C.LINE_PORT[a]}"][i]
            occ.append(dict(cell=a, port=1, date_s=date(k), delivered=True))
            reads = {a: read(k, a, True, 100 + i, "F"), "c": c_read(k, [a], letter == "F")}
            rows.append(dict(slot=k, stage="layer 2", date=k * 22, line=a, pattern=None, reads=reads))
            k += 1
    for key, v in p["tests"].items():
        firing = [c for c in cells if v[c]]
        reads = {c: read(k, c, v[c], 200, "F") for c in cells if any(i in C.pattern_set(key) for i in terms[c])}
        for c in reads:
            occ.append(dict(cell=c, port=1, date_s=date(k), delivered=True))
        if firing:
            reads["c"] = c_read(k, firing, v["c"])
        rows.append(dict(slot=k, stage="test", date=k * 22, pattern=list(C.pattern_set(key)), reads=reads))
        k += 1
    return rows, dict(occurrences=occ, fires=fires, still_queued_at_the_horizon=[])


class Reproduction(unittest.TestCase):
    """Section 9's first rule: the pushed record against the regenerated one, byte for byte."""

    def setUp(self):
        t = Analysis("setUp")
        t.setUp()
        self.pred, self.runs = t.pred, t.runs
        self.text = CC.record_text(self.pred)

    def test_reproduced(self):
        r = A.run(self.text, self.pred, self.runs)
        self.assertTrue(r["prediction_record_reproduced"])
        self.assertEqual(r["claims"]["primary"]["family"], "established for the family")

    def test_tampered_record(self):
        rid = next(x for x in self.pred["instances"] if x["member"] == "F2")
        old = json.dumps(rid["predicted"]["words"]["a1"])
        i = self.text.index(old)
        bad = self.text[:i] + old.replace("F", "s", 1) + self.text[i + len(old):]
        r = A.run(bad, self.pred, self.runs)
        self.assertFalse(r["prediction_record_reproduced"])
        self.assertEqual(set(r["claims"]), set(A.CLAIMS))
        self.assertTrue(all(v.startswith("not established") for v in r["claims"].values()))
        self.assertTrue(r["comparisons"].startswith("not computed"))
        self.assertEqual(r["reproduction"]["pushed"].strip(), self.text.split("\n")[r["reproduction"]["first_differing_line"] - 1].strip().replace(old, old.replace("F", "s", 1)))

    def test_serialization_only(self):
        r = A.run(json.dumps(self.pred, indent=2, default=str) + "\n", self.pred, self.runs)
        self.assertFalse(r["prediction_record_reproduced"])
        r = A.run(self.text.rstrip("\n"), self.pred, self.runs)
        self.assertFalse(r["prediction_record_reproduced"])

    def test_regenerated_differs(self):
        again = json.loads(self.text)
        again["instances"][0]["needs"]["a"] += 1
        self.assertFalse(A.run(self.text, again, self.runs)["prediction_record_reproduced"])


class Comparisons(unittest.TestCase):
    """M1 to M8 and H on synthetic rows: every member, with the entries that have no meaning for it."""

    def setUp(self):
        t = Analysis("setUp")
        t.setUp()
        self.pred, self.runs = t.pred, t.runs
        self.pred["constants"] = dict(between_mV=0.111, within_mV=0.094, per_dose_mV=0.009)
        inst = {(x["seed"], x["member"]): x for x in self.pred["instances"]}
        for r in self.pred["network_runs"]:
            if r["control"] == "untrained":
                continue
            x = inst[(r["seed"], r["member"])]
            rows, result = synthetic_rows(x, u0=100.0 + r["round"] * 0.1)
            self.runs[r["id"]].update(rows=rows, result=result, words_prime=dict(self.runs[r["id"]]["words"]))

    def test_shapes(self):
        c = A.analysis(self.pred, self.runs)
        comp, H = c["comparisons"], c["claims"]["H"]["per_member"]
        self.assertTrue(all(v.startswith("no data") for v in comp["M1"].values()))
        self.assertTrue(comp["M2"]["note"].startswith("no data") and comp["M2"]["runs_on_instances_not_eligible"] == [])
        self.assertTrue(all(v.startswith("not computed") for v in comp["M5"].values()))
        self.assertTrue(comp["M3"]["X1"]["8501-X1-quiet"]["skews"].startswith("no meaning for X1"))
        self.assertIsInstance(comp["M3"]["F2"]["8506-F2-quiet"]["skews"], list)
        self.assertEqual(comp["M3"]["F3"]["8503-F3-quiet"]["max_latency"]["c"], 0.5)
        for m in CC.MEMBERS:
            for rid, h in H[m].items():
                self.assertEqual((h["arrivals_not_routed"], h["late_fires"], h["c_fire_outside"], h["undelivered"]), (0, 0, 0, 0), rid)
                self.assertEqual(h["member"], m)
        self.assertTrue(H["X2"]["8502-X2-quiet"]["skews_above_bound"].startswith("no meaning"))
        self.assertEqual(H["F4"]["8505-F4-quiet"]["skews_above_bound"], 0)
        self.assertEqual(comp["M6"]["narrow_crossings"], {})
        self.assertTrue(all(v == {} for v in comp["M6"]["word_and_word_prime_differ"].values()))
        self.assertTrue(comp["M8"]["X1"]["8501-X1-quiet"]["assumption_on_c"].startswith("no meaning"))
        self.assertTrue(comp["M8"]["F2"]["8506-F2-quiet"]["checkers"].startswith("no data"))

    def test_M4_nominal(self):
        comp = A.analysis(self.pred, self.runs)["comparisons"]["M4"]
        self.assertEqual(comp, {m: {} for m in CC.MEMBERS})           # synthetic instances carry no `measured`
        for x in self.pred["instances"]:
            x["measured"] = True
        comp = A.analysis(self.pred, self.runs)["comparisons"]["M4"]
        f3 = comp["F3"]["8503-F3"]
        up = next(x for x in self.pred["instances"] if x["seed"] == 8503)["unary_ports"]["a"]
        self.assertTrue(f3["nominal_words"][f"a{up}"].startswith("no meaning for F3"))
        self.assertEqual(f3["nominal_words"]["b1"], "ssssFF")
        self.assertIn(dict(port="b1", i=3, nominal="s", other="F"), f3["words_vs_measured"])
        self.assertEqual(f3["tests_vs_measured"], [])                  # the synthetic chain answers f's truth table
        self.assertEqual(f3["words_vs_run"], f3["words_vs_measured"])

    def test_M6_and_H_find_what_was_put(self):
        rid = "8506-F2-quiet"
        x = next(y for y in self.pred["instances"] if y["seed"] == 8506)
        rows, result = synthetic_rows(x, narrow=True)
        a = next(y for y in rows if y["stage"] == "layer 2")["reads"]["c"]["arrivals"][0]
        a["fire_date_s"] += 3 * TU
        self.runs[rid].update(rows=rows, result=result)
        self.runs["8501-X1-n1"]["words_prime"]["a1"] = "s" + self.runs["8501-X1-n1"]["words_prime"]["a1"]
        c = A.analysis(self.pred, self.runs)
        self.assertEqual(len(c["comparisons"]["M6"]["narrow_crossings"][rid]), 2)     # a1 and b1 at slot 0
        self.assertEqual(list(c["comparisons"]["M6"]["word_and_word_prime_differ"]["8501-X1-n1"]), ["a1"])
        self.assertEqual(c["claims"]["H"]["per_member"]["F2"][rid]["arrivals_not_routed"], 1)
        self.assertEqual(c["claims"]["primary"]["family"], "established for the family")   # H decides nothing

    def test_M7(self):
        comp = A.analysis(self.pred, self.runs)["comparisons"]["M7"]
        x1 = comp["X1"]["8501-X1"]
        self.assertEqual(set(x1), {"a1", "c1"})
        self.assertEqual(x1["a1"]["runs"], 3)
        self.assertAlmostEqual(x1["a1"]["u_end_spread_mV"], (2 / 3) ** 0.5 * 0.1)
        self.assertAlmostEqual(x1["a1"]["model_sigma_mV"], (0.094 ** 2 + 0.111 ** 2 + 3 * 0.009 ** 2) ** 0.5)
        self.assertEqual(x1["c1"]["first_F_latency"], [0.5, 0.5, 0.5])
        self.assertEqual(set(comp["X1"]), {"8501-X1", "8504-X1", "8512-X1"})   # every X1 instance has room here
        self.assertEqual(set(comp["X1"]["8504-X1"]), {"a2", "c1"})             # its unary port is 2
        self.assertEqual(set(comp["F2"]), {"8506-F2"})                 # F2's only instance with room

    def test_runs_without_rows(self):
        for v in self.runs.values():
            for k in ("rows", "result", "words_prime"):
                v.pop(k, None)
        c = A.analysis(self.pred, self.runs)
        self.assertTrue(all(isinstance(v, str) and v.startswith("no data") for m in CC.MEMBERS for v in c["comparisons"]["M3"][m].values()))
        self.assertTrue(all(isinstance(v, str) and v.startswith("no data") for m in CC.MEMBERS for v in c["claims"]["H"]["per_member"][m].values()))

    def test_assumption_on_c_two_lines(self):
        x = next(y for y in self.pred["instances"] if y["member"] == "F4" and y["room_K3"])
        x["needs"]["c2"] = 4
        rid = f"{x['seed']}-F4-quiet"
        a = A.analysis(self.pred, self.runs)["comparisons"]["M8"]["F4"][rid]["assumption_on_c"]
        self.assertEqual((a["line_a_alone"]["pattern"], a["line_b_alone"]["pattern"]), ("A", "B"))
        self.assertEqual(a["line_a_alone"]["run"], 0.5)
        self.assertEqual(a["line_a_alone"]["calibration"], 0.5)

    def test_M8_mirror_on_the_predicted_observation(self):
        """The run's observation equal to the predicted one gives the mirror's verdicts of the prediction."""
        full, _ = TFP.Synthetic("chain").chain("F4", {"a": 1, "b": 2})
        x = next(y for y in self.pred["instances"] if y["member"] == "F4" and y["room_K3"])
        x.update({k: full[k] for k in ("guarded", "epsilon", "budgets", "Q1", "Q2", "observation")}, unary_ports=dict(full["unary_ports"]))
        rid = f"{x['seed']}-F4-quiet"
        self.runs[rid]["observation"] = json.loads(json.dumps(full["observation"]))
        m8 = A.analysis(self.pred, self.runs)["comparisons"]["M8"]["F4"][rid]
        s = spec.load(FP.raw_spec(x, "ref", "test"))
        want = FP.mirror_verdicts(s)
        self.assertEqual({K: v["checks"] for K, v in m8["mirror"].items()}, {K: v["checks"] for K, v in want.items()})
        self.assertTrue(m8["kernel"].startswith("not computed"))
        if os.environ.get("LEAN"):                                     # (b): once through the Lean kernel
            with tempfile.TemporaryDirectory() as d:
                gate = dict(out_dir=d, gen=GEN, lean=os.environ["LEAN"], build=Path(d) / "build")
                k = A.analysis(self.pred, self.runs, gate)["comparisons"]["M8"]["F4"][rid]
            self.assertEqual(k["kernel"], {K: v["checks"] for K, v in want.items()})
            self.assertTrue(k["kernel_agrees_with_mirror"])


class NetworkManifests(unittest.TestCase):
    """Q, N1 to N3 and R-N from the record: one run per (instance, kind, round), the placement, the place-holders."""

    def setUp(self):
        t = Analysis("setUp")
        t.setUp()
        self.pred = dict(t.pred, mode="campaign")
        for x in self.pred["instances"]:
            x.update(Q1=5, Q2=5)

    def test_campaign_plan(self):
        p = MF.network_plan(self.pred)
        self.assertEqual(set(p), set(CC.MACHINES))
        for m, st in p.items():
            for name, jobs in st.items():
                for j in jobs:
                    self.assertEqual(j["machine"], m)
                    self.assertEqual(CC.machine_of(j["seed"]), m)
                    self.assertEqual(j["limit_s"], MF.LIMIT_PLACEHOLDER)
                    self.assertEqual(j["argv"], MF.COMMAND_PLACEHOLDER)
                    if name == "Q":
                        self.assertIn(j["kind"], ("quiet", "untrained"))
                    else:
                        self.assertEqual((j["kind"], j["round"]), ("noisy", int(name[1])))
                        self.assertEqual(j["noise_seed"], 10 * j["seed"] + j["round"])
        q = p["M1"]["Q"]
        self.assertEqual([j["kind"] for j in q], sorted((j["kind"] for j in q), key=lambda k: k == "untrained"))
        self.assertEqual(sum(len(v) for st in p.values() for v in st.values()), len(self.pred["network_runs"]))
        self.assertEqual(p["M1"]["N1"][0]["expected_s"], [round(1179 * 0.37), round(2676 * 0.37)])

    def test_one_run_per_seed_kind_round(self):
        r = next(r for r in self.pred["network_runs"] if r["scenario"] == "n2")
        self.pred["network_runs"].append(dict(r, id=r["id"] + "-again"))
        with self.assertRaises(AssertionError):
            MF.network_plan(self.pred)

    def test_refusals(self):
        for change in (lambda rs: rs.pop(),                                               # a run missing
                       lambda rs: next(r for r in rs if r["noise"] != "none").update(noise_seed=1),
                       lambda rs: next(r for r in rs if r["noise"] == "none").update(machine="M6" if rs[0]["machine"] != "M6" else "M1")):
            pred = json.loads(json.dumps(self.pred))
            change(pred["network_runs"])
            with self.assertRaises(AssertionError):
                MF.network_plan(pred)
        pred = json.loads(json.dumps(self.pred))
        next(x for x in pred["instances"] if x["seed"] == 8506)["room_K3"] = False
        with self.assertRaises(AssertionError):
            MF.network_plan(pred)

    def rehearsal(self):
        xs = []
        for s in CC.REHEARSAL_SEEDS:
            for m in CC.MEMBERS:
                x = synthetic_instance(m, s, {"a": 1, "b": 2})
                x.update(Q1=5, Q2=5)
                xs.append(x)
        return dict(mode="rehearsal", instances=xs, network_runs=CP.rehearsal_runs(xs))

    def test_rehearsal_placement(self):
        pred = self.rehearsal()
        p = MF.network_plan(pred)["rehearsal"]["R-N"]
        self.assertEqual(len(p), 22)
        home = {(j["member"], j["kind"]): j["seed"] for j in p if j["kind"] != "noisy"}
        self.assertEqual({m: home[(m, "quiet")] for m in CC.MEMBERS}, dict(X1=8303, X2=8303, F2=8303, F4=8306, F3=8306))
        self.assertEqual({m: home[(m, "untrained")] for m in CC.MEMBERS}, {m: home[(m, "quiet")] for m in CC.MEMBERS})
        self.assertEqual(sorted(j["noise_seed"] for j in p if j["kind"] == "noisy"), sorted(CC.REHEARSAL_NOISE.values()))
        moved = json.loads(json.dumps(pred))
        r = next(r for r in moved["network_runs"] if r["id"] == "8303-X1-quiet")
        r.update(id="8306-X1-quiet", seed=8306)
        with self.assertRaises(AssertionError):
            MF.network_plan(moved)

    def test_network_stage_guards(self):
        class Launch:
            fills_argv = True

            def __call__(self, d, name, jobs):
                return [j["id"] for j in jobs]
        limits = {r["id"]: 1000 for r in self.pred["network_runs"]}
        ended = lambda d, st: {"x": "complete"}
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(AssertionError):                                   # no limit from the amendment
                MF.network_stage(self.pred, "M1", "Q", d, {}, Launch(), ended)
            with self.assertRaises(AssertionError):                                   # no command
                MF.network_stage(self.pred, "M1", "Q", d, limits, lambda *a: None, ended)
            with self.assertRaises(AssertionError):                                   # N1 before Q ended
                MF.network_stage(self.pred, "M1", "N1", d, limits, Launch(), lambda d, st: {"x": "running"})
            got = MF.network_stage(self.pred, "M1", "Q", d, limits, Launch(), ended)
            self.assertEqual(got, [j["id"] for j in MF.network_plan(self.pred)["M1"]["Q"]])
            with self.assertRaises(AssertionError):                                   # started once only
                MF.network_stage(self.pred, "M1", "Q", d, limits, Launch(), ended)
            self.assertEqual(json.loads((Path(d) / "JOBS_Q.json").read_text())[0]["limit_s"], 1000)


class NoiseSensitivity(unittest.TestCase):
    """Section 7's declared comparison: the record regenerated with the larger constants, then restored."""

    def test_patched_then_restored(self):
        import c4
        rec = dict(instances=[dict(seed=8303, member="F2", room_K3=True), dict(seed=8303, member="X1", room_K3=False)])
        seen = []

        def regenerate():
            seen.append(dict(c4.DECISION5))
            return dict(instances=[dict(seed=8303, member="F2", room_K3=False), dict(seed=8303, member="X1", room_K3=False)])
        r = CP.noise_sensitivity(rec, regenerate, dict(between_mV=0.2, within_mV=0.05, per_dose_mV=0.009))
        self.assertEqual(seen, [dict(between_mV=0.2, within_mV=0.094, per_dose_mV=0.009)])
        self.assertEqual(c4.DECISION5, dict(between_mV=0.111, within_mV=0.094, per_dose_mV=0.009))
        self.assertFalse(r["per_instance"]["8303-F2"]["keeps_room"])
        self.assertTrue(r["per_instance"]["8303-X1"]["keeps_room"].startswith("no meaning"))
        self.assertTrue(r["what"].endswith("counts nothing"))
        with self.assertRaises(AssertionError):
            CP.noise_sensitivity(rec, regenerate, dict(b=1))


if __name__ == "__main__":
    unittest.main(verbosity=1)
