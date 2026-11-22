"""Integration test, no simulation: the prediction record of synthetic instances (campaign_predict.predicted_words on
the frozen synthetic chains of test_family_predict), the network code's synthetic run folders (test_family_reads.
synthesise: family_net's plan, a binary raw trace parsed by the frozen measure.Trace, result.json, record.json), read
by family_reads.collect, then analysis.run (the reproduction check, the claims, the comparisons). All 15 instances of
the campaign and the rehearsal set (8303 and 8306, the five members).

  PYTHONPATH=FUP/dev:PREP/dev:FF/dev:.:NET python -B test_integration.py REPO GEN NET
      NET: research/function-family-campaign/net of research/function-family-campaign-net
"""
import json
import os
import shutil
from pathlib import Path
import sys
import tempfile
import unittest

REPO, GEN, NET = sys.argv.pop(1), sys.argv.pop(1), Path(sys.argv.pop(1))
sys.path.insert(0, str(NET))
import campaign_common as CC                                     # noqa: E402
import family_predict as FP                                      # noqa: E402
FP.paths(REPO, GEN)
FP.mods()
import analysis as A                                             # noqa: E402
import campaign_predict as CP                                    # noqa: E402
saved = sys.argv[1:]
sys.argv[1:] = [REPO, GEN]
import test_family_predict as TFP                                # noqa: E402  (the frozen synthetic chains)
sys.argv[1:] = [REPO]
import test_family_reads as TR                                   # noqa: E402  (the network code's synthetic runs)
sys.argv[1:] = saved
import family_reads as R                                         # noqa: E402

NEED = 3                                                         # the synthetic chains' need on every port and line
PORTS = [{"a": 1, "b": 1}, {"a": 2, "b": 1}, {"a": 1, "b": 2}]
CONTROL = dict(skew="skew", untrained="untrained")


def instance(member, seed, up, room, machine):
    x, _ = TFP.Synthetic("chain").chain(member, up)
    kd = FP.kinds(member)
    uport = {c: up[c] for c, k in kd.items() if k == "unary"}
    n = {c: NEED for c in kd}
    n.update({f"c{FP.LINE_PORT[c]}": NEED for c in kd})
    return dict(seed=seed, member=member, machine=machine, measured=True, eligible=True, room_K3=room, needs=n, unary_ports=uport,
                Q1=x["Q1"], Q2=x["Q2"], guarded=x["guarded"], epsilon=x["epsilon"], budgets=x["budgets"], observation=x["observation"],
                predicted=CP.predicted_words(member, uport, x["observation"]))


def record(mode):
    if mode == "campaign":
        d = CC.draw()
        xs = []
        for m in CC.MEMBERS:
            for i, s in enumerate(sorted(s for s in CC.SEEDS if d[s] == m)):
                xs.append(instance(m, s, PORTS[i], m in ("X1", "X2") or i == 0, CC.machine_of(s)))
        runs = CC.network_runs(xs)
    else:
        xs = [instance(m, s, PORTS[i], True, None) for i, s in enumerate(CC.REHEARSAL_SEEDS) for m in CC.MEMBERS]
        runs = CP.rehearsal_runs(xs)
    return dict(what="synthetic", mode=mode, constants=dict(between_mV=0.111, within_mV=0.094, per_dose_mV=0.009),
                instances=sorted(xs, key=lambda x: x["seed"]), network_runs=runs)


def write_runs(pred, d, status=None, beh=None, move=None):
    """Every network run of the record as a synthetic folder, with STATE.json; status/beh/move: {run id: ...}."""
    status, beh, move = status or {}, beh or {}, move or {}
    inst = {(x["seed"], x["member"]): x for x in pred["instances"]}
    st = {}
    for r in pred["network_runs"]:
        x = inst[(r["seed"], r["member"])]
        ctl = CONTROL.get(r["control"])
        b = beh[r["id"]](x, ctl) if r["id"] in beh else None
        TR.synthesise(d / r["id"], x["member"], x["needs"], x["unary_ports"], ctl, beh=b, noise="none" if r["noise"] == "none" else "injected",
                      move=move.get(r["id"]), seed=r["seed"])
        st[r["id"]] = dict(status=status.get(r["id"], "complete"))
    (d / "NET").mkdir()
    (d / "NET" / "STATE.json").write_text(json.dumps(dict(runs=st)))


def collect(pred, d):
    """The reader's records, with the record file given: `observation` is then the RUN's (family_reads.run_observation)."""
    path = d / "PREDICTED.json"
    path.write_text(CC.record_text(pred))
    return R.collect([r["id"] for r in pred["network_runs"]], d, with_rows=True, predicted=path)


def flip_first_fire(cell):
    """The run's behaviour with the first FIRE of `cell` in layer 1 replaced by one more silent write."""
    def f(x, ctl):
        plan, slots, b = TR.behaviour(x["member"], x["needs"], x["unary_ports"], ctl)
        i = next(i for i, (s, v) in enumerate(zip(slots, b)) if s["stage"] == "layer 1" and cell in v and v[cell][0])
        ports = FP.wiring(x["member"], x["unary_ports"])[cell].values()
        b[i] = dict(b[i], **{cell: (False, {p: 1 for p in ports})})
        return b
    return f


def output(stage, pattern, cell, value):
    def f(x, ctl):
        plan, slots, b = TR.behaviour(x["member"], x["needs"], x["unary_ports"], ctl)
        i = next(i for i, s in enumerate(slots) if s["stage"] == stage and "".join(sorted(s["inputs"])) == pattern)
        b[i] = dict(b[i], **{cell: (value, {})})
        return b
    return f


class EndToEnd(unittest.TestCase):
    mode = "campaign"

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.d = Path(self.tmp.name)
        self.pred = record(self.mode)
        self.text = CC.record_text(self.pred)

    def tearDown(self):
        self.tmp.cleanup()

    def analyse(self, **kw):
        write_runs(self.pred, self.d, **kw)
        self.runs = collect(self.pred, self.d)
        return A.run(self.text, json.loads(self.text), self.runs)

    def predicted_mirror(self, x):
        """The mirror on the instance's own predicted observation: the prediction's M8 verdicts."""
        import comparisons as C
        _, _, spec, *_ = FP.mods()
        mv = FP.mirror_verdicts(spec.load(FP.raw_spec(C.run_instance(x, x["observation"]), "pred", "test")))
        return {K: (v["checks"], sorted(map(tuple, v["failing"]))) for K, v in mv.items()}

    def test_all_as_predicted(self):
        r = self.analyse()
        self.assertTrue(r["prediction_record_reproduced"])
        self.assertEqual(r["missing"], [])
        c = r["claims"]
        if self.mode == "campaign":
            self.assertEqual(len(self.pred["instances"]), 15)
            self.assertEqual(c["primary"]["family"], "established for the family")
            self.assertTrue(c["N-out"]["verdict"].startswith("established, pooled over"))
            self.assertTrue(c["N-own"]["verdict"].startswith("established, pooled over"))
            self.assertTrue(c["N-word"]["verdict"].startswith("established, pooled over"))
        else:
            self.assertTrue(all(v["verdict"] == "held on one instance, not established" for v in c["primary"]["per_member"].values()))
            self.assertNotIn("refuted", c["primary"]["family"])
            self.assertNotEqual(c["N-out"]["verdict"], "refuted")
        self.assertEqual(c["G"]["verdict"], "held")
        self.assertTrue(all(v["verdict"] == "held" for v in c["U"].values()))
        self.assertEqual(c["S"]["verdict"], "held")
        for m in CC.MEMBERS:
            for rid, h in c["H"]["per_member"][m].items():
                self.assertIsInstance(h, dict, rid)
                self.assertEqual((h["undelivered"], h["c_fire_outside"], h["late_fires"]), (0, 0, 0), rid)
                self.assertEqual(h["arrivals_not_routed"], 0, rid)
        comp = r["comparisons"]
        for m in CC.MEMBERS:
            for rid, v in comp["M8"][m].items():
                # M8 reads the RUN's observation (family_reads.run_observation), not the predicted one
                self.assertNotEqual(self.runs[rid]["observation"], self.runs[rid]["observation_predicted"], rid)
                # The synthetic traces carry no calibrated q (flat voltages): only the calibration checker fails,
                # validity and separation hold on the run's dates and emissions
                for K, w in v["mirror"].items():
                    self.assertEqual({f[0] for f in w["failing"]}, {"checkCascadeCalibrationOneSided"}, (rid, K))
            for rid, v in comp["M3"][m].items():
                self.assertIsInstance(v, dict, rid)
        self.assertTrue(all(v == {} for v in comp["M6"]["word_and_word_prime_differ"].values()))

    def test_M8_differs_when_the_trace_differs(self):
        """A run whose trace differs from the prediction (one layer-1 FIRE of a replaced by a silent write) gives an M8
        result different from the prediction's, and from the as-predicted run's."""
        rid = next(r["id"] for r in self.pred["network_runs"] if r["member"] == "F2" and r["control"] == "skew")
        x = next(y for y in self.pred["instances"] if y["seed"] == int(rid.split("-")[0]))
        res = lambda r: {K: (w["checks"], sorted(map(tuple, w["failing"]))) for K, w in r["comparisons"]["M8"]["F2"][rid]["mirror"].items()}
        same = res(self.analyse())
        obs_same = self.runs[rid]["observation"]
        shutil.rmtree(self.d)
        self.d.mkdir()
        bad = res(self.analyse(beh={rid: flip_first_fire("a")}))
        obs_bad = self.runs[rid]["observation"]
        pred = self.predicted_mirror(x)
        self.assertEqual({K: v[0] for K, v in pred.items()}, dict(K0=True, K3=True))
        self.assertNotEqual(bad, pred)                                  # the coordinator's case
        self.assertNotEqual(obs_bad["firstTrain"], obs_same["firstTrain"])   # the replaced FIRE reaches the run's observation
        # Reported, not asserted: on these synthetic traces calibration already fails on every run (flat q), so the
        # mirror's failure list is the same with and without the replaced FIRE.
        print(f"\n  M8 {rid} ({self.mode}): prediction's checks {dict((K, v[0]) for K, v in pred.items())}; "
              f"run's checks {dict((K, v[0]) for K, v in bad.items())}; failing checkers of the run "
              f"{sorted({f[0] for v in bad.values() for f in v[1]})}; same failure list as the as-predicted run: {bad == same}", file=sys.stderr)

    def test_wrong_letter(self):
        rid = next(r["id"] for r in self.pred["network_runs"] if r["member"] == "F2" and r["control"] == "skew")
        c = self.analyse(beh={rid: flip_first_fire("a")})["claims"]
        self.assertEqual(c["primary"]["per_member"]["F2"]["verdict"], "refuted")
        self.assertTrue(c["primary"]["family"].startswith("refuted (F2)"))
        self.assertTrue(any(b["instance"] == int(rid.split("-")[0]) for b in c["primary"]["per_member"]["F2"]["discrepancies"]))

    def test_wrong_output_noisy(self):
        rid = next(r["id"] for r in self.pred["network_runs"] if r["member"] == "X1" and r["noise"] != "none")
        c = self.analyse(beh={rid: output("test", "A", "c", False)})["claims"]
        self.assertEqual(c["N-out"]["verdict"], "refuted")
        self.assertEqual(c["N-out"]["by"]["c"]["failures"], [rid])
        self.assertNotIn("refuted", c["primary"]["family"])

    def test_skew_and_untrained(self):
        sk = next(r["id"] for r in self.pred["network_runs"] if r["member"] == "F3" and r["control"] == "skew")
        un = next(r["id"] for r in self.pred["network_runs"] if r["member"] == "X2" and r["control"] == "untrained")
        c = self.analyse(beh={sk: output("skew control", "BC", "b", True), un: output("test", "AB", "a", True)})["claims"]
        self.assertEqual(c["S"]["verdict"], "refuted")
        self.assertEqual(c["U"]["X2"]["verdict"], "refuted")
        self.assertEqual(c["U"]["X1"]["verdict"], "held")

    def test_G(self):
        rid = next(r["id"] for r in self.pred["network_runs"] if r["member"] == "F2" and r["control"] == "skew")
        x = next(x for x in self.pred["instances"] if x["member"] == "F2" and x["seed"] == int(rid.split("-")[0]))
        plan, slots, b = TR.behaviour("F2", x["needs"], {}, "skew")
        i = next(i for i, s in enumerate(slots) if s["stage"] == "test" and "a" in b[i])
        c = self.analyse(move={rid: (i, "a", 1, 0.5)})["claims"]
        self.assertEqual(c["G"]["verdict"], "refuted")
        self.assertTrue(all(g["run"] == rid for g in c["G"]["failures"]))

    def test_missing_run(self):
        rid = next(r["id"] for r in self.pred["network_runs"] if r["member"] == "F4" and r["control"] == "skew")
        r = self.analyse(status={rid: "running"})
        self.assertIn(rid, r["missing"])
        if self.mode == "campaign":
            self.assertEqual(r["claims"]["primary"]["per_member"]["F4"]["verdict"], "established")      # 2 of 3 remain
        else:
            self.assertEqual(r["claims"]["primary"]["per_member"]["F4"]["verdict"], "not established")

    def test_tampered_record(self):
        x = self.pred["instances"][0]
        bad = json.loads(self.text)
        bad["instances"][0]["needs"][next(iter(x["needs"]))] += 1
        write_runs(self.pred, self.d)
        r = A.run(CC.record_text(bad), self.pred, collect(self.pred, self.d))
        self.assertFalse(r["prediction_record_reproduced"])
        self.assertTrue(all(v.startswith("not established") for v in r["claims"].values()))


class Rehearsal(EndToEnd):
    mode = "rehearsal"


if __name__ == "__main__":
    unittest.main(verbosity=2)
