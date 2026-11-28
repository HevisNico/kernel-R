"""The campaign entry's record rules, without simulation: python -B -m unittest tests/test_campaign.py

  1. first_failing names the first failing clause in the stated order, and None only when every clause holds;
  2. a record's eligible_K0 / room_K3 are never looser than the gate's own verdicts (an unmeasured StateBound fails);
  3. load() refuses a folder whose files differ from SHA256SUMS, or whose schema differs.
"""
import copy, json, sys, tempfile, unittest
from pathlib import Path

PKG = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PKG))
from invinst import campaign

OK = dict(measured=True, observed=dict(fired_absent=True, same_sample=True, silent_present=True),
          state_bound=dict(verdict=True), kernel=dict(K0=True, K3=True),
          mirror={K: {p: True for p in campaign.PREMISE_ORDER} for K in ("K0", "K3")},
          front_end_fits="not checked: skew or epsilon not set")


def changed(**kw):
    g = copy.deepcopy(OK)
    for k, v in kw.items():
        g[k] = v
    return g


class Campaign(unittest.TestCase):
    def test_first_failing(self):
        ff = campaign.first_failing
        self.assertIsNone(ff("ok", OK, "K0"))
        self.assertEqual(ff("timeout", None, "K0"), "run_timeout")
        self.assertEqual(ff("failed", None, "K3"), "run_failed")
        self.assertEqual(ff("ok", None, "K0"), "run_no_gate")
        self.assertEqual(ff("ok", changed(measured=False), "K0"), "not_measured")
        self.assertEqual(ff("ok", changed(observed=dict(OK["observed"], same_sample=False)), "K0"),
                         "observed:same_sample")
        self.assertEqual(ff("ok", changed(state_bound="not measured"), "K0"), "StateBound:not_measured")
        self.assertEqual(ff("ok", changed(state_bound=dict(verdict=False)), "K0"), "StateBound")
        self.assertEqual(ff("ok", changed(kernel=None), "K0"), "kernel:no_verdict")
        m = copy.deepcopy(OK["mirror"])
        m["K3"]["FiringBefore"] = m["K3"]["SilenceAfter"] = False
        g = changed(kernel=dict(K0=True, K3=False), mirror=m)
        self.assertIsNone(ff("ok", g, "K0"))
        self.assertEqual(ff("ok", g, "K3"), "kernel:SilenceAfter")
        self.assertEqual(ff("ok", changed(front_end_fits=dict(verdict=False)), "K0"), "FrontEndFits")

    def test_record_not_looser_than_gate(self):
        with tempfile.TemporaryDirectory() as d:
            out = Path(d)
            (out / "gates").mkdir()
            (out / "runs" / "1").mkdir(parents=True)
            g = changed(state_bound="not measured", eligible_K0=True, room_K3=True, attempts=[], margins=None,
                        measures=None, allowance=None, timing=None, kernel_agrees_with_mirror=True)
            (out / "gates" / "GATE_1.json").write_text(json.dumps(g))
            m = dict(measures=dict(machine_s_total=1.0, delta=0, etaH=0, etaM=0, etaJ=0, eps0=0, Q=0,
                                   emit_absent_tu=0, latch_delay_tu=0, same_sample=True,
                                   leak_above=dict(rate=0.5), leak_below=dict(rate=0.5)),
                     runs=dict(R1_absent=dict(finger=[0.0])))
            (out / "runs" / "1" / "MEASURE.json").write_text(json.dumps(m))
            r = campaign.record(out, 1, "ok")
            self.assertTrue(r["gate_eligible_K0"])           # the gate counts an unmeasured state bound as not failing
            self.assertFalse(r["eligible_K0"])               # the campaign does not
            self.assertEqual(r["first_failing_K0"], "StateBound:not_measured")

    def test_load_checks_sums_and_schema(self):
        with tempfile.TemporaryDirectory() as d:
            out = Path(d)
            (out / "INVERTERS.json").write_text(json.dumps(dict(schema=campaign.SCHEMA, records=[dict(seed=5)])))
            (out / "lean_build").mkdir()
            (out / "lean_build" / "x").write_text("not summed")
            self.assertEqual(campaign.write_sums(out), 1)
            self.assertEqual(list(campaign.load(out)), [5])
            (out / "INVERTERS.json").write_text(json.dumps(dict(schema="other", records=[])))
            with self.assertRaises(ValueError):
                campaign.load(out)
            campaign.write_sums(out)
            with self.assertRaises(ValueError):
                campaign.load(out)


if __name__ == "__main__":
    unittest.main()
