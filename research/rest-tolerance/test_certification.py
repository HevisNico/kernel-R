from dataclasses import replace
from fractions import Fraction as Q
import unittest

from evidence import PortEvidence, Read
import rule_a1_delta
import status3_delta


def port():
    silent = Read("0", "0.1", "0.1", "0", False, 0, 1, 0)
    fire = Read("0.04", "0.1", "0.1", "0", True, 1, 0, 0, "0.76")
    return PortEvidence(1, "1", "0.04", "0.001", "0.0003", "0", "0.0005", (silent, fire), True)


class CertificationTest(unittest.TestCase):
    rules = (status3_delta, rule_a1_delta)

    def test_sub_rest_enclosure_and_both_endpoint_equalities(self):
        p = port()
        p = replace(p, reads=(replace(p.reads[0], c_pre_lo="0.0999998"),
                              replace(p.reads[1], c_pre_hi="0.1001")))
        for rule in self.rules:
            with self.subTest(rule=rule.__name__):
                self.assertIn("rest charge", rule.certify(p, 0, "0.0001").reasons)
                self.assertTrue(rule.certify(p, "0.0000002", "0.0001").eligible)
                self.assertIn("rest charge", rule.certify(p, "0.0000002", "0.00009").reasons)

    def test_rest_budget_omission_would_admit_ports_on_both_sides(self):
        p = replace(port(), base_a="0.0176")
        for rule in self.rules:
            with self.subTest(rule=rule.__name__):
                self.assertTrue(rule.certify(p, 0, 0).eligible)
                self.assertFalse(rule.certify(p, "0.001", 0).eligible)
                self.assertFalse(rule.certify(p, 0, "0.001").eligible)

    def test_exact_budgets_include_readout_and_threshold_allowances(self):
        p = port()
        s = status3_delta.certify(p, "0.00001", "0.0001")
        a = rule_a1_delta.certify(p, "0.00001", "0.0001")
        common = Q("0.02") - Q("0.0019") - Q(20, 17) * Q("0.0002")
        self.assertEqual(s.silence_room, common - Q("0.0009") - Q(1, 8000))
        self.assertEqual(a.silence_room, common - Q("0.0004") - Q(1, 8000))
        self.assertEqual(a.fire_room, common - Q("0.0009") - Q(20, 17) * Q("0.00001"))

    def test_strict_silence_and_inclusive_fire(self):
        p = port()
        fire_room = rule_a1_delta.certify(p, 0, 0).fire_room
        p = replace(p, base_a=Q(p.base_a) + fire_room)
        self.assertTrue(rule_a1_delta.certify(p, 0, 0).eligible)
        self.assertIn("FIRE room", rule_a1_delta.certify(p, "0.0000001", 0).reasons)
        self.assertFalse(status3_delta.certify(p, 0, 0).eligible)
        p = replace(p, base_a=Q(p.base_a) + rule_a1_delta.certify(p, 0, 0).silence_room)
        self.assertIn("silence room", rule_a1_delta.certify(p, 0, 0).reasons)

    def test_count_agreement_is_an_outcome(self):
        p = port()
        early = replace(p.reads[0], fired=True, latch_rises=1, selected_writes=0, fire_latency="0.8")
        late = replace(p.reads[1], fired=False, latch_rises=0, selected_writes=1)
        for rule in self.rules:
            for reads, count in [((early, p.reads[1]), 0), ((p.reads[0], late), None)]:
                result = rule.certify(replace(p, reads=reads), 0, 0)
                self.assertTrue(result.contradicted)
                self.assertEqual(result.first_fire, count)

    def test_observation_guards_and_target_prefix(self):
        p = port()
        cases = (
            (replace(p, same_cell=False), "same-cell check"),
            (replace(p, level0="0.95"), "threshold floor"),
            (replace(p, reads=(p.reads[0], replace(p.reads[1], latch_rises=2))), "multiple latch rises"),
            (replace(p, reads=(p.reads[0], replace(p.reads[1], other_writes=1))), "steering"),
        )
        for rule in self.rules:
            for evidence, reason in cases:
                self.assertIn(reason, rule.certify(evidence, 0, 0).reasons)
            self.assertTrue(rule.certify(replace(p, need=0, reads=(p.reads[1],)), 0, 0).eligible)
            self.assertTrue(rule.certify(replace(p, reads=p.reads + (None,)), 0, 0).eligible)

    def test_malformed_or_incomplete_evidence_fails(self):
        p = port()
        for rule in self.rules:
            for lo, hi in [("-0.1", 0), (0, "0.050000001"), (0, "NaN"), ("1/0", 0), (0.1, 0)]:
                with self.assertRaises(ValueError):
                    rule.certify(p, lo, hi)
            for reads in [(p.reads[0],),
                          (p.reads[0], replace(p.reads[1], fire_latency="0.759")),
                          (replace(p.reads[0], c_pre_lo="0.2"), p.reads[1])]:
                with self.assertRaises(ValueError):
                    rule.certify(replace(p, reads=reads), 0, 0)


if __name__ == "__main__":
    unittest.main()
