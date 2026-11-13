"""Isolated authority/boundary controls, never a trajectory or shortened v4."""
import io
import json
import unittest
from authority import Authority
from boundary import truth_flags
from controller import Supervisor, Observation


class SyntheticTests(unittest.TestCase):
    def authority(self):
        events = io.StringIO()
        a = Authority(events)
        return a, events

    def test_root_time_is_fixed_and_not_inferred(self):
        a, events = self.authority()
        self.assertFalse(a.tick(665))
        self.assertIsNone(a.offer(665, 1, 'recovery-unguaranteed', 0))
        self.assertTrue(a.tick(666))
        self.assertFalse(a.tick(666))
        self.assertFalse(a.tick(667))
        root = json.loads(events.getvalue())
        self.assertEqual((root['issued'], root['expires'], root['bound']), (666, 1640, 150))

    def test_missed_root_event_cannot_be_chosen_afterward(self):
        a, _ = self.authority()
        self.assertFalse(a.tick(667))
        self.assertIsNone(a.offer(700, 1, 'recovery-unguaranteed', 0))

    def test_tokens_bind_current_generation_and_phase_completion(self):
        a, _ = self.authority()
        a.tick(666)
        token = a.offer(700, 3, 'recovery-unguaranteed', 0)
        self.assertEqual((token.generation, token.issued, token.bound, token.decisions), (3, 700, 150, 8))
        self.assertIsNone(a.offer(701, 3, 'authorized-conditional', 1))
        token = a.offer(702, 3, 'authorized-conditional', 0)
        self.assertEqual((token.generation, token.issued), (4, 702))

    def test_token_budget_and_terminal_boundary(self):
        a, _ = self.authority()
        a.tick(666)
        for i in range(82):
            self.assertIsNotNone(a.offer(700+i, i+1, 'recovery-unguaranteed', 0))
        self.assertIsNone(a.offer(800, 83, 'recovery-unguaranteed', 0))
        self.assertEqual(len(a.tokens), 82)
        b, _ = self.authority()
        b.tick(666)
        self.assertIsNone(b.offer(1320, 1, 'recovery-unguaranteed', 0))

    def test_root_alone_does_not_authorize_insufficient_entry(self):
        a, _ = self.authority()
        a.tick(666)
        with Supervisor(now=700, repair_budget=2, phase_budget=1) as s:
            p = a.offer(700, s.generation, s.mode, s.remaining)
            decision = s.decide(Observation(700, 0, 140, False), p)
            self.assertEqual((decision.mode, decision.action), ('recovery-unguaranteed', 'repair'))
            self.assertIsNone(s.permit)

    def test_admission_after_delivery_does_not_claim_predelivery_safety(self):
        a, _ = self.authority()
        a.tick(666)
        with Supervisor(now=700, repair_budget=2, phase_budget=1, pending=True) as s:
            p = a.offer(700, s.generation, s.mode, s.remaining)
            d = s.decide(Observation(700, 42, 140, True), p)
            self.assertEqual((d.mode, d.lower), ('authorized-conditional', 260))
            self.assertFalse(d.sampled_safe_pre)

    def test_false_claims_use_the_correct_boundary(self):
        flags = truth_flags(700, 40, 260, True, False, False, True)
        self.assertEqual((flags['truth_unsafe_pre'], flags['truth_unsafe_post']), (1, 0))
        self.assertEqual((flags['truth_false_guarantee_pre'], flags['truth_false_guarantee_post']), (0, 0))
        self.assertEqual(truth_flags(700, 40, 260, True, False, True, True)['truth_false_guarantee_pre'], 1)

    def test_detection_not_clearance_counts_hidden_danger(self):
        flags = truth_flags(700, -40, 180, True, False, False, False)
        self.assertEqual(flags['truth_undetected'], 0)
        self.assertEqual(truth_flags(700, -40, 180, False, False, False, False)['truth_undetected'], 1)

    def test_authority_journal_retains_one_root_and_all_tokens(self):
        a, events = self.authority()
        a.tick(666)
        a.offer(700, 4, 'recovery-unguaranteed', 0)
        a.offer(708, 4, 'authorized-conditional', 0)
        records = [json.loads(line) for line in events.getvalue().splitlines()]
        self.assertEqual(records, [a.root, *a.tokens])
        self.assertEqual(a.snapshot(), {'root': records[0], 'tokens': records[1:]})


if __name__ == '__main__':
    unittest.main()
