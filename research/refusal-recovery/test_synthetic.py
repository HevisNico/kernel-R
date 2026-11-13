"""Deterministic unit fixtures, not a preregistered performance campaign."""
import unittest
from dataclasses import replace
from controller import Observation, Permit, Supervisor


class RecoveryTests(unittest.TestCase):
    def test_negative_entry_five_repairs_then_external_resume(self):
        with Supervisor(now=0, repair_budget=5, phase_budget=1) as c:
            first = c.decide(Observation(0, -62, 149, False))
            self.assertEqual((first.action, first.lower, first.sampled_safe_pre),
                             ('repair', -64, False))
            for t in range(1, 5):
                d = c.decide(Observation(t, -212 + 70*(t-1), 149, True))
                self.assertEqual((d.action, d.mode, d.delay),
                                 ('repair', 'recovery-unguaranteed', 1))
                self.assertFalse(d.sampled_safe_pre)
            d = c.decide(Observation(5, 68, 149, True), Permit(1, 5, 85, 150, 2))
            self.assertEqual((d.mode, d.action, d.lower), ('authorized-conditional', 'write', 286))
            self.assertFalse(d.sampled_safe_pre)
            self.assertEqual((c.recovery_writes, c.fuel, c.probes, c.cost), (5, 0, 6, 66))
            d = c.decide(Observation(6, 138, 149, True))
            self.assertEqual((d.action, d.sampled_safe_pre), ('write', True))
            d = c.decide(Observation(7, 208, 149, True))
            self.assertEqual(d.action, 'exhausted')
            self.assertFalse(c.pending)
            self.assertLessEqual(c.cost, c.cost_limit)

    def test_later_violation_reopens_without_refunding_budget(self):
        with Supervisor(now=0, repair_budget=3, phase_budget=1) as c:
            d = c.decide(Observation(0, 288, 149, False), Permit(1, 0, 80, 150, 2))
            self.assertEqual(d.action, 'write')
            d = c.decide(Observation(1, 0, 201, True))
            self.assertTrue(d.invalidated)
            self.assertEqual((d.generation, d.action, d.mode), (2, 'repair', 'recovery-unguaranteed'))
            self.assertEqual((c.fuel, c.cost, c.permits_left), (2, 22, 0))
            for t in (2, 3):
                d = c.decide(Observation(t, -1000, 201, True))
                self.assertEqual(d.action, 'repair')
            d = c.decide(Observation(4, -1000, 201, True))
            self.assertEqual(d.action, 'exhausted')
            self.assertFalse(c.pending)
            self.assertEqual((c.recovery_writes, c.active_writes), (3, 1))
            self.assertLessEqual(c.cost, c.cost_limit)

    def test_missing_stale_mismatched_and_malformed_observations_fail_closed(self):
        bad = [None, Observation(1, 400, 10, False),
               Observation(0, 400, 10, False, measured_at=1),
               Observation(0, 400, 10, True), Observation(0, 400, -1, False)]
        for obs in bad:
            with self.subTest(obs=obs), Supervisor(now=0, repair_budget=2, phase_budget=1) as c:
                d = c.decide(obs)
                self.assertEqual((d.action, d.sampled_safe_pre), ('fault', False))
                self.assertEqual(c.cost, 1)
                self.assertIsNone(c.due)
                with self.assertRaises(RuntimeError):
                    c.decide(Observation(0, 400, 10, False))

    def test_permit_rejections_do_not_stop_fresh_probes(self):
        p = Permit(1, 0, 80, 150, 2)
        for bad in [replace(p, generation=0), replace(p, issued=1),
                    replace(p, expires=0), replace(p, bound=220),
                    replace(p, decisions=0), replace(p, decisions=9)]:
            with self.subTest(permit=bad), Supervisor(now=0, repair_budget=1, phase_budget=1) as c:
                d = c.decide(Observation(0, 288, 149, False), bad)
                self.assertEqual((d.action, d.delay), ('repair', 1))

    def test_budget_endpoint_never_sends_recovery_command(self):
        with Supervisor(now=0, repair_budget=0, phase_budget=0) as c:
            d = c.decide(Observation(0, -62, 140, False))
            self.assertEqual((d.action, c.cost), ('exhausted', 1))
            self.assertEqual(c.recovery_writes, 0)

    def test_safety_only_describes_measured_instant_without_permit(self):
        with Supervisor(now=0, repair_budget=1, phase_budget=0) as c:
            d = c.decide(Observation(0, 402, 140, False))
            self.assertTrue(d.sampled_safe_pre)
            self.assertEqual((d.action, d.mode), ('repair', 'recovery-unguaranteed'))

    def test_failed_delivery_not_invented(self):
        with Supervisor(now=0, repair_budget=2, phase_budget=0) as c:
            c.decide(Observation(0, -62, 140, False))
            d = c.decide(Observation(1, -202, 140, False))
            self.assertEqual(d.action, 'fault')
            self.assertFalse(d.sampled_safe_pre)

    def test_phase_budget_cannot_be_renewed_internally(self):
        with Supervisor(now=0, repair_budget=0, phase_budget=1) as c:
            c.decide(Observation(0, 288, 149, False), Permit(1, 0, 80, 150, 1))
            d = c.decide(Observation(1, 138, 149, True), Permit(2, 1, 81, 150, 1))
            self.assertEqual(d.action, 'exhausted')
            self.assertEqual((c.active_writes, c.permits_left), (1, 0))

    def test_new_generation_can_resume_and_then_be_revoked(self):
        with Supervisor(now=0, repair_budget=1, phase_budget=2) as c:
            c.decide(Observation(0, 288, 149, False), Permit(1, 0, 80, 150, 1))
            d = c.decide(Observation(1, 138, 149, True), Permit(2, 1, 81, 150, 2))
            self.assertEqual((d.generation, d.mode, d.action), (2, 'authorized-conditional', 'write'))
            self.assertEqual((c.probes, c.permits_left, c.fuel), (2, 0, 1))
            d = c.decide(Observation(2, 0, 201, True))
            self.assertEqual((d.generation, d.invalidated, d.action), (3, True, 'repair'))
            self.assertEqual((c.fuel, c.active_writes, c.recovery_writes), (0, 2, 1))
            d = c.decide(Observation(3, -1000, 201, True))
            self.assertEqual(d.action, 'exhausted')
            self.assertEqual(c.cost, 34)
            self.assertLessEqual(c.cost, c.cost_limit)


if __name__ == '__main__':
    unittest.main()
