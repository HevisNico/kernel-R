"""Synthetic inputs only: never runs the registered plant trajectories."""
import tempfile
import unittest
from controllers import Baseline, Contract, Observation
from experiment import plant_step, sense
from evaluate import metrics


class Synthetic(unittest.TestCase):
    def test_delivery_order_and_signed_reserve(self):
        self.assertEqual(plant_step(101, 5, True), (96, 316))
        self.assertEqual(plant_step(3, 8, False), (-5, -5))
        self.assertEqual(Observation(0, -300, 8, True).lower_after, -82)

    def test_bounded_sensor(self):
        for t in range(17):
            x, y, ex, ey = sense(t, -73, 42)
            self.assertEqual((x, y), (-73+ex, 42+ey))
            self.assertLessEqual(abs(ex), 2)
            self.assertLessEqual(abs(ey), 1)

    def test_baselines_use_measurements_not_old_fixed_threshold(self):
        naive, prudent = Baseline('naive'), Baseline('prudent')
        d = naive.decide(Observation(3, 152, 10, False))
        self.assertEqual((d.bound, d.action, d.delay), (21, 'wait', 40))
        d = naive.decide(Observation(3, 152, 20, False))
        self.assertEqual((d.bound, d.action, d.delay), (31, 'write', 1))
        self.assertEqual(prudent.decide(Observation(3, 402, 8, False)).delay, 1)
        self.assertEqual(naive.decide(Observation(3, 98, 8, True)).delay, 1)

    def test_native_adaptive_handoff_and_reopening(self):
        with tempfile.TemporaryFile(mode='w+') as errors:
            c = Contract(errors)
            try:
                d = c.decide(Observation(0, 302, 10, False))
                self.assertEqual((d.lower, d.bound, d.action, d.delay), (300, 21, 'wait', 7))
                # A noisy fresh lower is weaker than the certified handoff.
                d = c.decide(Observation(7, 150, 20, False))
                self.assertEqual((d.carried, d.lower, d.bound), (153, 153, 31))
                self.assertEqual((d.action, d.delay, d.reopened, d.invalidated), ('write', 1, True, False))
                d = c.decide(Observation(8, 340, 20, True))
                self.assertEqual(d.carried, 342)
                self.assertFalse(d.reopened)
            finally:
                c.close()

    def test_ambiguous_exceedance_is_not_violation(self):
        with tempfile.TemporaryFile(mode='w+') as errors:
            c = Contract(errors)
            try:
                c.decide(Observation(0, 302, 9, False))  # ceiling 20; wait 8
                d = c.decide(Observation(8, 160, 21, False))  # interval [20,22]
                self.assertTrue(d.ambiguous)
                self.assertFalse(d.invalidated)
            finally:
                c.close()

    def test_demonstrated_violation_discards_carry_and_refuses(self):
        with tempfile.TemporaryFile(mode='w+') as errors:
            c = Contract(errors)
            try:
                c.decide(Observation(0, 302, 9, False))
                d = c.decide(Observation(8, 120, 23, False))  # lower rate 22 > old 20
                self.assertEqual((d.lower, d.invalidated, d.action), (118, True, 'refuse'))
            finally:
                c.close()

    def test_unknown_high_rate_or_negative_reserve_is_not_accepted(self):
        for x,y in [(400, 210), (-4, 10)]:
            with tempfile.TemporaryFile(mode='w+') as errors:
                c = Contract(errors)
                try:
                    self.assertEqual(c.decide(Observation(0,x,y,False)).action, 'refuse')
                finally:
                    c.close()

    def test_undetected_metric(self):
        rows=[]
        for t,pre,detected in [(0,440,0),(1,90,0),(2,80,1),(3,120,0)]:
            rows.append(dict(t=t,pre=pre,post=300,alarm_detected=detected,probe=int(t%2==0),
                             command=0,delivery=0,reopened=0,rate=10,refused=0,
                             ambiguous=0,invalidated=0,bound=21))
        m=metrics(rows)
        self.assertEqual((m['pre_unsafe'],m['post_unsafe'],m['undetected'],m['longest_undetected']), (2,0,1,1))


if __name__=='__main__':
    unittest.main()
