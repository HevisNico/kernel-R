"""Small synthetic checks only. Never calls trajectory/main or registered run."""
import io
import tempfile
import unittest
from controllers import Baseline, Contract, Observation
from experiment import plant_step, sense
from evaluate import metrics


class Synthetic(unittest.TestCase):
    def test_pre_delivery_violation_is_not_erased(self):
        pre, post = plant_step(101, 5, True)
        self.assertEqual((pre, post), (96, 316))
        self.assertLess(Observation(7, 97, 5, True).lower_before, 100)
        self.assertGreater(Observation(7, 97, 5, True).lower_after, 100)

    def test_signed_failure_and_saturation(self):
        self.assertEqual(plant_step(3, 8, False), (-5, -5))
        self.assertEqual(plant_step(650, 1, True), (649, 660))
        self.assertEqual(Observation(0, -300, 8, True).lower_after, -82)

    def test_bounded_sensor(self):
        for t in range(17):
            x, rate, ex, er = sense(t, -73, 42)
            self.assertEqual((x, rate), (-73+ex, 42+er))
            self.assertLessEqual(abs(ex), 2)
            self.assertLessEqual(abs(er), 1)

    def test_baseline_threshold_and_failure_memory(self):
        naive, prudent = Baseline('naive'), Baseline('prudent')
        self.assertEqual(naive.decide(Observation(3, 146, 11, False)).delay, 40)
        self.assertEqual(naive.decide(Observation(3, 145, 11, False)).action, 'write')
        self.assertEqual(naive.decide(Observation(3, 98, 11, True)).delay, 1)
        self.assertEqual(prudent.decide(Observation(3, 302, 11, False)).delay, 1)

    def test_native_lean_decisions_and_reopening(self):
        with tempfile.TemporaryFile(mode='w+') as errors:
            c = Contract(errors)
            try:
                d = c.decide(Observation(3, 302, 10, False))
                self.assertEqual((d.lower, d.action, d.delay, d.reopened), (300, 'wait', 8, False))
                d = c.decide(Observation(4, 140, 20, False))
                self.assertEqual((d.action, d.delay, d.reopened), ('write', 1, True))
                self.assertEqual(c.decide(Observation(5, 123, 20, False)).action, 'refuse')
                d = c.decide(Observation(6, -300, 20, True))
                self.assertEqual((d.lower, d.action), (-82, 'refuse'))
            finally:
                c.close()

    def test_undetected_metric_uses_detection_before_delivery(self):
        rows = []
        for t, pre, detected in [(0, 440, 0), (1, 90, 0), (2, 80, 1), (3, 120, 0)]:
            rows.append(dict(t=t, pre=pre, post=300, alarm_detected=detected,
                             probe=int(t%2==0), command=0, delivery=0, reopened=0,
                             rate=10, refused=0))
        result = metrics(rows)
        self.assertEqual((result['pre_unsafe'], result['post_unsafe'], result['undetected'],
                          result['longest_undetected']), (2, 0, 1, 1))


if __name__ == '__main__':
    unittest.main()
