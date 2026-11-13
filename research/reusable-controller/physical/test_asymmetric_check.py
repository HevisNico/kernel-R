import unittest
from fractions import Fraction as Q
import asymmetric_check as a


class DirectionalBudgets(unittest.TestCase):
    def test_upward_fire_error_does_not_penalize_silence(self):
        silent, fire = a.directional_bounds([0,.04,.20],[False,False,True],.002,.04)
        self.assertAlmostEqual(silent,.0004)
        self.assertEqual(fire,0)

    def test_downward_early_error_does_not_penalize_fire(self):
        silent, fire = a.directional_bounds([0,-.20,.08],[False,False,True],.002,.04)
        self.assertAlmostEqual(silent,.0004)
        self.assertAlmostEqual(fire,.0024)

    def test_fire_deficit_and_both_endpoint_errors_are_paid(self):
        silent, fire = a.directional_bounds([0,.04,.07],[True,False,True],.002,.04)
        self.assertAlmostEqual(silent,.0044)
        self.assertAlmostEqual(fire,.0144)

    def test_final_read_is_excluded_only_from_upper_bound(self):
        _, fire = a.directional_bounds([0,.04,-1],[False,False,True],.002,.04)
        self.assertAlmostEqual(fire,1.0824)

    def test_missing_or_misaligned_prefix_is_rejected(self):
        for y,fired in [([],[]),([0],[]),([float('nan')],[False])]:
            with self.assertRaises(a.source.CampaignError):a.directional_bounds(y,fired,.002,.04)

    def test_silence_strict_fire_nonstrict(self):
        self.assertFalse(a.room_gates(Q(0),Q(1)))
        self.assertTrue(a.room_gates(Q(1),Q(0)))
        self.assertFalse(a.room_gates(Q(1),Q(-1)))

    def test_empty_silence_prefix(self):
        silent,fire=a.directional_bounds([0],[True],.002,.04)
        self.assertEqual(silent,0)
        self.assertAlmostEqual(fire,.0044)


if __name__ == '__main__':unittest.main()
