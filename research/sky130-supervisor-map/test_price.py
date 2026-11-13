"""Synthetic arithmetic controls; no registered scenario or circuit replay."""
import copy
import unittest

from price import analyze


def example():
    return dict(bounds_mV=dict(S=100, H=150, Dmin=220, Dmax=220, C=660, epsilon=2),
                horizon_periods=264, probe_spacing_periods=2,
                initial_reserve_mV=440, terminal_reserve_mV=440)


class PriceTests(unittest.TestCase):
    def test_exact_guard_and_equal_inventory_ledger(self):
        result = analyze(example())
        self.assertTrue(result["all_arithmetic_guards_pass"])
        self.assertEqual(result["maximum_wait_periods_from_capacity"], 2)
        self.assertEqual(result["conservation"]["necessary_write_count_using_Dmax"], 180)
        self.assertTrue(result["conservation"]["exact_target_for_exact_dose"])
        ledger = result["conditional_ledger"]
        self.assertEqual((ledger["spaced_decision_probes"], ledger["prudent_decision_probes"]), (132, 264))
        self.assertEqual((ledger["spaced_cost"], ledger["prudent_cost"]), ("2197", "2329"))
        self.assertEqual(ledger["difference_from_probe_counts_only"], "132")

    def test_capacity_cannot_cover_wait_and_repair(self):
        spec = example()
        spec["bounds_mV"]["C"] = 549
        result = analyze(spec)
        self.assertFalse(result["guards"]["selected_spacing_plus_one_repair_period"])
        spec["bounds_mV"]["C"] = 403
        spec["initial_reserve_mV"] = spec["terminal_reserve_mV"] = 400
        result = analyze(spec)
        self.assertFalse(result["guards"]["one_wait_plus_one_repair_period"])

    def test_broad_dose_bound_cannot_pay_worst_loss(self):
        spec = example()
        spec["bounds_mV"]["Dmin"] = 149
        result = analyze(spec)
        self.assertFalse(result["guards"]["independent_box_repair_balance"])
        self.assertTrue(result["conservation"]["gross_count_is_not_a_schedule_or_cost_upper_bound"])

    def test_maintenance_silence_can_close_otherwise_valid_write_interval(self):
        spec = example()
        spec["bounds_mV"]["M"] = 253
        result = analyze(spec)
        self.assertFalse(result["guards"]["fresh_ready_write_interval_nonempty"])
        self.assertEqual(result["guard_values_mV"]["minimum_fresh_write_upper"], "254")

    def test_invalid_dose_interval_and_nonfinite_inputs_rejected(self):
        for changes in ({"Dmin": 221}, {"Dmin": 0}, {"H": "nan"}, {"epsilon": -1}, {"Dmax": True}):
            with self.subTest(changes=changes):
                spec = example()
                spec["bounds_mV"].update(changes)
                with self.assertRaises(ValueError):
                    analyze(spec)

    def test_interval_doses_have_distinct_necessary_and_gross_counts(self):
        spec = dict(bounds_mV=dict(S=0, H=3, Dmin=2, Dmax=4, C=20, epsilon=0),
                    horizon_periods=10, probe_spacing_periods=1,
                    initial_reserve_mV=10, terminal_reserve_mV=10)
        result = analyze(spec)["conservation"]
        self.assertEqual(result["necessary_write_count_using_Dmax"], 8)
        self.assertEqual(result["gross_count_using_Dmin_without_saturation"], 15)
        self.assertFalse(result["at_most_one_maintenance_per_period_count_condition"])
        self.assertEqual(result["unsaturated_terminal_interval_mV"], ["10", "40"])

    def test_rounding_extra_stock_is_visible(self):
        spec = example()
        spec["horizon_periods"] = 1
        result = analyze(spec)["conservation"]
        self.assertEqual(result["common_write_count"], 1)
        self.assertEqual(result["unsaturated_terminal_interval_mV"], ["510", "510"])
        self.assertFalse(result["exact_target_for_exact_dose"])

    def test_subunit_quantities_are_exact(self):
        spec = dict(bounds_mV=dict(S="0", H="0.06", Dmin="1.33", Dmax="1.35", C="3.00", epsilon="0.01"),
                    horizon_periods=10, probe_spacing_periods=3,
                    initial_reserve_mV="2", terminal_reserve_mV="2")
        result = analyze(spec)
        self.assertEqual(result["bounds_mV"]["H"], "3/50")
        self.assertEqual(result["guard_values_mV"]["worst_fresh_lower_at_capacity"], "149/50")
        self.assertEqual(result["conditional_ledger"]["spaced_decision_probes"], 4)

    def test_zero_loss_and_zero_horizon_have_no_division_by_zero(self):
        spec = example()
        spec["bounds_mV"]["H"] = 0
        spec["horizon_periods"] = 0
        spec["prices"] = dict(probe=0, maintenance=0, service=0)
        result = analyze(spec)
        self.assertIsNone(result["maximum_wait_periods_from_capacity"])
        self.assertEqual(result["conservation"]["common_write_count"], 0)
        self.assertIsNone(result["conditional_ledger"]["difference_fraction_of_prudent"])

    def test_bad_count_price_or_inventory_rejected(self):
        for changes in ({"probe_spacing_periods": 0}, {"horizon_periods": 1.5},
                        {"initial_reserve_mV": 661}, {"terminal_reserve_mV": 99},
                        {"prices": {"probe": -1}}, {"common_maintenance_count": -1}):
            with self.subTest(changes=changes):
                spec = copy.deepcopy(example())
                spec.update(changes)
                with self.assertRaises(ValueError):
                    analyze(spec)


if __name__ == "__main__":
    unittest.main()
