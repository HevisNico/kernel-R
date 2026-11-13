"""Exact phase-0 guard and conditional cost arithmetic; no circuit or trajectory.

Input JSON keys: bounds_mV (S,H,Dmin,Dmax,C,epsilon, optional M),
horizon_periods, probe_spacing_periods, initial_reserve_mV,
terminal_reserve_mV, optional common_maintenance_count, and optional prices
(probe=1, maintenance=10, service=1, terminal_observation=1).

M is a closed admissible upper-reserve ceiling that already includes any
strict threshold, timing and observation margins of the maintenance stimulus.
Numbers can be exact decimal or rational strings. No value is a physical bound
merely because it appears in this calculation. The ledger assumes feasible
plans with common maintenance count and terminal inventory; it proves neither.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path


def rational(value, name):
    if isinstance(value, bool):
        raise ValueError(name + " must be a finite rational number")
    try:
        return Fraction(str(value))
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError(name + " must be a finite rational number") from exc


def natural(value, name, positive=False):
    if type(value) is not int or value < int(positive):
        raise ValueError(name + (" must be a positive integer" if positive else " must be a nonnegative integer"))
    return value


def ceil_nonnegative(value):
    if value < 0:
        raise ValueError("ceiling argument must be nonnegative")
    return (value.numerator + value.denominator - 1) // value.denominator


def analyze(spec):
    """Return rational arithmetic, not a safety certificate or simulated cost."""
    raw = spec["bounds_mV"]
    b = {key: rational(raw[key], key) for key in ("S", "H", "Dmin", "Dmax", "C", "epsilon")}
    s, h, dmin, dmax, cap, eps = (b[key] for key in ("S", "H", "Dmin", "Dmax", "C", "epsilon"))
    if s < 0 or h < 0 or eps < 0 or cap < s or not 0 < dmin <= dmax:
        raise ValueError("Require 0 <= S <= C, H >= 0, epsilon >= 0 and 0 < Dmin <= Dmax")
    m = rational(raw["M"], "M") if "M" in raw else None
    n = natural(spec["horizon_periods"], "horizon_periods")
    k = natural(spec["probe_spacing_periods"], "probe_spacing_periods", positive=True)
    initial = rational(spec["initial_reserve_mV"], "initial_reserve_mV")
    terminal = rational(spec["terminal_reserve_mV"], "terminal_reserve_mV")
    if not s <= initial <= cap or not s <= terminal <= cap:
        raise ValueError("Initial and terminal reserves must lie in [S,C]")
    price_raw = spec.get("prices", {})
    prices = {name: rational(price_raw.get(name, default), "price " + name)
              for name, default in (("probe", 1), ("maintenance", 10), ("service", 1))}
    if any(value < 0 for value in prices.values()):
        raise ValueError("Prices must be nonnegative")
    terminal_probes = natural(price_raw.get("terminal_observation", 1), "terminal_observation")
    if terminal_probes not in (0, 1):
        raise ValueError("terminal_observation must be 0 or 1")

    upper_for_write = min(cap-dmax, m) if m is not None else cap-dmax
    fresh_available = cap-2*eps
    ready = s+h
    spacing_floor = s+(k+1)*h
    guards = {
        "one_wait_plus_one_repair_period": fresh_available >= s+2*h,
        "selected_spacing_plus_one_repair_period": fresh_available >= spacing_floor,
        "independent_box_repair_balance": dmin >= h,
        "fresh_ready_write_interval_nonempty": ready+2*eps <= upper_for_write,
        "initial_fresh_ready": initial-2*eps >= ready,
    }
    if h:
        max_wait = max(0, (fresh_available-s)//h-1)
    else:
        max_wait = None if fresh_available >= s else 0

    # For constant worst loss H and no other inflow, even maximal doses must
    # supply this deficit. Saturation can only increase the required count.
    deficit = max(Fraction(0), n*h+terminal-initial)
    minimum_writes = ceil_nonnegative(deficit/dmax)
    gross_count = ceil_nonnegative(deficit/dmin)
    common_writes = natural(spec.get("common_maintenance_count", gross_count), "common_maintenance_count")
    decision_probes = (n+k-1)//k
    prudent_probes = n
    early_probe_total = decision_probes+terminal_probes
    prudent_probe_total = prudent_probes+terminal_probes
    common_cost = n*prices["service"]+common_writes*prices["maintenance"]
    early_cost = common_cost+early_probe_total*prices["probe"]
    prudent_cost = common_cost+prudent_probe_total*prices["probe"]
    lower_end = initial-n*h+common_writes*dmin
    upper_end = initial-n*h+common_writes*dmax

    return {
        "scope": "conditional arithmetic only; no circuit bounds, policy execution or performance guarantee",
        "units": "reserve quantities in mV; exact rational strings; costs in declared abstract units",
        "bounds_mV": {key: str(value) for key, value in b.items()} | ({"M": str(m)} if m is not None else {}),
        "guards": guards,
        "all_arithmetic_guards_pass": all(guards.values()),
        "guard_values_mV": {
            "worst_fresh_lower_at_capacity": str(fresh_available),
            "ready_lower": str(ready),
            "selected_spacing_required_lower": str(spacing_floor),
            "maximum_admissible_write_upper": str(upper_for_write),
            "minimum_fresh_write_upper": str(ready+2*eps),
        },
        "maximum_wait_periods_from_capacity": max_wait,
        "zero_loss_wait_is_unbounded": max_wait is None,
        "conservation": {
            "assumed_loss_each_period_mV": str(h),
            "horizon_periods": n,
            "initial_reserve_mV": str(initial),
            "terminal_reserve_target_mV": str(terminal),
            "required_gross_dose_mV": str(deficit),
            "necessary_write_count_using_Dmax": minimum_writes,
            "gross_count_using_Dmin_without_saturation": gross_count,
            "gross_count_is_not_a_schedule_or_cost_upper_bound": True,
            "common_write_count": common_writes,
            "common_count_at_least_necessary_bound": common_writes >= minimum_writes,
            "unsaturated_terminal_interval_mV": [str(lower_end), str(upper_end)],
            "interval_lower_meets_terminal_floor": lower_end >= terminal,
            "exact_target_for_exact_dose": dmin == dmax and lower_end == terminal,
            "at_most_one_maintenance_per_period_count_condition": common_writes <= n,
        },
        "conditional_ledger": {
            "requires_feasible_plans_and_matched_terminal_inventory": True,
            "same_service_and_maintenance_counts_assumed": True,
            "terminal_target_alone_does_not_ensure_equal_unused_stock": True,
            "service_pulses": n,
            "maintenance_actions_each": common_writes,
            "probe_spacing_periods": k,
            "spaced_decision_probes": decision_probes,
            "prudent_decision_probes": prudent_probes,
            "terminal_probes_each": terminal_probes,
            "prices": {name: str(value) for name, value in prices.items()},
            "spaced_cost": str(early_cost),
            "prudent_cost": str(prudent_cost),
            "difference_from_probe_counts_only": str(prudent_cost-early_cost),
            "difference_fraction_of_prudent": str((prudent_cost-early_cost)/prudent_cost) if prudent_cost else None,
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON containing declared arithmetic parameters")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = json.dumps(analyze(json.loads(args.input.read_text())), indent=2, sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(report)
    else:
        print(report, end="")


if __name__ == "__main__":
    main()
