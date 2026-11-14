"""Symmetric status-3 budget with a two-sided pre-read charge allowance."""

from evidence import Decision, Exact, PortEvidence, prepare


def certify(port: PortEvidence, delta_lo: Exact, delta_hi: Exact) -> Decision:
    budget = prepare(port, delta_lo, delta_hi)
    # At index zero the difference is identically zero.
    base_b = max([0] + [
        abs(dev) + budget.radii[k] + budget.radii[0]
        for k, dev in enumerate(budget.deviations) if k > 0
    ])
    cumulative = base_b + 2 * budget.epsilon
    room = (
        budget.half_dose - budget.initial - cumulative - budget.threshold
        - max(budget.silence_cost, budget.fire_cost)
    )
    reasons = budget.reasons + (("status-3 room",) if room <= 0 else ())
    return Decision(reasons, room, room, budget.first_fire, budget.need)
