"""Directional A1 budgets with a two-sided pre-read charge allowance."""

from evidence import Decision, Exact, PortEvidence, prepare


def certify(port: PortEvidence, delta_lo: Exact, delta_hi: Exact) -> Decision:
    budget = prepare(port, delta_lo, delta_hi)
    base_silent = max([0] + [
        dev + budget.radii[k] + budget.radii[0]
        for k, dev in enumerate(budget.deviations[:-1])
    ])
    base_fire = max(0, -budget.deviations[-1] + budget.radii[-1] + budget.radii[0])
    common_room = budget.half_dose - budget.initial - 2 * budget.epsilon - budget.threshold
    silence_room = common_room - base_silent - budget.silence_cost
    fire_room = common_room - base_fire - budget.fire_cost
    reasons = list(budget.reasons)
    if silence_room <= 0:
        reasons.append("silence room")
    if fire_room < 0:
        reasons.append("FIRE room")
    return Decision(tuple(reasons), silence_room, fire_room, budget.first_fire, budget.need)
