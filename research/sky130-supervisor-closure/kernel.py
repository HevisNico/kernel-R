"""The supervisor kernel, in exact integers: a Python mirror of ../sky130-supervisor-qualification/lean/Model.lean.

Every quantity is an integer number of units of reserve (UNIT volts each). `choose`, `lower`,
`upper` and `next_carry` are the definitions of the Lean file, line for line; `test_kernel.py`
checks them against the properties that the Lean file proves. The kernel knows nothing of the
circuit: it receives reports and returns one action per period.
"""
from dataclasses import dataclass

UNIT = 1e-7                     # volts per unit of reserve: 0.1 uV
WAIT, MAINTENANCE, REFUSE = "wait", "maintenance", "refuse"


@dataclass(frozen=True)
class Bounds:
    S: int                      # service floor: reserve at or above S gives a correct read
    H: int                      # largest loss of reserve in one whole service period
    Dmin: int                   # smallest dose of one maintenance cycle
    Dmax: int                   # largest dose
    linear_capacity: int
    semantic_capacity: int      # largest reserve at which every guaranteed read is still correct
    epsilon: int                # largest error of a report

    @property
    def capacity(self):
        return min(self.linear_capacity, self.semantic_capacity)

    def well_formed(self):
        return (0 <= self.S and 0 <= self.H and 0 <= self.epsilon and self.H <= self.Dmin and self.Dmin <= self.Dmax
                and self.S + 2 * self.H + 2 * self.epsilon + self.Dmax <= self.capacity)

    def room(self):
        """Capacity left by the room condition; negative when the bounds are not well formed for that reason."""
        return self.capacity - (self.S + 2 * self.H + 2 * self.epsilon + self.Dmax)


def ready(b, lo):
    return b.S + b.H <= lo


def lower(b, carry, report):
    return max(report - b.epsilon, carry)


def upper(b, report):
    return min(report + b.epsilon, b.capacity)


def choose(b, lo, hi):
    if ready(b, lo) and lo <= hi:
        if hi + b.Dmax <= b.capacity:
            return MAINTENANCE
        if b.S + 2 * b.H <= lo:
            return WAIT
        return REFUSE
    return REFUSE


def next_carry(b, lo, action):
    if action == WAIT:
        return lo - b.H
    if action == MAINTENANCE:
        return lo - b.H + b.Dmin
    return 0


def step(b, carry, report):
    """One period of guaranteed service: (action, lower, upper, next carry)."""
    lo, hi = lower(b, carry, report), upper(b, report)
    action = choose(b, lo, hi)
    return action, lo, hi, next_carry(b, lo, action)


def prepare(b, report):
    """Preparation, before any guaranteed service: a maintenance is allowed only with its Dmax headroom."""
    return MAINTENANCE if report + b.epsilon + b.Dmax <= b.capacity else WAIT


def entry(b, report):
    """Entry certificate: a fresh report whose lower bound is at least S + H and whose upper bound fits the capacity.
    Returns the first carry, or None when service must not begin."""
    lo, hi = report - b.epsilon, report + b.epsilon
    return lo if ready(b, lo) and hi <= b.capacity else None


def to_units(volts):
    """Outward rounding is the caller's business; this is the nearest unit."""
    return int(round(volts / UNIT))
