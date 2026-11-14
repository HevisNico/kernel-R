"""Exact arithmetic and common evidence checks for prospective port rules."""

from dataclasses import dataclass
from fractions import Fraction

Exact = str | int | Fraction
REST = Fraction(1, 10)
LEVEL_FLOOR = Fraction(19, 20)
MZ = MQ = Fraction(1, 5000)


def rational(value: Exact) -> Fraction:
    if type(value) not in (str, int, Fraction):
        raise ValueError("supply exact rationals or decimal strings")
    try:
        return Fraction(value)
    except ZeroDivisionError as error:
        raise ValueError("rational denominator must be nonzero") from error


def nonnegative(value: Exact) -> Fraction:
    value = rational(value)
    if value < 0:
        raise ValueError("expected a nonnegative bound")
    return value


@dataclass(frozen=True)
class Read:
    """One ordered port read, with a reported log gain and a charge enclosure."""

    gain: Exact  # Normalized reported log gain, including kappa if fired.
    c_pre_lo: Exact
    c_pre_hi: Exact
    noise_sup_v: Exact
    fired: bool
    latch_rises: int
    selected_writes: int
    other_writes: int
    fire_latency: Exact | None = None


@dataclass(frozen=True)
class PortEvidence:
    need: int  # Fixed by the prediction independently of count agreement.
    level0: Exact
    dose0: Exact
    base_a: Exact  # Includes all printed initial allowances except eps3.
    eps3: Exact
    h3: Exact
    eps_kappa: Exact
    reads: tuple[Read, ...]
    same_cell: bool


@dataclass(frozen=True)
class Budget:
    half_dose: Fraction
    initial: Fraction
    threshold: Fraction
    epsilon: Fraction
    silence_cost: Fraction
    fire_cost: Fraction
    deviations: tuple[Fraction, ...]
    radii: tuple[Fraction, ...]
    reasons: tuple[str, ...]
    first_fire: int | None
    need: int


@dataclass(frozen=True)
class Decision:
    reasons: tuple[str, ...]
    silence_room: Fraction
    fire_room: Fraction
    first_fire: int | None
    need: int

    @property
    def eligible(self) -> bool:
        return not self.reasons

    @property
    def contradicted(self) -> bool:
        return self.eligible and self.first_fire != self.need


def prepare(port: PortEvidence, delta_lo: Exact, delta_hi: Exact) -> Budget:
    """Compute common terms; malformed or incomplete evidence raises ValueError."""
    lo, hi = nonnegative(delta_lo), nonnegative(delta_hi)
    if hi > Fraction(1, 20):
        raise ValueError("delta_hi exceeds the proved upper cap (1/20)")
    if type(port.need) is not int or port.need < 0 or len(port.reads) <= port.need:
        raise ValueError("missing predicted read prefix")
    if type(port.same_cell) is not bool:
        raise ValueError("same-cell check must be a Boolean")
    dose = nonnegative(port.dose0)
    eps = nonnegative(port.eps3)
    kappa = nonnegative(port.eps_kappa)
    prefix = port.reads[:port.need + 1]
    gains = tuple(rational(read.gain) for read in prefix)
    ell = nonnegative(port.h3) + 2 * max(nonnegative(r.noise_sup_v) for r in prefix) + MQ
    reasons = []
    if not port.same_cell:
        reasons.append("same-cell check")
    if rational(port.level0) - ell < LEVEL_FLOOR:
        reasons.append("threshold floor")
    charges = [(rational(r.c_pre_lo), rational(r.c_pre_hi)) for r in prefix]
    if any(low > high for low, high in charges):
        raise ValueError("reversed charge enclosure")
    if any(low < REST - lo or high > REST + hi for low, high in charges):
        reasons.append("rest charge")
    for read in prefix:
        if type(read.fired) is not bool:
            raise ValueError("read outcome must be a Boolean")
        counts = (read.latch_rises, read.selected_writes, read.other_writes)
        if any(type(count) is not int or count < 0 for count in counts):
            raise ValueError("invalid observed event count")
        if read.fired and (read.fire_latency is None or rational(read.fire_latency) < Fraction(19, 25)):
            raise ValueError("missing FIRE latency or FIRE before 0.76")
    if any(r.latch_rises > 1 for r in prefix):
        reasons.append("multiple latch rises")
    if any(r.selected_writes != (0 if r.fired else 1) or r.other_writes != 0 for r in prefix):
        reasons.append("steering")
    return Budget(
        half_dose=dose / 2,
        initial=nonnegative(port.base_a) + eps,
        threshold=Fraction(20, 17) * ell,
        epsilon=eps,
        silence_cost=Fraction(5, 4) * hi,
        fire_cost=Fraction(20, 17) * lo,
        deviations=tuple(gain - gains[0] - k * dose for k, gain in enumerate(gains)),
        radii=tuple(MZ + (kappa if r.fired else 0) for r in prefix),
        reasons=tuple(reasons),
        first_fire=next((k for k, read in enumerate(prefix) if read.fired), None),
        need=port.need,
    )
