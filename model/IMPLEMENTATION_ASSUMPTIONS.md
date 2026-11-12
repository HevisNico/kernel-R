# Implementation assumptions

The [cell laws](CELL.md) describe ideal events and exact quantities. This
note lists what a physical implementation would have to provide for the
proved results to apply to it. These are assumptions about a device. No
device has been built, and none of them is verified here.

## The two ERROR thresholds share one detector

The dose of a full ERROR phase is `8 × (entry − exit)`. It depends on
the distance between the two thresholds and not on where they sit. An
error common to both thresholds leaves the dose unchanged.
[`training_read_common_offset`](../research/recursive-learning/native/OffsetAndDelay.lean)
states this for one training pulse and one read.

One comparator used for both crossings can supply a common error if its
input-referred offset is unchanged between them. This is an implementation
condition: a change of offset with common-mode voltage, noise or switching
history need not cancel. Two separate comparators can introduce distinct
offsets; the theorems that bound the thresholds separately then apply if
those bounds are met.

## Events react after a delay

The model switches phase at the instant a charge meets its threshold. A
circuit reacts a short time later, and the sensor keeps discharging in
the meantime. The dose then depends on the discharge rates.
[`training_read_reaction_delay`](../research/recursive-learning/native/OffsetAndDelay.lean)
bounds the change of the increment by `2.4 × d` for a delay `d` of at
most 0.01 model units, the same at both thresholds.

The rate independence of the dose is therefore a limit. It holds to the
extent that the reaction delay is short against the ERROR phase, which
lasts 0.15 model units at nominal values.

## A pulse acts after a lag

The model applies the gain of a port to a pulse at the instant it
arrives. A real gain element has settling dynamics. The result in
[`trained_dates_decide_lag`](../research/recursive-learning/native/ReadLag.lean)
assumes that each observed read FIRE date equals its model date plus a
cell-specific lag. Under the stated read schedule, the coincidence
decision survives when the two lags differ by at most 3/100 of a unit.

This theorem compares dates. It does not derive the additive-lag
assumption from a delayed input, a transistor's settling response or a
modified hybrid execution. A circuit must justify that approximation
separately. Pulse-dependent and port-dependent lags are not covered by
the fixed-per-cell statement.

## The log-gain is a voltage measured against temperature

The model stores a log-gain `z` and applies the gain `exp(z)`. An
element that turns a stored voltage into an exponential gain does so
through a thermal voltage, which is proportional to absolute
temperature. The same stored voltage is a different log-gain at a
different temperature.

For a dose to mean the same log-gain at every temperature, the voltages
that set it must scale with absolute temperature. In the model this is
hidden in the statement that thresholds and actuation factors are fixed.

## Gains and the FIRE threshold carry a per-cell error

The fixed-current comparison in
[`CoincidenceSeparation.lean`](../research/recursive-learning/native/CoincidenceSeparation.lean)
uses a birth gain of exactly 1.2 and a FIRE threshold within ±3%.
Those assumptions belong to that comparison. In a circuit the gain of
each port and the FIRE threshold of each cell carry device variation.

The read latency depends on both. A result that must hold for every
cell needs either a gain band wide enough for that error, or a mechanism
by which the cell absorbs it. The fixed-current comparison does not
establish that adaptation.

The v0.4.0 stop-learning theorems provide such a mechanism in the model.
Each port receives enough identical, spaced pulses to reach stable firing
from rest, so its final gain follows the cell's own FIRE level. The first
FIRE alone is not a stopping certificate: a residual-charge-assisted FIRE
can be followed by a silent pulse. For start gains that do not fire
and a FIRE level between 0.95 and 1.05, the read latency of two trained
ports lies in a window that depends on neither. See
[`trained_read_exists`](../research/recursive-learning/native/JointRead.lean)
and [`OpenCell.read`](../research/recursive-learning/native/FreeRead.lean).
The pulse amplitude and the unit response remain exact there.
The trained coincidence result is in
[`TrainedCoincidence.lean`](../research/recursive-learning/native/TrainedCoincidence.lean).
It does not extend the fixed-current separation theorem to trained cells.

The same theorems give a tolerance for the number of doses a port needs
before it fires. With errors `a` on the start log-gain, `b` on the dose
and `ℓ` on the FIRE level, the need is `m` when
`a + m * b + 20/17 * ℓ + 1/8000 < d₀ / 2`, for a nominal dose `d₀`. The
dose error is counted once for each dose, so a search over `2^k` needs
asks for a dose error below about `d₀ / 2^(k+1)`. See
[`needIs_of_tolerance`](../research/recursive-learning/native/NeedTolerance.lean).

The searches built on these cells use wires that release pulses at
preset dates when a FIRE falls inside a window. Such a wire stands for
a clocked register. The model does not build it from cells.

## What stays exact in every result

- The actuation factors 8 and 1/2.
- The canonical pulse shape and its unit width.
- The rest charges `r` and `r_m` in the READY equations.
- The leak constant `κ`.

Each of these is a ratio or a shape that a circuit realizes with its own
tolerance. No result here bounds the effect of an error on them.
