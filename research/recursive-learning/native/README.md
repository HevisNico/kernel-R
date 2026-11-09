# Native R memory for the adaptive teaching loop

The [discrete example](../README.md) has two teaching credits and a selector.
Here each is encoded in the log-gain of a separate port of one actual R cell.
One full exposed ERROR section adds `3/5` to its port, which represents one
credit or sets the selector. The encoding is relative to that port's starting
log-gain.

## What Lean checks

[`encodes_iff_counts`](NativeLearning.lean) applies to any native execution
with complete exposed ERROR covers on the three teacher ports. An endpoint
represents the claimed memory exactly when each port's actual phase count
equals the required credit increment. Missing, extra or misrouted doses
therefore cannot represent that commit. [`selector_iff`](NativeLearning.lean)
reads the selector by comparing the current log-gain on port 2 with its
starting value plus `3/10`, half the dose.

[`prepared_run_exists`](NativeLearning.lean) constructs the teacher's native
execution under either declared fabrication box. It starts from a prepared
READY state with unit gains, recovery `2/25`, full reserve and no active raw
current. The queue contains three separated canonical pulses on ports 0, 2
and 1, due at offsets 1, 9 and 17.

| Snapshot | Preparation credit | Practice credit | Selector |
|---|---:|---:|---|
| Initial | 0 | 0 | Preparation |
| Complete at offset 16.5 | 1 | 0 | Practice |
| Complete at offset 24.5 | 1 | 1 | Practice |

The actual trace carries the middle state into the second segment, consumes
the three deliveries and produces no teacher firing. The pulses arrive and
each sensor completes its own cycle under the existing [R dynamics](../../../model/CELL.md).
[`prepared_crossing_run_exists`](NativeLearning.lean) gives a complete
upward-crossing execution of the same history using its transverse contacts.

The queue in this construction is supplied in advance. The `8 → 7 → 6` pulse
count is the deployed lesson cost in the discrete experiment.

## One feedback pulse from an actual learner firing

The [two-cell experiment](Feedback.lean) starts with a canonical probe already
admitted on learner 0. The teacher's raw ports and the global pending queue
are empty. The fixed router sends any learner FIRE at time `F` to the teacher's
selector port at `F + δ(F)`, with `0.3 ≤ δ(F) ≤ 0.4`.

- With learner input gain in `[9/5, 11/5]`, `prepared_routed_feedback_of_strong_gain`
  constructs a complete first-contact execution with one learner FIRE, one
  corresponding feedback delivery and an exact increase of `3/5` on the
  selector port. `RoutedFeedback.every_complete` proves the same firing date,
  delivery and teacher gains for every first-contact execution complete through
  that horizon, from the same state with the same parameters and router.
- With learner input gain in `(0, 7/6]`, the probe is silent and the selector
  gain stays fixed. `prepared_weak_probe_crossing_exists` also constructs a
  complete upward-crossing execution with this outcome.

Both bands apply in either fabrication box. They leave a gap between
`7/6` and `9/5` where the exact firing threshold is open.

### Routed feedback under upward crossings

`causal_routed_crossing_exists` proves the strong-gain case in the model's
upward-crossing semantics. This construction numbers the teacher 0 and the
learner 1 and uses the same local starting states. The network starts with an
empty delivery queue. The learner's actual FIRE issues the token, and the
teacher consumes it at the routed date.

`CausalRoutedFeedback.every_crossing_complete` gives the same single FIRE,
single delivery, empty final queue and exact selector dose for every
upward-crossing execution complete through the constructed horizon. The other
two teacher gains stay fixed. The proof retains each candidate execution's
own paths and jumps when relating it to the first-contact semantics.

The discrete commit tests whether the accepted lesson still works with one
fewer preparation pulse. Its failure tells the teacher to switch to
practice. `prepared_probe_reports_failure` fixes the same meaning for the
physical signal. If failure is encoded by a gain in the strong band and
success by a gain in the weak band, the learner fires exactly on failure.
When the selector starts off, its final log-gain reads as on exactly when
the discrete commit selects practice. This holds for every first-contact
execution complete through the constructed horizon.

## The last preparation pulse determines the probe gain

The [one-cell assay](LessonProbe.lean) starts both runs with the same physical
state and unit gain on the probe port. It schedules a common diagnostic pulse
at offset 9 and a readout pulse on the same port at offset 17. The two lessons
differ by the preparation pulse on port 1 at offset 1.

| Last preparation pulse | State during the diagnostic | Probe log-gain at offset 17 | Readout through offset 18 |
|---|---|---:|---|
| Present | Protected recovery | 0 | Silent |
| Omitted | READY | 0.6 | One FIRE |

In the prepared case the diagnostic completes its sensor cycle during
protection and leaves the gain unchanged. In the omitted case it completes
an exposed ERROR phase and raises the log-gain by `3/5`. Lean proves that
`exp(3/5)` is in the strong band. The readout uses the actual state carried
from the lesson, including charge, recovery and energy. Only FIREs in the
readout window report failure.

`lesson_probe_run_exists` constructs the whole history and
`lesson_probe_crossing_exists` gives the same history under upward crossings.
`LessonProbeAdmission.gain_every_complete` fixes the gain at admission for
all complete first-contact histories. At offset 18, the failure signal is
the same for all complete histories under either semantics. Both fabrication
boxes are covered.

`LessonProbeRun.reports_example_failure` matches the two outcomes of the
discrete validation at its last preparation slot. The assay implements that
varying slot. The earlier discrete lesson pulses are outside this assay.
Joining this readout to the teacher's routed update and dispatching the next
lesson in the network are the remaining steps.

## Verify

Run from the repository root with Lean 4.35.0 available:

```sh
cd research/recursive-learning/native
lake exe cache get
lake build
```

The [dedicated CI workflow](../../../.github/workflows/recursive-learning.yml)
builds this package with the pinned dependencies. Its default targets compile
`NativeLearning`, `Feedback` and `LessonProbe`, and run [the axiom audit](NativeAudit.lean), which checks all
imported declarations under `RecursiveLearning`, including private ones.
Unexpected axioms and admitted proofs fail the build. The underlying R imports
and Mathlib pins come from the existing proof package.
