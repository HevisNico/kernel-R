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
`7/6` and `9/5`; the exact firing threshold and the upward-crossing witness
for the routed case are open.

The discrete commit tests whether the accepted lesson still works with one
fewer preparation pulse. Its failure tells the teacher to switch to
practice. `prepared_probe_reports_failure` fixes the same meaning for the
physical signal. If failure is encoded by a gain in the strong band and
success by a gain in the weak band, the learner fires exactly on failure.
When the selector starts off, its final log-gain reads as on exactly when
the discrete commit selects practice. This holds for every first-contact
execution complete through the constructed horizon.

The test outcome is supplied via the starting gain. The next obligations
are to derive that gain from the lesson and to use the selector to send
the next lesson within the network. The current router carries the response
from learner to teacher.

## Verify

Run from the repository root with Lean 4.35.0 available:

```sh
cd research/recursive-learning/native
lake exe cache get
lake build
```

The [dedicated CI workflow](../../../.github/workflows/recursive-learning.yml)
builds this package with the pinned dependencies. Its default targets compile
`NativeLearning` and `Feedback`, and run [the axiom audit](NativeAudit.lean), which checks all
imported declarations under `RecursiveLearning`, including private ones.
Unexpected axioms and admitted proofs fail the build. The underlying R imports
and Mathlib pins come from the existing proof package.
