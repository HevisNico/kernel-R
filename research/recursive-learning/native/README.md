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

- With learner input gain 2, `prepared_routed_feedback_exists` constructs a
  complete native execution with one learner FIRE, one corresponding feedback
  delivery and an exact increase of `3/5` on the selector port. The other two
  teacher gains stay fixed.
- With learner input gain 1, `prepared_silent_probe_exists` constructs a
  complete native execution with no FIRE, no delivery and unchanged selector
  gain. More generally, `selector_unchanged_without_learner_fire` derives the
  unchanged gain in any execution with the fixed router, an empty initial
  queue and a resting selector sensor with no active raw pulse if the learner
  never fires.

Both prepared cases work in either fabrication box. `RoutedFeedback.sets_selector`
links the routed dose to the discrete selector transition when the teacher
starts with the first teaching credit already set. The learner's firing here
comes from its prepared gain and probe. Deriving that gain from a lesson,
implementing the full acceptance test and using the selector to dispatch the
next lesson within the network remain separate obligations.

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
