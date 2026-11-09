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

The queue is supplied in advance. Learner signals, acceptance, routing of the
feedback pulses and an in-network implementation of the selector comparison
remain separate obligations. The native theorem concerns the teacher's memory
actuation. The `8 → 7 → 6` pulse count is the deployed lesson cost in the
discrete experiment.

## Verify

Run from the repository root with Lean 4.35.0 available:

```sh
repo=$PWD
(cd research/recursive-learning && lake build)
cd proof/lean
lake exe cache get
lake build KernelR.HybridDoseCounting KernelR.HybridQuietSourceArrival \
  KernelR.HybridWeakInputCycleExistence KernelR.HybridCrossingExecution
LEAN_PATH="$repo/research/recursive-learning/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}" \
  lake env lean --root="$repo/research/recursive-learning/native" \
  "$repo/research/recursive-learning/native/NativeLearning.lean"
```

The native file prints the axiom dependencies of its public results. The
underlying R imports and Mathlib pins come from the existing proof package.
