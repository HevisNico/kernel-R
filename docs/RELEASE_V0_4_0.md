# Kernel R v0.4.0: stop-learning training

Draft release text and checklist. This file does not create a tag or
publish a release.

## Before publishing

1. Merge the stop-learning pull request into `main` after the Lean and
   recursive-learning workflows pass on its final revision.
2. Check the workflows on the resulting `main` commit and record that
   exact commit as the release target.
3. Update the "Current release" line of the main README to v0.4.0.
4. Update `CITATION.cff`, which still names version 0.2.0: title,
   version and release date.
5. Create the release as a draft against the recorded commit, with the
   text below, and add the commit hash to its links.

## Draft release text

### Summary

This release adds Lean proofs that a training rule removes two hypotheses
of the v0.3.0 coincidence result: the exact birth gain of 1.2 and the FIRE
level within ±3%. The kernel definitions are unchanged.

Each port receives a train of identical pulses. A pulse that leaves the
cell silent writes one dose. A pulse that makes it fire writes nothing,
because the write phase then falls inside the refractory period. Training
stops by itself at a gain that depends on the cell's own FIRE level. This
is the stop-learning principle of Brader et al., implemented in switched
capacitors by Noack et al.

### Results

- **Training and read in one execution.** Two ports of a rested cell
  start from gains that do not fire. Each is trained until it stops, then
  one pulse on each port reads the cell, the second up to a quarter of a
  unit after the first. The read FIRE comes later than 0.239 model units
  after the first read pulse and no later than 0.256 units after the
  second. This holds for every FIRE level between 0.95 and 1.05 and ±10%
  fabrication variation. Every complete run has the same FIRE dates and
  the same end state. Lean theorem `trained_read_exists`.
- **Two-cell coincidence decision.** Two cells with their own parameters,
  start gains and FIRE levels are trained and read. In every complete run
  of the network, the two read FIRE dates are closer than 0.15 units
  exactly when the two cells are read at the same date, among offsets of
  −0.3, 0 and +0.3 units. Lean theorem `trained_coincidence_network`.
- **Witness.** An explicit cell and schedule satisfy every hypothesis of
  the two theorems. Lean theorems `trainedCell_witness` and
  `trained_coincidence_witness`.

At 100 µs per model unit, the read window is 23.9 µs to 25.6 µs plus the
delay between the two read pulses, and the receiver aperture is 15 µs.

### How the proofs are built

| Module | Content |
|---|---|
| `StopLearningLatency.lean` | The latency window on the read equation |
| `SilentStep.lean` | A silent pulse writes exactly one dose, for any gain |
| `Refractory.lean` | The period after a FIRE, for any order of events |
| `FiringStep.lean` | A firing pulse writes nothing |
| `TrainingLoop.lean` | The loop, its stopping rule, two ports, uniqueness |
| `Driven.lean` | The period before a FIRE under several pulses |
| `JointRead.lean` | The read of two ports and the end-to-end theorem |
| `TrainedCoincidence.lean` | The two-cell decision and the witness |

All are in `research/recursive-learning/native/`. Its
[README](../research/recursive-learning/native/README.md) describes each
module, and [STOP_LEARNING_SPEC.md](../research/recursive-learning/native/STOP_LEARNING_SPEC.md)
states the regime.

One finding is worth noting. Training does not always stop at the first
FIRE. A pulse may fire only thanks to the residual rest charge left by the
previous silent pulse, and the next pulse, which starts from the exact
rest charge, may then be silent once more. The stopping theorem therefore
asks for `2 r + 2` pulses when `r` doses reach a gain that always fires.

### Limits

- The work is a mathematical model. No hardware measurement is included.
- The window constants are for doses of at most 1/20. The training
  theorems hold for doses up to 3/5.
- The ERROR entry threshold of a trained port lies between 0.07 and 0.08,
  below the 0.1 of earlier releases.
- In each cell, the read pulse on the first trained port arrives no later
  than the one on the second, by at most 1/10 of a unit for the two-cell
  decision.
- The recovery rate lies between 0.07 and 0.10, the sensors start within
  `10⁻⁵` of their rest charge, and pulses are at least 22 units apart.
- The pulse amplitude, the unit response and the MARK and SILENT levels
  are those of the model.
- The two cells are independent, and the receiver is a decision rule on
  their FIRE dates.
- The v0.3.0 comparison with a constant-current timer is not redone with
  trained cells.

### Verification

Run from `research/recursive-learning/native` with Lean 4.35.0:

```sh
lake exe cache get
lake build
```

The build runs the axiom audit over every declaration of the package.
The new theorems depend only on `propext`, `Classical.choice` and
`Quot.sound`.

### AI assistance

As described in the main README, the work is directed by Nicolas
Breuillaud with AI assistance on proofs and documentation. Lean checks
the proof terms against their definitions and hypotheses.
