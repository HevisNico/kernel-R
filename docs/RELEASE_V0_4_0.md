# Kernel R v0.4.0: stop-learning training, networks and searches

**Published release notes for v0.4.0.** Released on 2026-11-11 from commit
[`5d47261`](https://github.com/HevisNico/kernel-R/commit/5d47261412a582f6b96ec139b67e406884d406cc), tag
[`v0.4.0`](https://github.com/HevisNico/kernel-R/releases/tag/v0.4.0). The text
below is the release text. Counts and limits describe that commit.

## Release text

### Summary

This release adds Lean proofs that a training rule removes two hypotheses
of the v0.3.0 coincidence result: the exact birth gain of 1.2 and the FIRE
level within ±3%. It then builds networks and searches from cells trained
that way. The kernel definitions are unchanged.

Each port receives a train of identical pulses. A pulse that leaves the
cell silent writes one dose. A pulse that makes it fire writes nothing,
because the write phase then falls inside the refractory period. Training
stops by itself at a gain that depends on the cell's own FIRE level. This
is the stop-learning principle of Brader et al., implemented in switched
capacitors by Noack et al.

### Results

**Trained cells**

- **Training and read in one execution.** Two ports of a rested cell
  start from gains that do not fire. Each is trained until it stops. One
  pulse on each port then reads the cell, in either order, at most a
  quarter of a unit apart. The read FIRE comes later than 0.239 model
  units after the first read pulse and no later than 0.256 units after
  the second. This holds for every FIRE level between 0.95 and 1.05 and
  ±10% fabrication variation. Every complete run has the same FIRE
  dates. Lean theorems `trained_read_exists` and `OpenCell.read`.
- **Two-cell coincidence decision.** Two cells with their own parameters,
  start gains and FIRE levels are trained and read. In every complete run
  of the network, the two read FIRE dates are closer than 0.15 units
  exactly when the two cells are read at the same date, among offsets of
  −0.3, 0 and +0.3 units. Lean theorem `trained_coincidence_network`.
- **A lag in each cell.** In a circuit a pulse acts a little after it
  arrives. A lag that is the same for every pulse of a cell shifts its
  FIRE dates by that lag. The decision above still holds when the lags
  of the cells lie within 3/100 of a unit of each other. Lean theorems
  `trained_dates_decide_lag` and `trained_network_lag`.

**Networks**

- **Composition.** Cells joined by wires that go forward are described
  one by one. The network then has a complete run, and every complete
  run has the same FIRE dates and the same final values. Lean theorems
  `routed_execution` and `acyclic_network_states`.
- **Any depth.** Any number of trained cells, each read by sources or by
  the read FIRE of earlier cells. A chain of `n` cells is proved for
  every `n`. Lean theorems `trained_wired_network` and
  `trained_chain_witness`.

**Searches**

- **The need of a port.** A port needs `m` doses before a pulse makes
  its cell fire. A probe cell that receives `c` training pulses and a
  read pulse fires on the read exactly when `m ≤ c`. The need is not an
  exact birth gain. It holds for start log-gain, dose and FIRE level
  errors `a`, `b`, `ℓ` with `a + m b + 20/17 ℓ + 1/8000 < d₀/2`. Lean
  theorems `self_calibrated_probe_exists` and `needIs_of_tolerance`.
- **Acting on silence.** A trained cell read by one pulse fires later
  than 0.355 units after it, and before 0.256 units when read by two. A
  gate cell read by a clock pulse fires late exactly when the probe sent
  no report. Lean theorems `OpenCell.read_one` and `trained_search`.
- **A tree of questions.** For every `k`, a tree of `2^k − 1` questions
  separates the needs 1 to `2^k`. A run asks `k` questions, and the last
  answer gives the need. Lean theorems `bisection_search`,
  `bisect_reached_iff` and `bisect_last`.
- **Successive approximation.** The same search with `2k + 1` cells. The
  gates give the binary digits of `m − 1`, and the last stage is a
  learner that receives exactly `m` training pulses. The run ends at the
  date `1003 + 33 · 2^k + 25k`. Lean theorems `successive_search`,
  `successive_digits` and `approx_duration`.

Explicit cells and schedules satisfy the hypotheses of each theorem, at
every size where the theorem has one: `trainedCell_witness`,
`trained_chain_witness`, `search_action_witness`,
`bisection_search_witness` and `successive_search_witness`.

At 100 µs per model unit, the read window is 23.9 µs to 25.6 µs plus the
delay between the two read pulses, and the receiver aperture is 15 µs.

### How the proofs are built

| Module | Content |
|---|---|
| `StopLearningLatency.lean` | The latency windows on the read equation |
| `SilentStep.lean` | A silent pulse writes exactly one dose, for any gain |
| `Refractory.lean` | The period after a FIRE, for any order of events |
| `FiringStep.lean` | A firing pulse writes nothing, and its date |
| `TrainingLoop.lean` | The loop, its stopping rule, two ports, uniqueness |
| `Driven.lean` | The period before a FIRE under several pulses |
| `JointRead.lean` | The read of two ports and the end-to-end theorem |
| `TrainedCoincidence.lean` | The two-cell decision and the witness |
| `SelfCalibratedProbe.lean` | The need of a port and the count probe |
| `FamilyProduct.lean` | Any number of independent cells |
| `RoutedProduct.lean` | Cells joined by wires |
| `FreeRead.lean` | A trained cell read from outside, in either order |
| `AcyclicNetwork.lean` | Composition along forward wires |
| `WiredNetwork.lean` | Networks of trained cells of any depth |
| `SignalNetwork.lean` | Report windows and pulses at fixed dates |
| `SearchCells.lean` | The probe cell and the gate cell |
| `TrainedSearch.lean` | A forest of questions |
| `NeedTolerance.lean` | The need of a probe from fabrication tolerances |
| `SearchActions.lean` | A search that ends by a lesson |
| `BisectionSearch.lean` | The tree of every depth |
| `SuccessiveSearch.lean` | The successive approximation of every depth |
| `ReadLag.lean` | The coincidence decision with a lag in each cell |

All are in `research/recursive-learning/native/`. Its
[README](../research/recursive-learning/native/README.md#map-of-the-stop-learning-results)
has a map of the strongest statement at each level, and
[STOP_LEARNING_SPEC.md](../research/recursive-learning/native/STOP_LEARNING_SPEC.md)
states the regime.

Two findings are worth noting.

Training does not always stop at the first FIRE. A pulse may fire only
thanks to the residual rest charge left by the previous silent pulse,
and the next pulse, which starts from the exact rest charge, may then be
silent once more. The stopping theorem therefore asks for `2 r + 2`
pulses when `r` doses reach a gain that always fires.

The error on the dose counts once for each dose. A search over `2^k`
needs therefore asks for a dose error below about `d₀ / 2^(k+1)`. For a
dose of 1/20 known to 1%, needs up to 49 are separated.

### Limits

- The work is a mathematical model. No hardware measurement is included.
- The window constants are for doses of at most 1/20. The training
  theorems hold for doses up to 3/5.
- The ERROR entry threshold of a trained port lies between 0.07 and 0.08,
  below the 0.1 of earlier releases.
- The recovery rate lies between 0.07 and 0.10, the sensors start within
  `10⁻⁵` of their rest charge, and pulses are at least 22 units apart.
- The pulse amplitude, the unit response and the MARK and SILENT levels
  are those of the model.
- In the two-cell decision the cells are independent, and the receiver
  is a decision rule on their FIRE dates.
- In a wired network whose two read pulses come from different cells,
  the proved windows widen with the depth and must stay within a quarter
  of a unit.
- In the searches a FIRE inside a window releases pulses at preset
  dates. Such a wire stands for a clocked register, which is not built
  from cells.
- The gates of a search are trained in advance. A search of depth `k`
  by successive approximation lasts about `33 · 2^k` units, three times
  its first question.
- The tolerance condition is sufficient. It is not shown to be
  necessary, and a dose that drifts from pulse to pulse is not covered.
- The explicit cells have nominal rates and a FIRE level of 1. The
  theorems cover the whole fabrication box.
- The v0.3.0 comparison with a constant-current timer is not redone with
  trained cells.

### Verification

Run from `research/recursive-learning/native` with Lean 4.35.0:

```sh
lake exe cache get
lake build
```

The build runs the axiom audit over every declaration in the
`RecursiveLearning` namespace that the package imports: the native
package, the discrete model it depends on, private declarations and the
auxiliary declarations Lean generates (equation lemmas, `match` and proof
helpers). At this commit it reports 5741 declarations, including 3525
theorems. The sources of the native package state 943 theorems and
lemmas directly; the difference is generated declarations and the parent
package. Every audited declaration depends only on `propext`,
`Classical.choice` and `Quot.sound`.

### AI assistance

As described in the main README, the work is directed by Nicolas
Breuillaud with AI assistance on proofs and documentation. Lean checks
the proof terms against their definitions and hypotheses.
