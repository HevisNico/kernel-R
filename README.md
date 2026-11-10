# kernel-R

[![Lean proof checks](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml/badge.svg)](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml)
[![Recursive learning proofs](https://github.com/HevisNico/kernel-R/actions/workflows/recursive-learning.yml/badge.svg)](https://github.com/HevisNico/kernel-R/actions/workflows/recursive-learning.yml)

**Current release** [v0.3.0](https://github.com/HevisNico/kernel-R/releases/tag/v0.3.0) · **Zenodo archive (all versions)** [10.5281/zenodo.23884521](https://doi.org/10.5281/zenodo.23884521)

Kernel R is a mathematical model of an asynchronous analog learning cell.
Its Lean 4 proofs start from the cell's differential equations and establish
what networks of these cells learn. The work is at the model stage.

## The R cell

While ready, an R cell charges in response to input pulses. When its
charge crosses the firing threshold, it emits a pulse and enters a
protected recovery phase. It learns each port's input gain while
ready and its recovery rate while protected.

Fabrication mismatch can make the same training pulse produce different
updates in nominally identical devices. Kernel R couples a sensor's
discharge to a memory update. When a complete ERROR phase stays eligible
and the gain remains below its cap, the increase in log-gain is

```text
Δz = 8 × (entry − exit)
```

The discharge rate changes how long the phase lasts and cancels from the
update. The sensor itself ends the update at the exit threshold. With
nominal thresholds 0.1 and 0.025, the increment is 0.6. A full MARK phase
while the cell stays protected adds 0.1 to its recovery rate at nominal
thresholds, provided the learning gates stay open and the rate stays
below its cap.

See the [cell laws](model/CELL.md) and the [glossary](docs/GLOSSARY.md).

## What is proved

### 1. Chains of any finite length learn the same increments

Under the [chain protocol](model/CHAIN_PROTOCOL.md), every complete run
raises each cell's active input log-gain by 2.4 and its recovery rate by 0.3.
The increments hold across independent fixed fabrication variation of up to
±10% and bounded wire jitter. For each fixed choice of parameters, birth
data and delays, complete runs agree on each cell's ordered firing dates
regardless of the legal order of simultaneous events. Lean constructs a
complete run in both first-contact and upward-crossing semantics. The
root ends with at least eight pulses, each within 0.15 model units of a
period-four rhythm.

Each cell first receives its own preparation train while the links are off,
which writes three of a relay's four active-port doses. The links then open,
the leaf receives a regular source rhythm, and each relay receives its
fourth dose from its neighbour. The theorem uses nominal thresholds and
the declared birth bounds, including `10⁻⁵` tolerances on the initial
charges, log-gains and recovery rate.

[`TrustedHeadline.every_finite_chain`](proof/lean/KernelR/TrustedHeadline.lean) ·
[theorem guide](docs/UNIVERSAL_FINITE_CHAIN.md) ·
[trusted definitions](docs/TRUSTED_BASE.md)

### 2. Thresholds are parameters, and runs stay unique

Charge thresholds are fields of each cell's parameters. For any finite
network, under the declared physical and threshold bounds, compare two
finite first-contact runs from the same initial snapshot with the same
realized parameters and fixed router. If both are complete through the
same horizon, they have the same endpoint up to pending-list order and the
same ordered firing dates in each cell.

[semantics](proof/lean/KernelR/HybridParameterExecution.lean) ·
[uniqueness](proof/lean/KernelR/HybridParameterUniversalExecution.lean)

### 3. One training pulse and one read tolerate threshold error

A single cell trained by one pulse fires on a later read of the same port
in every run complete through the certified read horizon. With the ERROR
exit centered at 0.025, the theorem allows ±5% on both ERROR thresholds and
FIRE. A separate instance lowers the nominal exit to 0.01 and reads later.
That gives a larger dose (0.72 at nominal thresholds) and a longer
discharge. The same absolute threshold errors account for a smaller
fraction of the larger dose.

[`training_read_every_complete` and `training_read_exit_001_every_complete`](research/recursive-learning/native/ParameterTraining.lean)

### 4. Two cells learn a coincidence task

Two cells each learn one of two ports. At 100 µs per model unit, the
receiver requires exactly one report from each cell by the deadline,
with their arrivals less than 15 µs apart. Lean proves that this happens
exactly when both test ports match the training and the programmed input
offset is zero. The benchmark timing is motivated by a published task.

- **Kernel R meets the full contract.** A complete run exists for each
  admissible trial and every complete run gives the expected decision.
  At 100 µs per model unit, the guarantee covers ±10% fabrication,
  ±3% FIRE error and absolute variation of up to 0.001 at ERROR entry and
  0.00025 at ERROR exit on each trained port.
- **The reduced constant-current comparator fails.** With ±10% current
  variation and nominal ERROR endpoints, one admissible positive trial
  fails for every shared current and duration, including settings that
  reach the gain cap.

The R proof uses native hybrid executions with realized thresholds. The
comparator proof uses the reduced read model, with an eligible write and
quiet charge relaxation after training.

[`coincidence_exit_001_separation`](research/recursive-learning/native/CoincidenceSeparation.lean) ·
[module guide](research/recursive-learning/native/README.md#coincidence-timing-with-an-error-exit-near-001)

## What the benchmark showed

The protocol was registered before the first sweep. At 100 µs per model
unit in the wide fabrication box, the baseline R setting passed 16 of 36
ERROR × FIRE boxes on the sampled points, the best tested constant-current
timer passed 12, and the long timed discharge passed 27. The long
discharge covered every tested box in which baseline R passed. The capped
timer also passed all 36 boxes at the same scale in the narrow fabrication
box.

R ends its write at a state threshold without a clock. In this sweep,
the long timed discharge achieved the higher timing score. The
[exit-threshold sweep](research/recursive-learning/coincidence/EXIT_TRADEOFF_RESULTS.md)
reports the timing and memory-capacity trade-off for lower exit thresholds.

[protocol](research/recursive-learning/COINCIDENCE_BENCHMARK.md) ·
[numerical results](research/recursive-learning/coincidence/RESULTS.md)

## Scope

- **A mathematical model.** Hardware measurements would be needed for
  experimental validation.
- **Small tasks.** The tolerant learning results cover one dose in one
  or two cells. The [exact counting theorem](docs/EXACT_DOSE_COUNTING.md)
  uses nominal thresholds.
- **Exact quantities.** Actuation factors are exact. The coincidence
  theorem uses a trained-port birth gain of exactly 1.2.
- **Receiver.** The coincidence receiver is a decision rule on the
  two cells' emitted dates.
- **Complete runs.** Theorems compare runs complete through a horizon.
  A delivery due before the previous pulse expires on the same port blocks
  completion through that date. The declared tasks have complete witnesses.

The native guide covers [binary search for a hidden need](research/recursive-learning/native/README.md#searching-for-an-unknown-need),
[reuse of a learned choice](research/recursive-learning/native/README.md#reusing-a-learned-choice-in-two-rounds)
and the [8 → 7 → 6 teaching loop](research/recursive-learning/native/README.md#the-8--7--6-experiment-with-learner-readouts).
See also [chain progress](proof/lean/PROGRESS.md) and
[port-memory saturation](docs/GAIN_MEMORY_SATURATION.md).

## Related work

Analog synaptic increments that contain no discharge rate already exist.
The closest precedent we examined is the switched-capacitor synapse of
Noack et al., whose step is set by a capacitor ratio and control voltages
in a clocked circuit. Kernel R integrates a self-timed discharge between
two state thresholds and machine-checks how the updates compose.
[Noack et al.](https://www.frontiersin.org/journals/neuroscience/articles/10.3389/fnins.2015.00010/full) ·
[full comparison](docs/RELATED_WORK.md)

## How to check it

The project pins **Lean 4.35.0** and **Mathlib v4.35.0**.
Run each block from the repository root.

```sh
cd proof/lean
lake exe cache get
lake build
lake build Audit
```

```sh
cd research/recursive-learning/native
lake exe cache get
lake build
```

The core audit and the native package's default audit allow only
`propext`, `Classical.choice` and `Quot.sound` and fail on admitted proofs.
See the [validation ledger](docs/VALIDATION_LEDGER.md).

The [reviewer's reading path](REVIEW.md) starts with how the Lean
definitions represent the written model.

## Repository map

| Folder | Contents |
|---|---|
| [`model/`](model/README.md) | Cell laws and the chain protocol |
| [`proof/lean/`](proof/lean/README.md) | Core Lean development and audit |
| [`research/`](research/README.md) | Tolerant training, coincidence proofs and benchmark |
| [`docs/`](docs/UNIVERSAL_FINITE_CHAIN.md) | Theorem guides, trusted base, provenance |
| [`archive/`](archive/README.md) | Earlier experiments and specifications |

## Origin, AI assistance and license

This work draws inspiration from Nicolas Breuillaud's
[*The Reset Operator: A Structural Constraint on Recursivity*](https://ssrn.com/abstract=6964960).

Nicolas Breuillaud directs the work with assistance from **Claude**
(Anthropic) and **ChatGPT** (OpenAI) on models, code, proofs and
documentation. Lean checks the proof terms against their definitions and
hypotheses. Physical assumptions and claims outside those proofs remain
subject to independent review.

Source code is [MIT](LICENSE). Documents, proofs, data and other non-code
material are CC BY 4.0 under [LICENSE-docs.md](LICENSE-docs.md).
