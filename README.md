# kernel-R

[![Lean proof checks](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml/badge.svg)](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml)
[![Recursive learning proofs](https://github.com/HevisNico/kernel-R/actions/workflows/recursive-learning.yml/badge.svg)](https://github.com/HevisNico/kernel-R/actions/workflows/recursive-learning.yml)

**Current release** [v0.5.0](https://github.com/HevisNico/kernel-R/releases/tag/v0.5.0) · **Zenodo archive (all versions)** [10.5281/zenodo.23884521](https://doi.org/10.5281/zenodo.23884521)

Kernel R is a small analog learning cell whose behaviour is proved in
Lean 4, tested in a transistor-level simulation, and guarded by a supervisor
that knows when its own guarantees stop. There is no chip.

## What is what

**The problem.** Analog circuits can learn with very little energy, but two
circuits built from the same design never behave alike: each copy ends up
with a different memory.

**The cell.** A Kernel R cell has inputs called *ports*. Each port has a
*gain*: how strongly its pulses charge the cell. The gain is the memory.
When the charge reaches a level, the cell *fires*.

**Learning by a fixed dose.** A pulse that leaves the cell silent raises the
gain of its port by a fixed *dose*. The dose is set by two voltage levels,
not by how fast the circuit discharges, so a slow copy learns the same
amount as a fast one.

**Stopping by itself.** A pulse that makes the cell fire writes nothing.
Trained with identical pulses, a cell therefore stops learning on its own,
at a gain set by its own firing level. No final value is tuned by hand.

**The need.** The number of doses a port must receive before it fires is its
*need*. It is a property of the cell. Knowing it in advance means knowing
how the cell will learn.

**Certification.** From margins measured on one cell, a theorem decides
whether that cell's need is guaranteed. Where it says yes, the count is the
predicted one. Where margins are too thin, it says nothing.

**The supervisor.** A task that slowly degrades must be observed and
repaired. The supervisor decides when, keeps the task in service at a
fraction of the cost of constant checking, never stops looking where its
next error could appear, and refuses to claim safety when its own
assumption is broken.

**Three kinds of evidence**, marked throughout:

| Mark | Meaning |
|---|---|
| **Lean** | A theorem checked by the Lean proof assistant, from stated definitions and hypotheses |
| **simulation** | A transistor-level simulation in the SkyWater 130 nm process with ngspice; predictions dated before the runs |
| **experiment** | A discrete model run once, after its predictions and code were published |

## Main results

| Result | Evidence |
|---|---|
| One pulse adds a fixed dose, whatever the discharge rate, with ±10% fabrication variation | Lean |
| Trained with identical pulses, a cell stops by itself, for any start gain and a firing level from 0.95 to 1.05 | Lean |
| Networks of trained cells of any size behave as the single cells predict; two cells decide a coincidence; `2k + 1` cells find a number among `2^k` | Lean |
| The need stays exact while the errors on start gain, doses and firing level stay within half a dose | Lean |
| A transistor-level cell trains and stops by itself; 22 of 24 registered checks and predictions hold | simulation |
| On 200 new simulated ports, 37 are certified by preregistered rules and 57 by a directional rule fixed afterwards, from margins measured on their own runs; every certified count is the predicted one | simulation + Lean |
| On 1 140 fresh noisy trials of those 57 ports (same cells, new noise), the count is always right: under 0.26% error per trial at 95% confidence | simulation |
| A supervisor keeps a degrading task in service from dated observations, at 40 to 44% less cost than constant checking, with no missed danger | Lean + experiment |
| When its assumption breaks, it detects it at its next probe, refuses, recovers without false safety claims, and resumes only on a fresh external authorization | Lean + experiment |

## 1. The cell (Lean)

A complete ERROR phase of a port's sensor raises the log-gain of that port by

```text
Δz = 8 × (entry − exit)
```

where `entry` and `exit` are the two thresholds of the phase. The discharge
rate cancels. The write happens only while the cell is ready; after a FIRE
the cell is protected and nothing is written.

- **Fixed dose.** A single cell trained by one pulse fires on a later read,
  in every complete run.
  [`training_read_every_complete`](research/recursive-learning/native/Thresholds/ParameterTraining.lean)
- **Stops by itself.** Training ends at a gain set by the cell's firing
  level; two trained ports read together fire within a proved window.
  [`stop_training_exists`](research/recursive-learning/native/Training/TrainingLoop.lean)
- **One chip, one behaviour.** Two complete runs from the same start agree
  on the end state and every firing date.
  [uniqueness](proof/lean/KernelR/HybridParameterUniversalExecution.lean)
- **Networks.** Single-cell descriptions compose into any network with
  forward wires; trained chains hold at every length; two cells decide a
  coincidence; a search with `2k + 1` cells gives a hidden number in binary.
  [`acyclic_network_states`](research/recursive-learning/native/Network/AcyclicNetwork.lean) ·
  [`trained_coincidence_network`](research/recursive-learning/native/Training/TrainedCoincidence.lean) ·
  [`successive_search`](research/recursive-learning/native/Search/SuccessiveSearch.lean)
- **Tolerance.** If start-gain, dose and firing-level errors stay within
  half a dose, the need is exact. A directional version asks only an upper
  bound for silence and a lower bound for firing.
  [`needAlong_of_cumulative_tolerance`](research/recursive-learning/native/Search/VariableNeedTolerance.lean) ·
  [`needAlong_of_asymmetric_cumulative_tolerance`](research/recursive-learning/native/Search/AsymmetricNeedTolerance.lean)

Regime: firing level 0.95 to 1.05, ERROR entry 0.07 to 0.08, dose at most
1/20 for the read windows (3/50 for the wider ones), pulses at least 22
units apart, other parameters within ±10%. Cell laws: [model](model/CELL.md).

## 2. A simulated circuit, certified port by port (simulation + Lean)

A transistor-level cell trains and stops by itself across mismatch, noise,
corners and temperature, and maintains itself under a leak.
[circuit study](research/circuit/README.md)

On 100 new cells (200 ports), the tolerance theorem is applied to each port
with bounds measured on its own run. The first three steps were registered
before they ran. The directional rule was fixed afterwards and applied to
the same 200 ports, so it is retrospective; the repetitions test it on new
noise but on the same cells. It has not yet been tried on new cells.

| Step | Ports certified | Counts contradicted |
|---|---|---|
| Margins measured, two conditions assumed | 59 | 0 |
| Threshold of each cell measured | 58 | 0 |
| Gain also measured independently | 37 | 0 |
| Directional rule (silence and firing bounded separately), retrospective | 57 | 0 |
| 20 fresh noisy repetitions of the 57 ports | 1 140 of 1 140 trials right | 0 |

Every port whose count differs from its prediction is outside the certified
domain. In 925 of the 1 140 repetitions, the port is certified again from
the measures of that repetition alone, with no wrong count.
[certification](research/circuit/certification/REPORT.md) ·
[measured conditions](research/circuit/certification-unconditional/REPORT_AMENDMENT_1.md) ·
[directional rule](research/reusable-controller/physical/ASYMMETRIC_PROTOCOL.md) ·
[repetitions](research/circuit/repetition/REPORT.md)

## 3. A supervisor that stays verifiable (Lean + experiment)

A reserve leaks and is repaired by doses. Lean proves that, for the plan the
supervisor builds from dated bounded-error observations, service holds at
every time of the plan and the number of writes is bounded. Stale
observations are refused; every contract expires at a fixed horizon, so the
supervisor cannot save cost by looking less.
[`system_safe`](research/self-certifying-learning/SelfCertifyingLearning/OfferFactory.lean) ·
[supervisor](research/self-certifying-learning/README.md)

Four experiments, each published before its code and run once. The leak
jumps at a date the controllers do not know. A *naive* controller spaces its
probes while it sees no failure; a *prudent* one probes every period.

| Run | What changes | Result |
|---|---|---|
| [v1](research/discrete-refresh-experiment/run-v1/REPORT.md) | leak ceiling known | supervisor 1 247, prudent 2 211, naive 1 014 with 759 dangerous periods unseen |
| [v2](research/adaptive-refresh-experiment/run-v2/REPORT.md) | ceiling estimated from observations, variation law given | supervisor 1 325, no missed danger, 6% above v1 |
| [v3](research/refresh-contract-rupture/run-v3/REPORT.md) | the leak jumps from 10 to 140, beyond that law | detected at the next probe, one period after the jump in this run (probes were 6 periods apart), contract refused, no false safety claim |
| [v4](research/recovery-v4/run-v4/REPORT.md) | v3, then recovery | four unguaranteed repairs, service resumed after a fresh external authorization, zero false safety claims |

The naive controller is cheapest because it observes least, and it is the
one that misses danger. Recovery after a refusal is bounded and makes no
safety claim without a fresh measurement.
[recovery](research/refusal-recovery/README.md) ·
[calibration on the circuit's refresh records](research/adaptive-refresh-experiment/R_CALIBRATION.md)

A reusable teaching controller is also closed natively in R cells over any
number of rounds, and adapts its own search without degrading its true
cost under an assumed evaluator precision.
[controller](research/reusable-controller/README.md)

## Limits

- **No hardware.** The circuit results are simulations of one cell.
- **Read window.** The simulated joint read fires near 0.267 units, outside
  the window proved for the model, (0.239, 0.256].
- **Ideal timing.** The simulated cell receives the arrival of each pulse
  from ideal signals.
- **Certification** pools repetitions under an assumption of interchangeable
  ports; per port, 20 repetitions bound the error only at 13.9%. The gain
  of a read that fires is checked by the current up to 0.75 unit.
- **The supervisor** is proved and tested in discrete models. The variation
  law of v2 is supplied, not learned; the new ceiling of v4 comes from an
  external authority that knows the simulator; the experiment wrappers have
  no end-to-end proof. Its link to the circuit is a nominal calibration.
- **Model quantities.** Pulse amplitude, unit response and some phase
  levels are those of the model.
  [Implementation assumptions](model/IMPLEMENTATION_ASSUMPTIONS.md)

## How to check it

The project pins **Lean 4.35.0** and **Mathlib v4.35.0**. Run each block
from the repository root.

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

Each research package has its own build, axiom audit and CI workflow; see
its README. Every audit allows only `propext`, `Classical.choice` and
`Quot.sound` and fails on admitted proofs. Circuit reports regenerate from
the committed results; experiment evidence is checked in CI.
[Validation ledger](docs/VALIDATION_LEDGER.md) ·
[reviewer's reading path](REVIEW.md)

## History

| Version | Date | What it added |
|---|---|---|
| [v0.1.0](https://github.com/HevisNico/kernel-R/releases/tag/v0.1.0) | 2026-10-30 | Robust composition of N cells |
| [v0.2.0](docs/RELEASE_V0_2_0.md) | 2026-11-02 | A chain of any length learns the same amounts in every cell |
| [v0.3.0](docs/RELEASE_V0_3_0.md) | 2026-11-10 | Learning with realized thresholds; the coincidence decision and its benchmark |
| [v0.4.0](docs/RELEASE_V0_4_0.md) | 2026-11-11 | Training that stops by itself, networks of trained cells, searches |
| [v0.5.0](docs/RELEASE_V0_5_0.md) | 2026-11-13 | A simulated circuit certified port by port; a supervisor that stays verifiable |

All versions: [releases](docs/RELEASES.md).

## Repository map

| Folder | Contents |
|---|---|
| [`model/`](model/README.md) | Cell laws and the chain protocol |
| [`proof/lean/`](proof/lean/README.md) | Core Lean development and audit |
| [`research/recursive-learning/`](research/recursive-learning/README.md) | Trained cells, networks, searches, tolerance |
| [`research/circuit/`](research/circuit/README.md) | Transistor-level simulation, certification and repetition campaigns, circuit-to-model bridge |
| [`research/self-certifying-learning/`](research/self-certifying-learning/README.md) | Supervisor proofs; experiments in `discrete-refresh-experiment`, `adaptive-refresh-experiment`, `refresh-contract-rupture`, `refusal-recovery`, `recovery-v4` |
| [`research/reusable-controller/`](research/reusable-controller/README.md) | Reusable and adaptive controller, physical bridge, directional rule |
| [`research/`](research/README.md) | All research packages |
| [`docs/`](docs/RELEASES.md) | Releases, theorem guides, trusted base, related work |
| [`archive/`](archive/README.md) | Earlier experiments and specifications |

## Related work, origin and license

Rate-independent increments, stop-learning rules, run-time contracts and
formal verification of spiking networks all have precedents. Kernel R
studies one combination of them, proved and tested end to end.
[Comparison and references](docs/RELATED_WORK.md)

This work draws inspiration from Nicolas Breuillaud's
[*The Reset Operator: A Structural Constraint on Recursivity*](https://ssrn.com/abstract=6964960).
Nicolas Breuillaud directs the work with assistance from **Claude**
(Anthropic) and **ChatGPT** (OpenAI) on models, code, proofs and
documentation. Lean checks the proof terms against their definitions and
hypotheses. Physical assumptions and claims outside those proofs remain
subject to independent review.

Source code is [MIT](LICENSE). Documents, proofs, data and other non-code
material are CC BY 4.0 under [LICENSE-docs.md](LICENSE-docs.md).
