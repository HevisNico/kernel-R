# kernel-R

[![Lean proof checks](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml/badge.svg)](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml)
[![Recursive learning proofs](https://github.com/HevisNico/kernel-R/actions/workflows/recursive-learning.yml/badge.svg)](https://github.com/HevisNico/kernel-R/actions/workflows/recursive-learning.yml)
[![Network stability proofs](https://github.com/HevisNico/kernel-R/actions/workflows/network-stability.yml/badge.svg)](https://github.com/HevisNico/kernel-R/actions/workflows/network-stability.yml)

**Current release** [v1.0.0](https://github.com/HevisNico/kernel-R/releases/tag/v1.0.0) · **Zenodo archive (all versions)** [10.5281/zenodo.23884521](https://doi.org/10.5281/zenodo.23884521)

> In an analog network that learns in closed loop, learning stops by itself:
> every memory settles after finitely many writes, whatever the order of the
> pulses and even while they keep arriving. Its final value is computed
> before the network is run, from measurements made cell by cell; a
> measurable margin says when that computation is guaranteed.

Kernel R is a small analog learning cell, and networks of such cells, whose
behaviour is proved in Lean 4 and tested in transistor-level simulation.
Before a two-cell network was ever run, its final memory was computed from
measurements of each cell alone, on cells no one had looked at; the network
then learned exactly that memory. There is no chip.

## What is what

**The problem.** Analog circuits can learn with very little energy, but two
circuits built from the same design never behave alike: each copy ends up
with a different memory, and what a network of them will learn is usually
found out by running it.

**The cell.** A Kernel R cell has inputs called *ports*. Each port has a
*gain*: how strongly its pulses charge the cell. The gain is the memory.
When the charge reaches a level, the cell *fires*.

**Learning by a fixed dose.** A pulse that leaves the cell silent raises the
gain of its port by a fixed *dose*. The dose is set by two voltage levels,
not by how fast the circuit discharges, so a slow copy learns the same
amount as a fast one.

**Stopping by itself.** A pulse that makes the cell fire writes nothing. A
port therefore stops learning once it fires, and later pulses leave its
memory unchanged. No final value is tuned by hand.

**The need.** The number of doses a port must receive before it fires is its
*need*. It is a property of the cell. Knowing it in advance means knowing
how the cell will learn.

**Networks.** A cell that fires sends a pulse to another cell, so cells
train each other in a closed loop. A *margin* says how far each read is from
changing its outcome. While every read has room for its error, the
network's final memory is fixed by the needs of its ports, whatever the
order of the pulses.

**The supervisor.** A task that slowly degrades must be observed and
repaired. The supervisor decides when, keeps the task in service at a
fraction of the cost of constant checking, and refuses to claim safety when
its own assumption is broken.

**Three kinds of evidence**, marked throughout:

| Mark | Meaning |
|---|---|
| **Lean** | A theorem checked by the Lean proof assistant, from stated definitions and hypotheses |
| **simulation** | A transistor-level simulation in the SkyWater 130 nm process with ngspice; predictions published before the runs |
| **experiment** | A discrete model run once, after its predictions and code were published |

## Main results

| Result | Evidence |
|---|---|
| One pulse adds a fixed dose, whatever the discharge rate; a cell trained by identical pulses stops by itself | Lean |
| In a network with explicit error budgets per read, every run makes finitely many writes, no memory reaches its rail, the final memory does not depend on the order of the pulses, and it settles even when pulses never stop | Lean |
| For every ring of N ≥ 2 analog cells whose parameters pass a rational check, the native analog execution follows that network model exactly and ends in the predicted memory | Lean |
| Before a two-cell closed-loop network was simulated, the final memory of its 16 ports on four new mismatched instances was computed from per-cell measurements: 16 of 16 exact, final values within 2.4 µV for a dose of about 1.35 mV | simulation (preregistered) |
| In those runs, every port kept its memory unchanged through the 4 to 15 pulses it received after its last write; a predictor without the measurements would have been wrong on 11 of 16 ports; outside the timing condition the prediction fails, as predicted | simulation (preregistered) |
| On 200 simulated ports, every port certified from its own margins has the predicted count; 1 140 of 1 140 noisy repetitions right | simulation + Lean |
| A supervisor on the simulated circuit keeps a leaking memory in service through a tripled leak: 0 failed services of 2 232, against 44 of 240 for the cell left to itself; 14 of 14 predictions hold | simulation (preregistered) + Lean |
| The cell laid out in SKY130 with extracted capacitances: 7 of 16 ports certified, no wrong count | simulation |

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
- **Forward networks and searches.** Single-cell descriptions compose into
  any network with forward wires; two cells decide a coincidence; a search
  with `2k + 1` cells gives a hidden number in binary.
  [`acyclic_network_states`](research/recursive-learning/native/Network/AcyclicNetwork.lean) ·
  [`trained_coincidence_network`](research/recursive-learning/native/Training/TrainedCoincidence.lean) ·
  [`successive_search`](research/recursive-learning/native/Search/SuccessiveSearch.lean)
- **Tolerance.** If start-gain, dose and firing-level errors stay within
  half a dose, the need is exact.
  [`needAlong_of_cumulative_tolerance`](research/recursive-learning/native/Search/VariableNeedTolerance.lean) ·
  [`needAlong_of_asymmetric_cumulative_tolerance`](research/recursive-learning/native/Search/AsymmetricNeedTolerance.lean)

Regime: firing level 0.95 to 1.05, ERROR entry 0.07 to 0.08, dose at most
1/20 for the read windows (3/50 for the wider ones), pulses at least 22
units apart, other parameters within ±10%. Cell laws: [model](model/CELL.md).

## 2. Networks that learn in closed loop (Lean)

**The network theorem.** Pulses are admitted in the order of their dates;
each read of a port has an error budget. If every read has room for its
budget, then along every run: each port makes finitely many writes and stays
below its rail; the final memory is the same whatever the order of
admissions, ties included; and with traffic that never stops, the memory
still settles after a finite cut.
[`dated_network_memory`](research/network-stability/DatedNetwork.lean) ·
[`memory_stabilizes`](research/network-stability/PerpetualFeedback.lean) ·
[theorem guide](research/network-stability/THEOREM.md)

**From the analog cell to the network model.** The network theorem is about
a discrete model. Two results show that executions of the analog cell model
(continuous charge, mode jumps, real routing) follow it exactly:

- the two-cell reciprocal network, over its 77 transactions, coordinate by
  coordinate:
  [`nominal_reciprocal_refinement`](research/network-stability/ReciprocalPostBirth.lean);
- **every ring of N ≥ 2 cells** whose delays and gains pass a rational
  membership check: the native execution exists, matches the network model
  transaction by transaction, stays below its rails, and every complete
  execution ends in the same, predicted memory.
  [`NativeRingRefinement`](research/network-stability/NativeRingTarget.lean) (frozen statement) ·
  [`native_ring_refinement`](https://github.com/HevisNico/kernel-R/blob/419e4c66aae2921416993dd4e7c64996e05dc98f/research/network-stability/NativeRingRefinement.lean) (proof)

Each condition of the ring class is rejected by a checked counterexample
([examples](research/network-stability/NativeRingExamples.lean)).

## 3. Predicting what a network will learn (simulation, preregistered)

Two cells joined in a loop, at transistor level, each with its own mismatch
sample. The predictions, the rules and the analysis were published before
any network was simulated; each machine was launched once.
[preregistration and report](https://github.com/HevisNico/kernel-R/blob/94d0f7f93bc7a8dcef825d0ed4df420938ff69cb/research/network-circuit-campaign/REPORT.md) ·
[design](research/network-circuit/README.md)

1. Each cell is measured alone: the gap of each port to its threshold, its
   dose, the help of a recent pulse, the bracket of the threshold.
2. From those numbers alone, the network theorem gives the word each port
   will learn, if every read has room for its budget.
3. The predictions are pushed; then the network is simulated.

| | Result |
|---|---|
| Instances measured / with room for the budget | 5 of 6 / 4 (one instance had an inconsistent threshold scan and was excluded by the preregistered rule) |
| Port words predicted and observed, without noise | 16 of 16 the same |
| Final stored voltages | within 0.0007 to 0.0024 mV of the predicted values; one dose is about 1.35 mV |
| Pulses after the last write | 4 to 15 per port, all predicted, none of them writes |
| Predictor that ignores the measurements | wrong on 11 of the 16 ports |
| Negative control, pulses 8 units apart instead of 16 | 3 of 4 ports learn another word, as predicted |
| Runs with noise | reported, no claim: most words unchanged, some not |

The predictions reproduce byte for byte from the evidence of the measures.
The waveforms are public
([`WAVEFORMS.md`](https://github.com/HevisNico/kernel-R/blob/94d0f7f93bc7a8dcef825d0ed4df420938ff69cb/research/network-circuit-campaign/WAVEFORMS.md)).

## 4. A circuit certified port by port (simulation + Lean)

A transistor-level cell trains and stops by itself across mismatch, noise,
corners and temperature. On 100 new cells (200 ports), the tolerance theorem
is applied to each port with bounds measured on its own run.
[circuit study](research/circuit/README.md)

| Step | Ports certified | Counts contradicted |
|---|---|---|
| Margins measured, two conditions assumed | 59 | 0 |
| Threshold of each cell measured | 58 | 0 |
| Gain also measured independently | 37 | 0 |
| Directional rule (silence and firing bounded separately), retrospective | 57 | 0 |
| 20 fresh noisy repetitions of the 57 ports | 1 140 of 1 140 trials right | 0 |

The repetitions bound the error per trial below 0.29% at 95% confidence,
counting the 1 040 independent runs. The directional rule was fixed after
the 200 ports were seen; it has not yet been tried on new cells.
[certification](research/circuit/certification/REPORT.md) ·
[directional rule](research/reusable-controller/physical/ASYMMETRIC_PROTOCOL.md) ·
[repetitions](research/circuit/repetition/REPORT.md)

## 5. A supervisor that stays verifiable (Lean + experiment + simulation)

A memory leaks and is repaired by doses. Lean proves that, for the plan the
supervisor builds from dated bounded-error observations, service holds at
every time of the plan and the number of writes is bounded; stale
observations are refused, and every contract expires.
[`system_safe`](research/self-certifying-learning/SelfCertifyingLearning/OfferFactory.lean) ·
[supervisor](research/self-certifying-learning/README.md)

In discrete experiments it keeps a degrading task in service at 40 to 44%
less cost than constant checking with no missed danger, detects a broken
assumption at its next probe, refuses, and resumes only on a fresh external
authorization ([v1](research/discrete-refresh-experiment/run-v1/REPORT.md),
[v2](research/adaptive-refresh-experiment/run-v2/REPORT.md),
[v3](research/refresh-contract-rupture/run-v3/REPORT.md),
[v4](research/recovery-v4/run-v4/REPORT.md)).

On the simulated circuit, with the leak tripled at a date it does not know,
the supervised cell failed no service in 93 runs over nine corners and
temperatures (2 232 services); left to itself, the cell failed 44 of 240.
14 of 14 preregistered predictions hold.
[supervisor campaign](research/sky130-supervisor-campaign/REPORT.md)

## 6. Layout (simulation)

One cell laid out in SKY130 with the open-source flow, DRC and LVS clean,
capacitances extracted. On layout 2.2, 7 of 16 ports are certified again,
with no wrong count; three rest-state readings are refused by a few
nanovolts. About 30 to 40 ports per mm². First nominal energy figures, on
the first extracted layout with ideal sources: about 372 µW at rest and about
15.5 nJ per write.
[conclusion](research/sky130-layout/CONCLUSION.md) ·
[energy](research/sky130-layout/phase1/P_REPORT.md)

## Limits

- **No hardware.** Every circuit result is a simulation (SKY130, ngspice).
- **The network experiment** has two cells, one calendar, 27 °C, the typical
  corner with mismatch, and a claim without noise. The noise model overstates
  low-frequency noise; a claim under noise is left to a separate study.
- **Two objects.** The prediction of the simulated network uses the network
  theorem with hypotheses checked on the run (pulse separation, doses only).
  The refinement from the analog cell model is proved for the ring class
  and the reciprocal witness, not for the simulated transistor network.
- **Ideal timing and router.** The simulated cells receive pulses from
  ideal signals; the network's router is ideal.
- **Read window.** The simulated joint read fires near 0.267 units, outside
  the window proved for the model, (0.239, 0.256].
- **Certification** pools repetitions under an assumption of interchangeable
  ports; the directional rule is retrospective.
- **The supervisor's** variation law is supplied, not learned, and the new
  ceiling after a rupture comes from an external authority.
- **Layout** extraction is capacitance only; 9 of 16 ports are not
  certified on layout 2.2.
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

```sh
bash research/network-stability/check.sh
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
| [v1.0.0](https://github.com/HevisNico/kernel-R/releases/tag/v1.0.0) | 2026-11 | Closed-loop networks: the network theorem, the native ring refinement for every N, the preregistered prediction of a network's memory; the supervisor on the circuit; the layout |

All versions: [releases](docs/RELEASES.md).

## Repository map

| Folder | Contents |
|---|---|
| [`model/`](model/README.md) | Cell laws and the chain protocol |
| [`proof/lean/`](proof/lean/README.md) | Core Lean development and audit |
| [`research/recursive-learning/`](research/recursive-learning/README.md) | Trained cells, forward networks, searches, tolerance |
| [`research/network-stability/`](research/network-stability/THEOREM.md) | The network theorem and the native refinements |
| [`research/network-circuit/`](research/network-circuit/README.md) | Networks of simulated cells and the prediction campaign |
| [`research/circuit/`](research/circuit/README.md) | Transistor-level simulation, certification and repetition campaigns |
| [`research/sky130-supervisor-campaign/`](research/sky130-supervisor-campaign/REPORT.md) | The supervisor on the simulated circuit |
| [`research/sky130-layout/`](research/sky130-layout/README.md) | Layout, extraction and certification of the laid-out cell |
| [`research/self-certifying-learning/`](research/self-certifying-learning/README.md) | Supervisor proofs; discrete experiments in the refresh folders |
| [`research/`](research/README.md) | All research packages |
| [`docs/`](docs/RELEASES.md) | Releases, theorem guides, trusted base, related work |
| [`archive/`](archive/README.md) | Earlier experiments and specifications |

## Related work, origin and license

Learning that stops once a unit responds correctly, stop-learning synapses,
order-independent halting in abelian networks, and formal verification of
spiking and hybrid systems all have precedents. Kernel R studies one
combination of them, proved and tested end to end; no precedent was found
for the refinement from an analog cell model to a network model, or for a
preregistered prediction of a network's exact memory from per-cell
measurements. [Comparison and references](docs/RELATED_WORK.md)

This work draws inspiration from Nicolas Breuillaud's
[*The Reset Operator: A Structural Constraint on Recursivity*](https://ssrn.com/abstract=6964960).
Nicolas Breuillaud directs the work with assistance from **Claude**
(Anthropic) and **ChatGPT** (OpenAI) on models, code, proofs and
documentation. Lean checks the proof terms against their definitions and
hypotheses. Physical assumptions and claims outside those proofs remain
subject to independent review.

Source code is [MIT](LICENSE). Documents, proofs, data and other non-code
material are CC BY 4.0 under [LICENSE-docs.md](LICENSE-docs.md).
