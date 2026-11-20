# kernel-R

[![Lean proof checks](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml/badge.svg)](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml)
[![Network stability proofs](https://github.com/HevisNico/kernel-R/actions/workflows/network-stability.yml/badge.svg)](https://github.com/HevisNico/kernel-R/actions/workflows/network-stability.yml)

**Current release** [v1.1.0](https://github.com/HevisNico/kernel-R/releases/tag/v1.1.0) · **Zenodo archive (all versions)** [10.5281/zenodo.23884521](https://doi.org/10.5281/zenodo.23884521)

> In an analog network that learns in closed loop, learning stops by itself:
> while every read has room for its error budget, every memory settles after
> finitely many writes, whatever the order of the pulses and even while they
> keep arriving. Its final value is computed before the network is run, from
> measurements made cell by cell.

Kernel R is a small analog learning cell, and networks of such cells. Their
behaviour is proved in Lean 4 and tested in transistor-level simulation.
In three preregistered experiments on cells no one had looked at, the final
memory of every port was computed from measurements of each cell alone,
before the network was run; the networks then learned exactly that memory,
52 ports out of 52. In a further preregistered experiment, a network of
three such cells learned a Boolean function, `(A and B) or (C and D)`, and
answered all 16 input patterns as predicted, on 4 of 4 eligible instances.
The Lean theory behind that experiment covers every monotone Boolean
function; the experiment tests one. There is no chip.

## Words used here

| Word | Meaning |
|---|---|
| **cell** | one analog circuit that learns; a network is several cells that send pulses to each other |
| **port** | an input of a cell; each port has its own memory |
| **gain** (the **memory**) | how strongly a pulse on a port charges the cell; stored as a voltage on a capacitor |
| **read** | a pulse arriving on a port: it either leaves the cell silent or makes it **fire** |
| **dose** | the fixed amount a silent read adds to the gain of its port (about 1.35 mV); a read that fires writes nothing |
| **need** | the number of doses a port takes before it fires; it differs from cell to cell |
| **closed loop** | the pulses a cell emits when it fires train the other cells, and come back |
| **freeze** | the moment after which no port writes any more, although pulses keep coming |
| **mismatch** | two copies of one design never behave alike; each simulated cell gets its own random sample |
| **margin**, **error budget** | how far a read is from changing its outcome, and how much error it is allowed; a read with **room** has a margin larger than its budget |
| **eligible instance** | a simulated network whose ports all have room, so that the theorem applies to it; in campaign 6, an instance whose measures complete and whose prediction passes the Lean check |
| **preregistered** | the predictions and the rules of analysis were published, alone, before any run they concern |
| **guarded model** | the discrete model of a network (counts of doses, read outcomes) in which the network theorem is proved |
| **native model** | the continuous model of the analog cell (charge, phases, pulses in time) |
| **Lean** | a proof assistant: a **Lean** result is a theorem checked by a machine from stated definitions and hypotheses |

## Main results

| Result | Evidence |
|---|---|
| A cell trained by identical pulses stops learning by itself, each silent read adding one fixed dose | Lean |
| In a network where every read has room, every run makes finitely many writes, no memory saturates, the final memory does not depend on the order of the pulses, and it freezes even when pulses never stop | Lean |
| For three classes of ring networks, for every number of cells N ≥ 2, the native model follows the guarded model exactly and ends in the predicted memory | Lean |
| A two-layer network of cells trained by its own pulses can express every monotone Boolean function, and only those; for any number of cells and inputs, a run whose records satisfy three checkable premises has trained as predicted and answers every input pattern as predicted; the same holds for layered networks of any depth; with each input also given as its complement on a second line, every Boolean function | Lean |
| Final memory of every port computed before the run from per-cell measures: 52 of 52 ports exact without noise, over three campaigns and two kinds of network | simulation, preregistered |
| Under the simulator's noise, on twelve new instances: 21 of 21 learned states and 11 of 11 exact words | simulation, preregistered |
| A network of three cells, trained only by its own pulses, learns `(A and B) or (C and D)`: its training and its answers to all 16 input patterns, computed before the run from per-cell measures, held on 4 of 4 eligible instances (campaign 6) | simulation, preregistered |

Simulations use the SkyWater 130 nm process (SKY130) and ngspice, at the
level of transistors.

## 1. The cell

A silent read raises the gain of its port by a fixed dose, set by two
voltage levels and not by how fast the circuit discharges. A read that fires
writes nothing. A port therefore takes doses until it fires, and stops: the
final memory is set by the cell itself, not tuned by hand.
[cell laws](model/CELL.md) ·
[`stop_training_exists`](research/recursive-learning/native/Training/TrainingLoop.lean) ·
[tolerance](research/recursive-learning/native/Search/VariableNeedTolerance.lean)

## 2. Networks, proved for every N

**The network theorem** (guarded model). If every read has room for its error
budget: each port makes finitely many writes and stays below its rail; the
final memory is the same in whatever order the pulses are admitted; and with
traffic that never stops, the memory still freezes after a finite time.
[`dated_network_memory`](research/network-stability/DatedNetwork.lean) ·
[`memory_stabilizes`](research/network-stability/PerpetualFeedback.lean) ·
[guide](research/network-stability/THEOREM.md)

**From the analog cell to the network model.** For three classes of rings,
for every N ≥ 2 and every set of parameters that passes a rational check,
a native execution exists, follows the guarded model transaction by
transaction, stays below its rails and ends in the predicted memory; every
other complete execution ends in the same state.

| Class | What happens in it | Theorem |
|---|---|---|
| ring with one launch | one pulse goes round once; one write in all | [`native_ring_refinement`](research/network-stability/NativeRingRefinement.lean) |
| periodic ring | a launch every period, forever; the memory freezes at its predicted value while pulses keep arriving | [`native_periodic_ring_refinement`](research/network-stability/NativePeriodicRingExecution.lean) |
| multi-token ring | several pulses in flight, repeated training, pulses admitted while a cell recovers | [`native_multi_token_refinement`](research/native-multitoken/NativeExternalRows.lean) |

Each condition of each class is rejected by a checked counterexample.

**Networks that compute a function** (guarded model, added after v1.0.0).
A two-layer network is given by its parameters: each first-layer cell learns
a conjunction of inputs, and each output cell learns a disjunction of
first-layer lines. A Boolean function is **monotone** when switching an
input on never turns its answer from true to false.

- For any number of first-layer cells, output cells and inputs, and any
  parameters that pass a check: if the records of a run also show training
  slots separated in time and calibrated reads, then every port stopped
  training as predicted and every output answers every input pattern as the
  parameters predict.
  [`two_layer_monotone_recognition_one_sided`](research/learned-coincidence/MonotoneOneSidedRecognition.lean)
- The functions these networks express are exactly the monotone ones.
  [`monotone_characterization`](research/learned-coincidence/MonotoneCharacterization.lean)
- Each of the three premises is decided on finite records by a checker,
  proved [sound](research/learned-coincidence/MonotonePremiseSoundness.lean)
  and [complete](research/learned-coincidence/MonotonePremiseCompleteness.lean).
- Both results hold for layered networks of any depth, built from two-port
  cells, with four checkers.
  [`layered_monotone_recognition_one_sided`](research/learned-coincidence/LayeredMonotoneRecognition.lean) ·
  [`layered_monotone_characterization`](research/learned-coincidence/LayeredMonotoneCharacterization.lean) ·
  [checkers](research/learned-coincidence/LayeredMonotoneCheckerProofs.lean)
- **Negation by two rails.** These networks have no negation. With each input
  given on two lines, the input and its complement, every Boolean function is
  the predicted answer of such a network, with no change to the cell. On two
  rails, the exclusive OR of two inputs is the function campaign 6's circuit
  learned, `(A and B) or (C and D)`, read with `A = p`, `B = not q`,
  `C = not p`, `D = q`; campaign 6 did not test it as an exclusive OR.
  [`every_function_on_two_rails`](research/learned-coincidence/TwoRails.lean) ·
  [note](research/learned-coincidence/TWO_RAILS.md)

These theorems are about records that satisfy their premises. They do not
say that a physical or simulated cell satisfies them; an experiment tests
that, and campaign 6 below is the first, on one function.

## 3. Predicted before the run (simulation, preregistered)

Each campaign follows the same steps, each pushed before the next:
every cell is measured alone; from those numbers only, the memory each port
will learn is computed and published; then the network is simulated, once
per machine; one analysis at the end. Mismatched instances are new in each
campaign.

| Campaign | Network | Eligible | Without noise | Under noise |
|---|---|---|---|---|
| [1](research/network-circuit-campaign/REPORT.md) | two cells in closed loop | 4 of 6 | **16 of 16 ports exact** | no claim |
| [2](research/network-circuit-ring-campaign/REPORT.md) | periodic ring of three cells | 2 of 6 | **8 of 8 exact**, freeze lap exact | exact words 6 of 6; learned state reported as failed (below) |
| [3](research/network-circuit-ring-campaign-3/REPORT.md) | the same ring, corrected measurement, twelve instances | 7 of 12 | **28 of 28 exact**, freeze lap exact | **learned states 21 of 21, exact words 11 of 11** |

- Final stored voltages agree with the predictions within a few µV, and
  every port keeps its memory through all the pulses it receives after its
  last write.
- A predictor that ignores the measures would have been wrong on 11 of 16,
  8 of 8 and 25 of 28 ports: the measures carry the prediction.
- Outside the timing condition (pulses 8 units apart instead of 16) the
  prediction fails, as predicted, in campaigns 1 and 3; in campaign 2 that
  control showed nothing.
- **Campaign 2 under noise.** One port-run is reported as failed, and it was
  a measurement artifact, not a prediction error: the cell fired cleanly and
  wrote nothing, but a 4 ns spike from a testbench edge was counted as a
  write. The verdict stays "fails", the rule accepted in advance.
  Campaign 3 kept that rule and added a write that must last 1 µs; both held.
  [diagnosis](research/network-circuit-ring-campaign-3/DIAGNOSIS_N_OWN.md)
- Every waveform is public on its `evidence/…` branch with its SHA-256 list.

### Campaign 6: a learned function

Campaigns 1 to 3 predict how much each port learns. Campaign 6 predicts what
a network computes. Three cells, each with its own mismatch, are wired in
two layers and trained only by their own pulses; they should learn
`(A and B) or (C and D)`. Each cell is measured alone. From those measures
only, the training of every port and the answer to each of the 16 input
patterns are computed, and a Lean proof checks that this prediction implies
the function. Then the network is simulated.

| | Result |
|---|---|
| Instances | five new ones, four eligible; the fifth was set aside by a rule fixed in advance, because the frozen prediction code raised an error on it |
| Without noise (the primary claim) | **established on 4 of 4**: every training letter and all 16 answers as predicted, with no discrepancy |
| Under noise, per training port | established: 21 port-runs on four instances for one claim, 12 port-runs on two instances for the other, with no failure |
| Under noise, per output | **not established**: two cells held on one instance each, where the rule asks for two; the output cell had no room on any instance, as anticipated before the data |
| Controls | an untrained network fires no output on any of the 16 patterns; a skewed coincidence leaves the first layer silent |
| Runs | 62 of 62 complete; none lost, none repeated |

- [Report](research/learned-dnf-circuit-campaign-6/REPORT.md) · [preregistration](research/learned-dnf-circuit-campaign-6/PREDICTION.md)
- The Lean proof is not specific to this function. It is the general
  theorem of section 2, applied at two first-layer cells, one output cell
  and four inputs.
- The Lean proof certifies the prediction, and the simulation tests what the
  prediction announces. A descriptive check of the theorem's premises on the
  measured runs is true for two of its three checkers and false for the
  calibration checker, for reasons given in the report (comparison M8). No
  verdict depends on it.
- Before the final freeze of the code, a dry run of every stage found
  defects in the campaign's code and procedure. All were fixed before any
  run that counts, and the report lists them.
- Two earlier attempts at this claim, campaigns 4 and 5, stopped before
  testing it. [What happened](research/learned-dnf-circuit/CAMPAIGNS_4_AND_5.md)

## 4. Also in this release

- **Certification, port by port**: on 200 simulated ports, every port
  certified from its own margins has its predicted count.
  [circuit](research/circuit/README.md)
- **A supervisor** that keeps a leaking memory in service through a tripled
  leak: 0 failed services of 2 232, against 44 of 240 for the cell left to
  itself. [campaign](research/sky130-supervisor-campaign/REPORT.md)
- **Layout**: one cell drawn in SKY130 with open tools; 7 of 16 ports
  certified again with no wrong count; about 372 µW at rest and 15.5 nJ per
  write, nominal. [conclusion](research/sky130-layout/CONCLUSION.md)

## Limits

- **Simulation only**; no silicon.
- **Noise.** The claims under noise hold for the injected noise model of the
  simulations ([`noise.py`](research/circuit/noise.py)), with constants fixed
  in advance; in campaign 3 the measured noise was larger than those
  constants. A separate study with a noise model drawn
  from the transistors themselves is
  [committed](research/network-noise-study/COMMITMENT.md). In campaign 6 the
  claims per output under noise are not established.
- **Two objects.** The simulated networks are predicted through the network
  theorem, with its hypotheses checked on each run; the refinement from the
  analog cell model is proved for the native classes, not for the
  transistor networks. In campaign 6 the Lean proof is checked on the
  predicted observation of each instance; the measured runs do not satisfy
  its calibration premise as measured.
- **What is learned.** In campaigns 1 to 3, how many doses each port needs
  before it fires. In campaign 6, one Boolean function of four inputs, on
  three cells. The theory covers every monotone function, under its
  premises, and every Boolean function when something outside the network
  supplies each input with its complement; the network makes no complement
  itself. The experiment covers this one function, and no simulation has
  tested another function or a larger network.
- **Selected instances.** Every claim is about eligible instances, selected
  by per-cell measures before any network run.
- Two or three cells per simulated network, 27 °C, typical corner, ideal
  router and pulses. [Implementation assumptions](model/IMPLEMENTATION_ASSUMPTIONS.md)

## How to check it

Lean 4.35.0 and Mathlib v4.35.0, from the repository root:

```sh
cd proof/lean && lake exe cache get && lake build && lake build Audit
```

```sh
bash research/network-stability/check.sh
```

```sh
bash research/native-multitoken/check.sh
```

```sh
bash research/learned-coincidence/check.sh
```

Every audit allows only `propext`, `Classical.choice` and `Quot.sound` and
fails on admitted proofs. Each campaign folder holds its `PREDICTION.md`, its
frozen code, its evidence, its generated `REPORT.md` and the commands that
reproduce its predictions. Campaign 6's frozen code and evidence are on the
branches its report names.
[Validation ledger](docs/VALIDATION_LEDGER.md) · [reviewer's path](REVIEW.md)

## History

| Version | What it added |
|---|---|
| [v0.1.0](https://github.com/HevisNico/kernel-R/releases/tag/v0.1.0) – [v0.3.0](docs/RELEASE_V0_3_0.md) | composition of cells, chains, learning with realized thresholds |
| [v0.4.0](docs/RELEASE_V0_4_0.md) | training that stops by itself, networks of trained cells, searches |
| [v0.5.0](docs/RELEASE_V0_5_0.md) | a simulated circuit certified port by port; a verifiable supervisor |
| [v1.0.0](https://github.com/HevisNico/kernel-R/releases/tag/v1.0.0) | closed-loop networks proved for every N; their memory predicted before the run in three preregistered campaigns |
| [v1.1.0](https://github.com/HevisNico/kernel-R/releases/tag/v1.1.0) | networks that compute any monotone Boolean function, proved under checkable premises; a network of three cells that learns one such function, predicted before the run (campaign 6) |

All versions: [releases](docs/RELEASES.md). Folders: [`research/`](research/README.md),
[`proof/lean/`](proof/lean/README.md), [`model/`](model/README.md), [`docs/`](docs/RELEASES.md).

## Related work, origin and license

Learning that stops once a unit responds correctly goes back to Novikoff
(1962); stop-learning synapses exist in silicon; order-independent halting
is a theorem for abelian networks (Bond and Levine, 2016). The cell is not
an abelian processor in general (a recent pulse helps the next read), so
order-independence holds only under the separation and margin conditions.
No precedent was found for the refinement from an analog cell model to a
network model, or for a preregistered prediction of a network's exact
memory from per-cell measurements.
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
