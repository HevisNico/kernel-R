# A circuit network that learns (A and B) or (C and D), campaign 4: predictions

Pushed alone while the noise study validates its device model, before any implementation of campaign 4. Every
choice that waits for the noise study's validation report is fixed here **as a rule**; its outcome, and the numbers
it gives (`I`, the stage caps, the noise constants, the costs), are recorded by the frozen code in
[`BEFORE_M.md`](#the-record-before-stage-m), a file pushed alone before stage M, so before any run of campaign 4.

Written and pushed alone, before any implementation of campaign 4: no runner, no manifest, no analysis of this
campaign exists when this file is committed, and none of its seeds has been simulated. Nothing in it may be changed
afterwards; a wrong rule is corrected by an amendment file pushed before the run or the computation it concerns.

Everything here is a transistor-level simulation (ngspice 42, SKY130 models) of three R cells of
[`../circuit/cell.spice`](../circuit/cell.spice), with the junction areas of stage J, joined by an ideal router
outside the simulator. There is no layout, no wire between the cells and no silicon. The circuit does not verify
the proved read window, and nothing here says that it does.

## What is tested

The guarded theory (#168 to #171, and #177) says that an AND-OR cascade trained only by its own emitted pulses
learns exactly the monotone Boolean functions. This campaign asks whether three circuit cells with mismatch that no
one has looked at, trained by their own pulses, **learn `(A and B) or (C and D)` and answer every one of the 16
input patterns as computed beforehand from per-cell measures**.

The theorem this campaign stands against is `TwoLayerMonotoneRecognitionOneSided`, proved by
`two_layer_monotone_recognition_one_sided` in `research/learned-coincidence/MonotoneOneSidedRecognition.lean` of
#177, **cited by its commit `c45c0f716164c4bc7d2371f65676b8ab77f767a2`** (merged into `main` by #177). Its premise
`CascadeCalibrationOneSided` keeps the symmetric `CalibratedAdditiveRead` for every read of layer 1, for the teaching
reads of layer 2 and for the test reads of layer 2 that contain no selected line, and asks, for the test reads of
layer 2 predicted to fire (`FiringMaskRead`): the dated threshold decoder; the measured score of the test mask never
below the score of any submask that reaches the threshold; and each trained line's singleton score at least its
guarded line score minus the test budget (for a constant-true cell, the empty mask against its help). Every other
read keeps the symmetric `CalibratedAdditiveRead`. #176, a competing version, is closed.

**Campaign 4 is the preregistered campaign of point 3 of the noise study** (`../network-noise-study/COMMITMENT.md`,
commit `0cfe85a`, and its amendment 1, commit `7a37685`), run under the noise model of the rule of Noise model. It
carries two families of claims, **each with its own verdict, fixed here** (amendment 1, point 4):

- **the learned function**: a noise-free primary claim (the learned function and the 16 read-only outputs,
  predicted exactly, one run without noise per eligible instance, one discrepancy refutes it), and per-output claims
  under noise;
- **the per-port claims of the noise study**, N-own and N-word, under noise, on `R = 3` noisy runs per instance.

A failure of the learned-function claims does not change the verdicts of N-own and N-word; a failure of N-own or
N-word does not change the verdicts on the learned function, with or without noise.

## Decisions of the owner that this file applies

Recorded in [`research/learned-dnf-circuit/DECISIONS.md`](https://github.com/HevisNico/kernel-R/blob/49684afca5231c5497a77742d3eeb5b3d1ed64c3/research/learned-dnf-circuit/DECISIONS.md) (#172, commit `49684af`),
after the review of phase 0, with the one-sided premise of #177 and amendment 1 of the noise study:

1. Read-only tests by the testbench gate (`idis` off), every test read checked for writes in each run.
2. Layer-1 pulse amplitude **0.49**, fixed from the nominal cell; layer 2 at amplitude 1.
3. A calibration covering every stage up to the maximal write count, with the geometric gain path (it fits better
   than the linear one on the nominal cell, `GAINPATH.json`), and a calibration and validation split fixed here.
4. The saturated pair of the OR cell under the one-sided premise of #177.
5. Per-output claims under noise need room on their training reads as well as their test reads, under `K = 3`,
   with the noise constants **0.111 mV between runs, 0.094 mV within a run, 0.009 mV per dose**; under the validated
   model, each constant is the larger of this value and the one fixed by the noise study's validation (Noisy budget,
   below).
6. Size: **replaced by the owner's budget decision**
   ([`research/learned-dnf-circuit/BUDGET_DECISION.md`](https://github.com/HevisNico/kernel-R/blob/db4638bf4ad583d8b6e07eccb0936cc308068e94/research/learned-dnf-circuit/BUDGET_DECISION.md), commit `db4638b`),
   the choice that point 5 of amendment 1 of the noise study asks for above 4 h, and the owner's cost-model
   decision ([`research/learned-dnf-circuit/COST_MODEL_DECISION.md`](https://github.com/HevisNico/kernel-R/blob/2ffe04db391e9d0cd674c8e55419509e6b2fa0e1/research/learned-dnf-circuit/COST_MODEL_DECISION.md), commit `2ffe04d`): one run without
   noise and **`R = 3` noisy runs** per measured instance; **up to 8 h of expected compute**, measured with the
   measured cost model stated below; **the number of instances is the largest that fits**, set here. Two machines, `a` and `b`; the launch kit unchanged; every stage's manifest within
   the kit's aggregate cap of 14 400 s over both machines.
7. Controls: the untrained network, the skewed coincidence, the nominal predictor.

## What was run before this file

Phase 0 of #172 on the nominal cell only (model section `tt`, no mismatch, no seed): the gate, the calibration at
amplitudes 0.49, 0.5 and 1, guard on and guard off. The theory of #168 to #171 and #177. Campaigns 1 to 3 (seeds 7101
to 7103, 7201 to 7206, 7301 to 7306, 7401 to 7412). **Nothing was ever simulated with the seeds 7501 to 7520**, and the noise study's code refuses every seed but its
development instances 7101 to 7103 (its seed guard, `research/network-noise-study/phase0/pilot.py`, commit `ce9bb68`).

## Definitions

**Time unit.** 20 us, the length of a pulse.

**Instance.** One deck with three cells `a`, `b`, `c`: `net.deck` of `../network-circuit/net.py` with the model
section `tt_mm`, 27 C, the junction areas of stage J, and the simulator command `setseed` with the seed of the
instance. `I` instances, set by the rule of Execution and recorded in `BEFORE_M.md` (`I = 9` with the costs known
when this file is pushed),
seeds **7501 to 7500 + `I`**, the lower half (rounded up) on machine `a` and the rest on machine `b`, each
measured and run on its machine.

**Ports and lines.** Input A is port 1 of `a`, B port 2 of `a`, C port 1 of `b`, D port 2 of `b`, all at amplitude
0.49. Line `a` is port 1 of `c`, line `b` port 2 of `c`, at amplitude 1. A **mask** of a cell is the set of its ports
pulsed in one read.

**The gate.** Before a slot, the cell at rest, 3 units before it, the dose source of every port that may not write
in that slot is set to zero (`alter i.x<cell>.x<port>.idis dc = 0`), and restored to 8.2 nA for the ports that may.
A **gated read** is a read of a cell whose ports are all gated.

**FIRE**: the protection latch of the cell rises through 0.9 V within one unit and 2 us after the start of the read
(the **decision window**; for `c` in a routed slot, its deadline, below). **Write**: the write signal of the port rises through 0.9 V during the cycle of the pulse.
**Write'**: a write that stays above 0.9 V for at least 1 us (amendment 2 of campaign 3).

**Word** of a port of `a` or `b` in training, or of a line of `c` in teaching: one letter per read of that port, `s`
(no FIRE, exactly one write on that port), `F` (one FIRE, no write), any other read its own letter. **Output** of a
cell on a test pattern: whether it fires in the decision window of its test read.

**Score.** The score `Z` of a read is the peak, over the read, of the main charge `q` of the cell (0.1 at rest, 1 at
the FIRE level), as given by the matched guard-disabled probe of the calibration (the same deck with `vfire` at 0 V).
Guarded integer units: per cell, `Z` times 100 000, so the threshold is **`theta = 100 000`**.

### Measures, each cell alone in its slot

Per instance, two calibration decks with the same calendar, **guard on** (FIRE bits and latencies) and **guard off**
(scores), on the deck of the three cells. At each dose stage `k = 0, ..., 7`, under the gate, reads 22 units apart:
the empty read; port 1 alone; port 2 alone; both ports at one date; and on `c` also both lines with the second 0.3
unit late. Cells `a` and `b` at amplitude 0.49, `c` at amplitude 1. Then one clock-only dose on both ports of each
cell, writes enabled: the next stage. Two runs.

An instance is **measured** when both runs count, the guard-on FIRE bit of every read equals `Z >= 1` of the
guard-off read of the same stage and mask, and every stage has its reads; otherwise it is **not measured**, has no
prediction, gets no network run and enters no claim.

### Needs, the gain path and the budgets

**Need.** For `a` and `b`: the least stage whose pair read fires (guard on); for each line of `c`: the least stage
whose single read of that line fires. A cell or line with no firing stage up to 7 has no need.

**Write budget.** `Q = need + 2` per layer (the largest need of the layer, plus 2), and `Q <= 7` is required: every
stage the guarded memory can reach is then calibrated. Each layer is trained for `Q + 1` presentations.

**Calibration and validation split.** For each cell, the geometric gain path `Z(S, k) = h + sum over j in S of
g_j r_j^k` is fitted (least squares, `h` on a grid) on the singles and aligned pairs of the even stages 0, 2, 4, 6:
the **calibration**. The odd stages 1, 3, 5, 7 are the **validation**: their residuals are reported. For `c` only the
single lines are fitted: its pairs enter the one-sided premise, not the additive fit.

**Guarded tuple.** The theorem's memory adds one dose per write. Per cell, its guarded tuple uses the linear path of
the same reads over stages 0 to `Q`: `help`, `initialGain` per port and the layer's common `dose` in the integer
units above, rounded to the nearest unit; the threshold `theta`. The **residual bound** `epsilon` of a cell is the
largest `|Z - G|` over every calibrated single and aligned pair (layer 1) or single line (layer 2), stages 0 to `Q`,
where `G` is the score of the guarded tuple; it covers the geometric curvature and the differences between the two
ports of a cell. The geometric fit gives the validation and the predicted scores; the guarded tuple is the one the
Lean kernel checks.

**Noise-free budget**, per cell, in integer units: `beta_0 = epsilon + 0.030 mV x s`, where `s` is the sum over the
active ports of the read of the measured sensitivity (score per mV of stored voltage: the score step of one dose
divided by the measured dose in mV).

**Noisy budget, `K = 3`**: `beta_3 = epsilon + 3 x sigma`, with `sigma = s x sqrt(w^2 + b^2 + n x d^2)` mV, `n` the
writes of the port at that read; for a read of two ports, the two terms are added linearly. **Each constant is the
maximum of its value in decision 5 (`b = 0.111` mV between runs, `w = 0.094` mV within a run, `d = 0.009` mV per
dose) and its value fixed by the noise study's validation**, from the validation runs of the noise study only, never
from any campaign-4 data: the values of section 3 of the validation criteria
(`research/network-noise-study/VALIDATION_CRITERIA.md`, commit `5a24d10`), as the validation report gives them,
cited by its commit in `BEFORE_M.md`. If the device model is not validated: under the injected default, the
constants are those of decision 5; under a corrected model, each constant is the maximum of its value in decision 5
and the corrected model's own value, from the trains of section 3 of the validation criteria on the development
instances, stated in the corrected model's file.

**Room.** A read predicted silent has room under `beta` when `G + beta < theta`; a read predicted to fire has room
when `G - beta >= theta`. The test reads of `c` predicted to fire follow `FiringMaskRead`. Let `n_1`, `n_2` be the
predicted writes of lines `a` and `b`, and `Z_j` the guard-off score of line `j` alone at stage `n_j`. A test read of
line `j` alone has room when `Z_j - beta >= theta` (its anchor, `Z_j >= lineScore_j - beta`, then holds, since
`|Z_j - lineScore_j| <= epsilon`). The test read of both lines has room when each line alone has room and the
guard-off pair at stage `min(n_1, n_2)`, aligned and with the second line 0.3 unit late, is at least
`max(Z_1, Z_2) + beta`: the mask is then above every submask that reaches the threshold, with the lower stage of the
pair making the comparison conservative. The silent test read of `c` (the empty mask) keeps the symmetric read, at
stage `max(n_1, n_2)`: it must stay silent, so the higher stage is the conservative one.

**Declared assumption on `c`.** The calibration doses both ports of a cell at once, so its stage `k` is both lines at
`k` writes, while after teaching `c` is at `(n_1, n_2)`, often unequal. Each line alone is taken at its own stage
`n_j`, measured with the other line at the same stage `n_j`, not at its actual count: it is assumed that the stored
voltage of the other, inactive line does not change the score of a line alone by more than the residual bound. M8
reports this assumption against the runs.

**Relevant reads of an output.** Of `a` (`b`): its training reads (the pair at stages 0 to `need - 1`, silent; at
`need`, FIRE) and its test reads at the trained stage `need` (empty and each single silent; the pair FIRE). Of `c`:
its teaching reads (each line alone, stages 0 to `need_line - 1` silent, at `need_line` FIRE) and its test reads at
the trained stages (empty silent; each line alone and both lines FIRE).

An instance is **eligible** when it is measured, `Q <= 7` in each layer, and every relevant read of its three
outputs has room under the noise-free budget. An output has **room at K = 3** when every relevant read of it has
room under `beta_3`.

**Learning ports.** Six per instance: ports 1 and 2 of `a` and of `b` (trained jointly, as a pair) and the two lines
of `c` (each taught alone). **Own reads** of a learning port: for a port of `a` (`b`), the pair reads of its cell at
stages 0 to `need`; for a line of `c`, its single reads at stages 0 to `need_line`. A port has **own room** under a
budget when every own read has room. **Room up to** a learning port: for a port of `a` or `b`, own room; for line
`a` (`b`) of `c`, own room, own room of both ports of `a` (`b`), and room of the trained pair read of `a` (`b`) at
stage `need`, which sends the line its pulse in each teaching slot.

### The calendar

`calendar` of [`research/learned-dnf-circuit/dnf.py`](https://github.com/HevisNico/kernel-R/blob/49684afca5231c5497a77742d3eeb5b3d1ed64c3/research/learned-dnf-circuit/dnf.py) (#172, commit `49684af`), with the needs of the instance: one
slot every **22 units**; gates set 3 units before each slot.

1. **Layer 1**, `Q_1 + 1` rounds: A, B, C, D at one date; `a` and `b` write; nothing is routed.
2. **Layer 2**, `Q_2 + 1` rounds of two slots: AB in the first, CD in the second; `a` and `b` gated; `c` writes;
   routed.
3. **Tests**, 16 slots: each pattern of {A, B, C, D}, its inputs at one date; every cell gated; routed.
4. **Skew control**, 2 slots (in the run without noise only): AB with B 2 units late; CD with D 2 units late; every
   cell gated; routed.

**Routing.** A FIRE of `a` (`b`) rising within the decision window of a routed slot sends one pulse of amplitude 1
to port 1 (port 2) of `c`, **1.5 units after the FIRE** (`RoutedBatch`); an upstream silence sends nothing. The
read of `c` in a routed slot starts at its first arrival (`SlotTiming`): skew bound **1.1 units** (the spread of
layer-1 latencies seen on the bench, 0 to 1.06, plus two snaps of 0.02), deadline **2.2 units** after the first
arrival (the skew bound plus one unit and 2 us), slot duration 22 units. For `c` in a routed slot, the decision
window is its deadline: an output of `c` is a FIRE rising after its last arrival and before its deadline. By construction two pulses of a cell are at least 18.9 units apart and every slot is settled before the gates
of the next one are set.

**Noise-model extraction, per instance** (under the device model only). The model is extracted for each measured instance, on
its own deck and seed, in the four frozen states of the noise study's validation criteria (`hold`, `window`,
`fire`, `pulse`; `research/network-noise-study/VALIDATION_CRITERIA.md` (PR HevisNico/kernel-R#180, commit `5a24d10`), section 1), by **a frozen copy of the noise study's extraction code** (`devnoise.py
extract`) in this folder. The copy has its own seed guard: it refuses every seed but 7501 to
7500 + `I`, and refuses to run outside a launch of the kit; the nominal cell (no seed) is allowed for the rehearsal
only. The noise study's own guard on 7101 to 7103 is unchanged. Each extraction is checked by **the rule for
campaign 4 of the noise study's validation criteria** (`research/network-noise-study/VALIDATION_CRITERIA.md` (PR HevisNico/kernel-R#180, commit `5a24d10`), section 2): **V2** (the extraction completes; the
kept devices cover at least 99 % of each output's power; per kept device, p95/p5 of A and of B·f^ef at most 1.1; no
logic device above 1 % of an output; logic outputs at the rails within 10 mV; no DC failure; drain currents within
10⁻³ relative plus 1 pA; the conditioning of the stack nodes without effect), **V2b** (stationarity: a device kept
in more than one state has its A and B within 25 % between them), and **the isolation check** (the isolated
operating point of each cell within 1 µV of the full deck's on every node of the cell). An extraction passes when
every state and output of the instance passes all three; an extraction that does not complete fails. Every
extraction is done and checked before `PREDICTED.json` is pushed, and its pass or fail is recorded there. **A
measured instance whose extraction fails V2 or V2b, or whose isolated operating point fails the 1 µV check, gets no
noisy runs**: its noisy
runs are not in the manifests of N1, N2 and N3, are reported as **missing**, and enter no count of N-out, N-own,
N-word or G on noisy runs. Its noise-free claims stand: L1, L2, T and G on its run without noise.

**Where the extraction runs** (the owner's decision): through the launch kit, with the inventory and evidence of
every kit launch, since it simulates the campaign's own seeds, in **dedicated stages E1, E2, ...** after M and
before `PREDICTED.json`, one launch per machine per stage. The extraction of an instance is **split per cell, per
state and per output** (the owner's decision): one kit run per independent output of a cell in a state (7 per
cell, 21 per instance; `devnoise.py extract` restricted to that cell, state and output), on the machine of the
instance, merged by the frozen code into the instance's extraction in the order of a single-run extraction. This
is orchestration only: the method and its deterministic result are unchanged. The states are `hold`, `window`,
`fire` and `pulse`; `preset`, which serves V6 of the validation only and is not part of the model, is not extracted.
**The trip value is reused in the transfer step only if the noise study's identity check passes** (the result
identical to the last digit on its four development instances); otherwise it is not. Which applies is recorded in
`BEFORE_M.md`, with the commit of that check. **Identity check, in the rehearsal**: on the
nominal cell, the extraction split by cell, state and output and then merged must equal the single-run extraction
exactly (the same output file to the last digit written, that is the same SHA-256 after merging); if it does not,
nothing is launched. The E stages hold the per-output runs of the extractions of the measured instances, split by seed by a fixed rule: each machine's
measured instances in the order of their seeds, cut into the fewest consecutive parts such that every stage, the `j`-th
part of each machine together, is within the kit's 14 400 s. Their manifests are generated by the frozen code from
the collected measures of stage M (which instances are measured) and pushed before the first launch of E1. Its cost
per instance is part of the expected compute that sets `I` (Execution).

**Run positions**, by a fixed rule, recorded in `PREDICTED.json`: the slow 1/f part of the model places each
transient run of an instance at a virtual start of `k` x 1 000 s, `k` its position in the instance's list of runs
(`research/network-noise-study/VALIDATION_CRITERIA.md`, commit `5a24d10`, section 1, item 5). Per instance the list
is: calibration guard on (`k = 0`), calibration guard off (1), run without noise (2), N1 (3), N2 (4), N3 (5), and
the untrained control run last (6), on the control instance only. Extractions are not transients and are not in the
list.

**Noise seed.** The noisy run of round `n` (1, 2, 3: stage N1, N2, N3) of the instance of seed `S` has the noise
seed **`10 x S + n`**, written into `PREDICTED.json` by the frozen code: 75011 to 75013 for seed 7501, up to
`10 x (7500 + I) + 3`. The runs without noise and the measures have none. These numbers were never used to fix the
noise of any run: campaigns 2 and 3 and the noise study fixed no noise number (their noise was seeded by the
simulator's process number, chosen by the system and not recorded), and the numbers fixed elsewhere in this
repository lie in 1 to 707 (the diagnosis of a55, `research/sky130-supervisor-campaign`), in 201 to 9920 and 900000
to 900002 (`research/circuit/repetition`), and in 706002 to 706082 (`research/sky130-layout`, 700000 plus a cell
seed). A process number chosen by the system in an earlier run may have taken any value; such a draw was not fixed
and is not a use of the seed. **How the seed fixes the noise**: under the device model, the samples of every source are drawn outside the
simulator by the frozen generator (`noisegen.py`), the white and 1/f parts from `SeedSequence([noise_seed,
source_index])` and the slow part from `SeedSequence([instance_seed, source_index, 1])` at the run's virtual start
(run positions, above); the simulator draws no random number for the noise
(`research/network-noise-study/VALIDATION_CRITERIA.md`, section 1, items 5 and 6, commit `5a24d10`). Under the
default, the simulator's built-in noise of amendment 1, point 6, which is the injected model of
`research/circuit/noise.py` (ngspice 42 adds no device noise to a transient), its `trnoise` sources are seeded by
the simulator's process number and not by `setseed`, so the seed is the imposed process number (`noise_id` of
`net.Session`, the `fakepid` shim of `research/circuit/repetition`), set by the frozen runner on its simulator
process only, the launcher's own environment unchanged.

**Every noisy run is reproducible from its seed**: the same deck, instance seed and noise seed give the same run.
The rehearsal checks it on the nominal cell, before any launch: two noisy runs with the same noise seed give
byte-identical records (the field `wall_s` aside) and byte-identical waveforms (the date line of the raw file
aside); two noisy runs with two noise seeds give different noise; and all of them start from the same operating
point; under the device model, two generations of the samples file from one noise seed give the same SHA-256, which the analysis relies on
(Evidence, below). If one of these checks fails, no stage is launched.

**The untrained control run**: the 16 test slots only, on the preset state, every cell gated.

**Control instance.** Among the eligible instances, the one whose layer-1 pair at stage 0 has the highest score
(the closest to firing untrained), the lowest seed in case of a tie.

## Order of the campaign

1. **Measures.** Each machine runs the two calibration decks of each of its instances (stage M); then the
   noise-model extraction of each of its measured instances under the device model (stages E1, E2, ...; below).
2. **Predictions.** From the collected measures of both machines, the frozen scripts write `PREDICTED.json`: per
   instance, measured or not and why, the needs, the fits and residuals of both splits, the guarded tuples, the
   budgets, the room of every relevant read under both budgets, eligibility, room at `K = 3` per output, the
   zero-error words and outputs, the control instance and the network runs with their limits, the predicted
   observation of every measured instance (below), and, per learning port, own room and room up to it under
   `beta_3`, and, per measured instance, the pass or fail of its noise-model extraction under V2 (below). The frozen
   generator writes from it the Lean file of the **kernel gate** (below).
   **`PREDICTED.json` and the Lean file are committed and pushed before any network run**, and the launcher of the
   network runs is bound to the SHA-256 of `PREDICTED.json`. If the kernel gate fails, no network run is launched.
3. **Network runs**, on the machine of the instance, in the stages of Execution: **Q**, one run without noise per
   measured instance (with the skew control), in the order of the seeds, and the untrained control run on the
   control instance; then **N1, N2, N3**, one noisy run per measured instance each (without the skew control), in
   the order of the seeds, each noisy run with its own noise seed (below).
4. **One analysis**, after the last stage has ended on both machines.

## The kernel gate

A gate on the launch of the network runs, **not a claim**.

**The predicted observation** of a measured instance is the `Observations` of #177 built by the frozen code from
`PREDICTED.json`, in time units as rationals (latencies rounded to 0.0001 unit) and scores in the integer units of
the guarded tuple:

- **reads and dates**: one `ReadObservation` per slot of the calendar and per cell (`firstTrain`, `teach`,
  `secondTrain`, `firstTest`, `secondTest`); the start of a read of `a` or `b` is the date of its slot, the arrival
  of each active input that date; the arrival of a line on `c` is the predicted emission of its upstream cell plus
  the routing delay of 1.5 units (`delay = 3/2`), and the start of a read of `c` its first arrival;
- **emissions**: one emission per predicted FIRE, at the start of the read plus the latency of that cell, mask and
  stage measured in the guard-on calibration; none for a predicted silence;
- **scores**: the guard-off calibration score of that cell and mask at the stage of its predicted writes; on `c`,
  each line alone at its own stage `n_j` (the declared assumption above), the pair at stage `min(n_1, n_2)`, the
  lower of its aligned and 0.3-late scores (it must fire, so the lower stage is the conservative one), and the
  empty mask at stage `max(n_1, n_2)` (it must stay silent, so the higher stage is the conservative one); these also
  give the `scores` function of `FiringMaskRead` on every submask;
- **timing**: `firstTiming` skew 1/50 (two snaps), deadline 11/10, duration 22; `secondTiming` skew 11/10, deadline
  11/5, duration 22.

**What Lean checks.** For each measured instance and each of the two budgets (`beta_0`, `beta_3`, as the errors of
the guarded tuple), the Lean file decides, by Boolean checkers proved sound and complete against their definitions
(soundness: checker `= true` implies the property; completeness: the property implies checker `= true`),
`Cascade.Valid`
of the guarded tuple, `TrainingSeparation` and `CascadeCalibrationOneSided` on the predicted observation. The room
of `PREDICTED.json` is defined as the `admissible` of #177 on these numbers.

**One set of numbers.** `PREDICTED.json` holds the predicted observation, the guarded tuples and the budgets as
exact numbers only: dates as rationals in time units, rounded to 0.0001 unit, scores, residual bounds and budgets as
integers in the units of the guarded tuple. The Python computes room and eligibility on exactly these numbers, in
exact rational and integer arithmetic, never on floats; the Lean file is written from the same numbers. Lean and the
Python then cannot disagree by rounding.

**The gate holds** when every check
compiles and, on every measured instance, the conjunction under `beta_0` holds exactly when the Python says the
instance is eligible, and under `beta_3` exactly when the Python says all three outputs have room at `K = 3`. If Lean
fails, or disagrees with the Python room or eligibility on any instance, **no network run is launched**. Per-output
room at `K = 3` for a single output is checked by the Python only.

**What the gate gives.** When it holds, the predicted words and outputs of every eligible instance, which are those
of its predicted observation, follow from the measures by kernel check, with
`two_layer_monotone_recognition_one_sided` (#177, `c45c0f7`). This checks the derivation of the prediction from the
measures; it says nothing of what the circuit does, which the network runs test.

**The gate on "no" cases.** Fixed here, built from the nominal cell of phase 0 (`CALIBRATION.json` of #172,
commit `49684af`, need 4 on each pair and each line), with no campaign data: one unperturbed case and six
hand-perturbed ones (P1 to P6), each from the unperturbed one by a single change. P1 to P3 change a nominal measure, and the
frozen prediction code recomputes everything from it (fits, residual bounds, guarded tuple, room, predicted
observation); P4 to P6 change the predicted observation itself. The Python verdict of a case is eligibility under
`beta_0` together with its own check of the decoder, routing and separation conditions on the predicted
observation; the Lean verdict is the conjunction of the gate under `beta_0`. Under `beta_3`, the same, with the
eligibility replaced by room at `K = 3` for all three outputs.

| Case | Change | Expected verdict |
|---|---|---|
| P0 | none | yes |
| P1, silent read without room | the score of the pair read of `a` at stage 3 (its last silence) raised to `theta - 1`, so `G + beta_0 >= theta` though the read stays silent | no |
| P2, firing read without room | the score of the pair read of `a` at stage 4 (its first FIRE) lowered to `theta`, so `G - beta_0 < theta` though the read fires | no |
| P3, a submask of `c` above its mask | the score of the test pair read of `c` set to the score of line `a` alone minus 1, both above `theta` | no |
| P4, a FIRE before the last arrival | the emission of the test pair read of `c` moved to between its two arrivals | no |
| P5, a wrong route | the arrival of line `a` on `c` in one test read moved 1/10 unit from the emission of `a` plus 3/2 | no |
| P6, slots that overlap | the start of one test read moved earlier, so that it begins before the 22 units of the previous slot end | no |

In the rehearsal, on each of P0 to P6, the Python and Lean must give the expected verdict under `beta_0` and the same
verdict as each other; under `beta_3` they must give the same verdict as each other, with no fixed expected value.
Otherwise nothing is launched.

**The split of the work.** The Boolean checkers and their soundness and completeness theorems use no campaign
data: they are theory, built now by the theory track, with frozen targets and an audit, and cited here by commit
on the branch `proof/learned-dnf-premise-checkers`. Their frozen targets are generic soundness and completeness
statements over any `Observations`: soundness `CascadeValidCheckerSound`, `TrainingSeparationCheckerSound` and
`CascadeCalibrationOneSidedCheckerSound` in `research/learned-coincidence/MonotonePremiseTargets.lean`, commit
`423a24fde2d476752fec70eb44e9aca1fd550065`; completeness `CascadeValidCheckerComplete`,
`TrainingSeparationCheckerComplete` and `CascadeCalibrationOneSidedCheckerComplete` in
`research/learned-coincidence/MonotonePremiseCompletenessTargets.lean`, commit
`d1f8fa2b070ee80f2e19726e9e2644663fa51b9f`. **Both directions are proved** at commit
`2e586aa20857c61814aa94ee3b1a227ad113e998` (PR HevisNico/kernel-R#178, merged into `main`;
every workflow of the repository green on it): `cascade_valid_checker_sound`, `training_separation_checker_sound`
and `cascade_calibration_one_sided_checker_sound` in `MonotonePremiseSoundness.lean`, and
`cascade_valid_checker_complete`, `training_separation_checker_complete` and
`cascade_calibration_one_sided_checker_complete` in `MonotonePremiseCompleteness.lean`. So a `true` from Lean
proves the property and a `false` proves that it fails; the disagreement rule is kept unchanged.
The construction of the predicted observation is not one of the targets. That construction and the generator of
the Lean file from `PREDICTED.json` are campaign implementation, frozen after this file is pushed and rehearsed on
the nominal cell, where the gate is checked too, on P0 to P6.

## Predictions

**Primary claim, without noise.** For every eligible instance, in its run without noise:

- **L1, layer-1 stops.** The word of each port of `a` is `need_a` letters `s` then `Q_1 + 1 - need_a` letters `F`,
  and the same for `b`.
- **L2, layer-2 per-line counts.** The word of line `a` of `c` over its teaching slots is `need_c1` letters `s` then
  letters `F`, and the same for line `b`.
- **T, the outputs.** On each of the 16 test patterns, `a` fires exactly when A and B are both in it, `b` exactly
  when C and D are, `c` exactly when `(A and B) or (C and D)`.

Refuted by one letter of L1 or L2, or one output of T, that differs, on one eligible instance.

**Read-only, with its own verdict.** **G**: in every run without noise, across every gated read, no stored voltage
moves by more than 0.01 mV, and no write and no write' rises; in every noisy run, across every gated read, no write
and no write' rises (the stored voltage is not bounded there: the noise within a run is 0.094 mV). One gated read
that fails refutes G.

**Hypotheses, observed, reported, never refuting the primary claim.** **H**: two pulses of a cell never less than
16 units apart; no FIRE after the decision window in the cycle of a read; every arrival on `c` is a FIRE of `a` or
`b` plus 1.5 units, within the skew bound, and an upstream silence sends nothing; a FIRE of `c` comes after its last
arrival and before its deadline; every pulse delivered, nothing queued at the horizon.

**Learned function under noise, per output.** For every measured instance, every output that counts
and every one of its `R` noisy runs that counts: **N-out**, the output answers as predicted on every one of the 16
test patterns. An output of `a` (`b`) counts when it has room at `K = 3`; an output of `c` counts only when `c`,
`a` and `b` all have room at `K = 3`, since its test reads depend on `a` and `b` firing as predicted (as room up to
a line of `c` does). One test pattern answered otherwise in one noisy run refutes the claim of that output; each output
(`a`, `b`, `c`) has its own verdict, over its counted output-runs. A claim with no counted output-run is not
established.

**Per-port claims of the noise study, at `K = 3`**, over every measured instance and each of its `R` noisy runs
that counts, as in campaigns 2 and 3 with the learning ports above in place of the ports of the ring:

- **N-own**. A learning port with own room under `beta_3`, in a noisy run in which it receives at least `need`
  pulses in its training (teaching) slots, has a word of exactly `need` letters `s` followed only by letters `F`. A
  port-run in which the port receives fewer than `need` pulses does not count; their number is reported.
- **N-word**. A learning port with room up to it under `beta_3` reads exactly its zero-error word over its
  `Q + 1` training (teaching) slots.

Each is refuted by one port-run that fails it, and is not established without a port-run that counts. Words are
read with the write of this file; the word' (with write') of every port-run is reported in M6, never in place of
the word.

**The verdicts are separate**: the primary claim (L1, L2, T), G, N-out per output, N-own and N-word each have their
own, fixed by the rules above. None of them changes another.

**Controls.**

- **U, the untrained network.** In the untrained control run, no output fires on any of the 16 patterns. Stated in
  advance: on the nominal cell the pair at stage 0 is 0.12 of the FIRE level below threshold.
- **S, the skewed coincidence.** In the two skew slots, `a` and `b` stay silent. The predictor that ignores timing
  says FIRE. S can fail without touching the other claims.

**Declared comparisons, not claims**, as counts:

- **M1**, outputs that do not count for N-out: test patterns answered as predicted in their noisy runs; learning
  ports without own room, or with own room but not room up to them: port-runs with the zero-error word.
- **M2**, the run without noise of the measured instances that are not eligible: L1, L2 and T against their
  zero-error words and outputs.
- **M3**, latencies of every FIRE and the arrival skews on `c`, against the decision window and the skew bound.
- **M4**, the **nominal predictor** (need 4 for each pair and each line, the outputs of the truth table): the letters
  and outputs where it differs from the measured predictor, and where it differs from the runs.
- **M5**, the residuals of the validation stages, against `epsilon`.
- **M6**, every write-signal crossing that is not a write', with its date in the cycle and its width; per port-run
  of the noisy runs, whether its word and its word' differ.
- **M7**, per instance and per learning port, the spread over its `R` noisy runs of the stored voltage at the end
  of training, and of the FIRE latency of its first `F`, against the model's prediction.
- **M8**, the kernel checkers on the runs. After the one analysis, the checkers of the kernel gate run on the
  observations of the runs without noise of the eligible instances, under `beta_0`. Dates are those of the run's
  record: the start of each slot, each pulse's start as arrival, each FIRE crossing as emission. Scores: for the
  observed mask of a read, the peak of the main charge `q` over the read in the run, in the integer units of the
  guarded tuple, and for a read that fires the larger of that peak before the FIRE crossing and `theta` (the guard
  stops the charge at the FIRE, so the run has no unguarded score there); for every other submask in `scores`, the
  calibration score of the predicted observation. For a firing read the score `max(peak, theta)` decides the FIRE
  bit by construction, and the guard stops the charge near `theta`, so the residual and threshold parts of the check
  on firing reads are nearly empty; this is reported so, beside each result. M8 also reports the declared assumption
  on `c`: for each eligible instance with `n_1 != n_2`, the run's FIRE latency of each line alone at test against
  the guard-on calibration latency of that line at stage `n_j`, and the run's peak `q` of the empty test read of `c`
  against the calibration at stages `min(n_1, n_2)` and `max(n_1, n_2)`. The result of each check, per instance, is
  reported as it is and refutes nothing.

## Rules of the analysis

As in campaigns 1 to 3. One analysis, at the end, frozen with the implementation. **No word, output or score of any
network run is looked at before the last stage has ended on both machines**; between stages, only the launcher's
status of each run (complete or missing) is checked. The analysis first checks that `PREDICTED.json` is what the frozen
prediction script gives from the evidence of the measures; if not, every claim is "not established". **Then the
regeneration check of the samples file of every noisy run** (Evidence) runs, before any word, output or score of a noisy run is read;
the number of noisy runs it drops is reported. If every noisy run fails it, the claims under noise (N-out, N-own,
N-word, and G on the noisy runs) are "not established": that is a fault of the generator, not missing runs, and it
is reported so. A run counts
when the launcher recorded it complete and its own record says that it reached its last date; any other is a
missing run, never replaced. No re-scoping: the eligible instances, the needs, the budgets, the room and the control
instance are those of `PREDICTED.json`. Failures are reported as they are.

**Reporting.** This campaign is reported on its own, with its own verdicts. It is the first circuit campaign of
this claim; nothing is pooled with campaigns 1 to 3, which tested other claims.

## Noise model

A rule fixed now, applied before stage M, never from campaign-4 data. That this file may be pushed before the
validation's verdict is allowed by the noise study's amendment 2 (`research/network-noise-study/AMENDMENT_2.md`,
commit `b233b8b`, pushed alone), which moves point 6 of its amendment 1 from "before any preregistration of
campaign 4" to "before the first run of campaign 4 (stage M)".

- **If the noise study's validation report says the device model is validated** (validation attempt 2, under
  `research/network-noise-study/VALIDATION_CRITERIA.md`, commit `5a24d10`, its amendment 1, commit `4169e91`, and
  its amendment 2, `research/network-noise-study/VALIDATION_AMENDMENT_2.md`, commit `771e8b7`), campaign 4 runs under **the device model**: per instance, the extraction of section 1 of
  the criteria (stages E), one source per kept device and the shot terms, the samples of `noisegen.py`, as
  `filesource` sources with `xtrtol=7`.
- **If it is not validated**, the owner chooses, by a file pushed alone before stage M, between **the injected
  default** (the simulator's built-in noise of amendment 1, point 6: ngspice 42 adds no device noise to a transient,
  `research/network-noise-study/phase0/FEASIBILITY.md`, section 1, commit `0d8e21e`, so that default is the injected
  model of [`research/circuit/noise.py`](../circuit/noise.py), used in campaigns 1 to 3, `trnoise` sources at the
  input of each block, which overstates the low-frequency noise of the integrator amplifier) and **a corrected model
  with an independent justification**. Nothing is chosen from campaign-4 data.
- **Under the injected default**, there is no extraction and no E stage, and the rule of V2, V2b and the isolation
  check does not apply: every measured instance gets its noisy runs. The noise seed is applied as the imposed process
  number (Noise seed, above); `xtrtol` is not set (there is no XSPICE device); the deck of a noisy run is stored and
  there is no samples file.
- **Under a corrected model**, its file states how it is generated, seeded and costed, and which of the rules
  written here for the device model it follows; it is reviewed before stage M.

The claims under noise hold for the model applied, and only for it. The outcome is recorded in `BEFORE_M.md` and is
not changed afterwards.

## The record before stage M

`BEFORE_M.md`, written by the frozen code and pushed alone before the first launch of stage M, records:

1. **The noise model applied**: the verdict of the validation report, cited by its commit; if not validated, the
   owner's choice, cited by the commit of its file.
2. **The noise constants** `b`, `w`, `d` (Noisy budget, above), with their sources.
3. **The costs** of the cost model (Execution): a noisy run and an extraction run, as the validation report gives
   them (section 4 of the criteria), cited by its commit; under the injected default, the noisy run at the measured
   1 316 s of the injected model on the need-4 calendar (`research/network-noise-study/phase0/COST_C4_need4.json`,
   commit `4d3b5a1`) and no extraction; under a corrected model, the costs its file states.
4. **`I`, the expected compute, the stage caps** and the expected counts, computed by the frozen code from these
   costs by the rule of Execution.
5. **The reuse of the trip value**, with the commit of the noise study's identity check.

After the rehearsal, the fixed rule of Execution can only lower `I`, never raise it, by a file pushed alone before
the first launch of M.

## Execution

- **Executor.** A Claude Code cloud session on behalf of the owner, on two cloud containers whose inventories are
  recorded.
- **Launcher.** The second launch kit, unchanged, used once per stage, with one launch per machine: M (M1, M2) and
  E1, E2, ... with this file as their protocol, then Q, N1, N2 and N3 with `PREDICTED.json` as their protocol.
- **Environment, identical on both machines and checked by the launcher**: ngspice 42
  (`820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45`), PDK commit
  `1232782c1b9fab3aacda74d67ce7c92bf7da8105`, Python 3.12.3
  (`e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f`), numpy 2.3.5
  (`064003bdb6f9f7bb06e46e07cc3398cbfdc3c114dfe55b89d239e564917be2fb`). Four runs at a time on each machine.
- **Time limits.** Per run kind, 1.3 times its wall time measured in the rehearsal of the frozen implementation on
  the nominal cell (decks of three cells, four at a time), scaled to the stages, slots and pulses of each run, and
  never above 1.3 times the measured cost model below.
- **Both noise models.** The frozen implementation supports the device model and the injected default, so that
  the noise model of `BEFORE_M.md` needs no change of code. The rehearsal on the nominal cell runs every check of
  this file under each of the two: reproducibility from the noise seed, memory, the zero-amplitude check and the
  identity of the split extraction (device model only), and the kernel gate on P0 to P6. A corrected model, if the
  owner chooses one, is implemented, frozen and rehearsed in the same way before stage M.
- **Memory.** The rehearsal runs four noisy runs at a time on one machine, on the nominal cell with the longest
  calendar a measured instance can have (need 7 in both layers, `dnf.calendar(7, 7, 7, 7)`, about 20.5 ms
  simulated), and records the peak
  resident memory of the machine over them, generation of the samples files included. Expected from `research/network-noise-study/phase0/COST_C4_need4_sources.json`, commit `c2cb677`: 717 MB
  per run at 16.7 ms, four at a time, so about 3 GB for four, against the 15 GB of the present machine. If the peak exceeds 80 % of the memory of
  the machine recorded in its inventory, nothing is launched until an amendment, pushed alone before any launch,
  changes the runs at a time (for example 3 in place of 4), recomputes the stage caps with it, and lowers `I` by the
  fixed rule of Execution if a stage then exceeds 14 400 s.
- **Solver setting of the noisy runs under the device model.** The device model's sources are XSPICE `filesource` instances, and ngspice
  lowers `trtol` for the whole circuit when an XSPICE device is present unless `xtrtol` is set; every noisy run
  sets **`xtrtol=7`**. The noise study checked that, with the sources at zero amplitude and `xtrtol=7`, the run of
  the need-4 calendar reproduces the quiet run: the same occurrences, writes and FIRE events, the stored voltages of
  the reads within 87 nV (tolerance 1 uV), the FIRE dates within 0.1 us (`research/network-noise-study/phase0/ZEROCHECK_need4.json`, commit `47add4b`). **The rehearsal repeats this check
  on the nominal cell**, with the frozen generator at zero amplitude, against the run without noise of the same
  calendar, with the same tolerance; if it fails, nothing is launched.
- **Cost model**, the owner's cost-model decision (`COST_MODEL_DECISION.md`, commit `2ffe04d`): **wall times
  measured on the nominal cell**, decks of three cells, four runs at a time, each scaled to the calendar of a run by
  the ratio of `dnf.cost` for that calendar to `dnf.cost` for the measured calendar (only the structure of
  `dnf.cost` is used, not its absolute values):
  - a run without noise: **814 s** on the need-4 calendar (`research/network-noise-study/phase0/COST_C4_need4.json`,
    commit `4d3b5a1`); 845 s with the two skew slots;
  - a noisy run: **1 033 s** on the same calendar, the device model as 75 `filesource` sources
    (`research/network-noise-study/phase0/COST_C4_need4_sources.json`, commit `c2cb677`), when this file is pushed;
    the cost of `BEFORE_M.md` (above) replaces it;
  - a calibration deck: **125.1 s** measured for phase 0's one-cell deck, scaled to the three-cell deck of campaign
    4 by `dnf.cost` (accepted by the owner for sizing): **925 s** (`research/learned-dnf-circuit/cost-measures/COST_MEASURES.json`, commit `3144c57`);
  - the untrained control run: **369.2 s** (`research/learned-dnf-circuit/cost-measures/COST_MEASURES.json`, commit `3144c57`);
  - an extraction, per output run (the noise study's breakdown when this file is pushed, the trip value reused): per
    cell, two `window` outputs of 260 s, one `fire` of 290 s, two `hold` of 100 s and two `pulse` of 95 s, 1 200 s
    per cell, with the 1 µV isolation check (about 40 s per instance) once per cell, in that cell's first output run;
    the costs of `BEFORE_M.md` replace them.

  **Expected compute**, counted as in campaigns 2 and 3 and in phase 0: for each stage and each machine, the sum of
  the expected costs of its runs divided by the four runs at a time, plus three quarters of its largest expected
  cost; summed over every stage and both machines. A stage ends when its last run ends, so every stage on every
  machine has its tail. The instances are costed at the need-4 calendar of the nominal cell.
- **Budget, `R = 3`.** Up to 8 h of expected compute. `I` is the largest instance count whose expected compute, with
  `round(0.92 x I)` measured instances (campaign 3: 11 of 12) and one untrained control run, is at most 8 h.
  **With the costs known when this file is pushed: `I = 9`** (seeds 7501 to 7509, five on machine `a`, four on `b`), 8
  measured, **7.55 h** of expected compute (10 instances would need 8.20 h), in six stages; stage caps under the
  kit, with time limits 1.3 times these costs: M 7 881 s, E1 10 658 s, Q 4 558 s, N1, N2 and N3 5 412 s each.
  Expected: about **5 eligible instances** (0.6 per drawn instance, from campaigns 1 to 3); with the per-port rates
  of campaign 2 at `K = 3` (own room 6 of 16 ports, room up to 2 of 16), about 54 port-runs for N-own and 18 for
  N-word over the 24 noisy runs of the 8 measured instances. `BEFORE_M.md` recomputes every figure here, the N-out
  output-runs included, from its costs.
- **Stages and manifests**, accepted by the owner. The kit bounds each manifest by the sum over both machines of
  `sum(caps) / 4 + max(caps)`, with each cap a run's time limit plus 10 s, at 14 400 s. The stages run one after the other,
  each with one launch per machine and its own manifest within 14 400 s: **M** the calibration decks (in two halves
  by seed, M1 and M2, if they do not fit one); **E1, E2, ...** the extractions, per cell (above); **Q** the runs
  without noise with the skew control, and the untrained control
  run; **N1, N2, N3**, the first, second and third noisy run of every measured instance.
- **Lowering `I` after the rehearsal, a fixed rule.** The rehearsal measures the cost of one extraction on the
  nominal cell. If, with the time limits of the rehearsal, a stage exceeds 14 400 s, or if, with the extraction cost
  the rehearsal measured in place of the stated one, the expected compute exceeds 8 h, `I` is lowered by dropping
  the instances of the highest seeds, one at a time, until every stage fits and the expected compute is at most
  8 h. The new `I`, the dropped seeds, the measured extraction cost, the expected compute and the stage caps are
  recorded in a file pushed alone before the first launch of M. Dropped instances are never simulated, enter no
  count and are not missing runs. **The rehearsal never raises `I`.** No other change follows from the rehearsal.
- **The fixed sequence of stages.** Every manifest after M (Q, N1, N2, N3) is generated by the frozen code from
  `PREDICTED.json` alone, bound to its SHA-256, and **all of them are pushed before the first launch of Q**. The
  stages then run in the fixed order M (M1, M2), E1, E2, ..., Q, N1, N2, N3, **whatever the results**: no early stop, no added
  stage, no change of any manifest, limit, run or order between stages. A stage that is not launched, or whose
  launch on a machine reaches its cap, is **missing** on that machine, never **failed**: its runs are missing runs,
  enter no count, and are reported as missing.
- **Evidence.** As in campaigns 2 and 3, with one change for the noisy runs under the device model. With the sources as `filesource`
  instances the deck of a noisy run is about 0.1 MB and is **stored as for the runs without noise**; the noise
  samples are in a separate samples file, about 50 MB per run (`research/network-noise-study/phase0/COST_C4_need4_sources.json`, commit `c2cb677`). **The samples file is not stored**: the
  evidence holds the frozen generator (by its path and the SHA-256 of the frozen file), the noise seed, the
  parameters it was generated from (the noise model and its constants, the instance seed, the run position `k`, the calendar of the run)
  and the SHA-256 of the samples file. **The analysis regenerates every samples file** with the frozen generator and
  checks that it gives that SHA-256; a noisy run whose regenerated samples file gives another SHA-256 does not count,
  and is reported as missing. Each samples file is deleted as soon as its run ends and its SHA-256 is recorded; the
  evidence no longer needs it. The decks of every run and measure are stored. Otherwise: logs, records, fingerprints and SHA-256 lists here; waveforms to
  `HevisNico/kernel-R-circuit` during the campaign and after the one analysis to an evidence branch of this
  repository with no shared history, a waveform above 100 MiB as parts of 90 000 000 bytes with the SHA-256 of every
  part and of the whole file.

## What this campaign cannot show

Nothing about silicon, a layout, wires between cells or a real router. Nothing about the noise of a fabricated cell.
Nothing about a monotone function other than `(A and B) or (C and D)`, or about more than three cells and four
inputs. Nothing about the native cascade of `research/recursive-learning`. Nothing about outputs or ports without room.
Nothing outside 27 C and the typical corner with mismatch. The per-cell measures are made on the deck of the network
by the same simulator; the claim is that the network does what its cells, measured alone, say it will.
