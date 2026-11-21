# Design note: a layered kernel-gate generator, for A∧B∧C, A∨B∨C and majority of three

Phase 1, design only. No code is written, nothing is committed and nothing is pushed.

**Sources.** `main` at `d50cdec`, fetched by name. LC/ means `research/learned-coincidence/`. Every `Layered*.lean`
file is byte-identical between `bf9392e` and `d50cdec` (`git diff --quiet`), so the line numbers below hold on both.
`#184` (two rails) touched only `TwoRails*`, `Audit.lean`, `check.sh` and the README. For the two-layer generator I
cite its own branch `research/learned-dnf-generator` at `4fca6256` (GEN/).

**Tags.** [K] is known, from reading or running. [I] is inferred. [G] is guessed. "Search" means the exhaustive
enumeration script of section 2.1, which I ran locally. It is not a Lean proof.

## 0. Summary

- **Minimal networks.** [K, search] Among layered networks of depth at most 3 and layer widths up to (3, 2, 1):
  - A∧B∧C needs 3 cells, in 2 layers.
  - A∨B∨C needs 3 cells, in 2 layers.
  - Majority needs 6 cells, in 3 layers (3 + 2 + 1).
  - [I] No deeper network is smaller (argument in 2.1).
  - [K, search] Every minimal majority network drives some external input into at least two cell ports.
- **Untrained cells.** None of the recommended networks has an untrained cell. Only `on` and `off` are untrained,
  and none is needed. `copy` is a trained gate: one group, a single-port lesson (LayeredMonotoneTarget.lean:31–40).
- **A gate with precedent.** [K, search] `both(X, X)`, a `both` cell with both ports wired to the same source,
  computes the same function as `copy(X)`. It trains as a simultaneous pair read, like campaign 6's cells a and b.
  Each `copy` below therefore has a variant built only from kinds that campaign 6 has already run (gate kinds, not
  positions: see 5).
- **The calendar.** [K]
  - The layered separation premise orders every training read in one strict sequence: by layer, then cell, then
    group, then round (LayeredMonotoneTarget.lean:224–241).
  - Two cells can never be trained in one slot. Campaign 6 trained a and b in one slot, and the two-layer premise
    allowed that (MonotoneTarget.lean:147–148).
  - [K] Both recognition proofs ignore the separation premise. It is bound as `_separation`
    (LayeredMonotoneRecognition.lean:247, MonotoneOneSidedRecognition.lean:40), and the docstring says "the proof
    derives its conclusion from validity and the two calibration premises alone" (LayeredMonotoneRecognition.lean:243–245).
  - So the order is a protocol premise that the gate checks. It is not used in the proofs.
- **Cost.** At R = 7 rounds per group, one network run needs:

  | Network | Slots per run |
  |---|---|
  | A∧B∧C | 29 |
  | A∨B∨C | 43 |
  | Majority | 64 |
  | Campaign 6 (measured) | 35 to 39 |

## 1. The Lean input of the layered theory

All [K], from LC/LayeredMonotoneTarget.lean (T) and LC/LayeredMonotoneCheckerTargets.lean (C).

### Gates (T:13–48)

| Gate | Value (T:17–22) | Ports used (T:26–29) | Groups (T:31–34) | Group masks (T:36–40) | Anchors (T:43–48) |
|---|---|---|---|---|---|
| off | false | none | 0 | (none) | none |
| on | true | none | 0 | (none) | the empty mask |
| copy | port 0 | port 0 only | 1 | {0} | {0} |
| both | port 0 and port 1 | both | 1 | {0, 1} | {0, 1} |
| either | port 0 or port 1 | both | 2 | {0}, then {1} | {0} and {1} |

### Cell (T:50–59)

- **Fields.** `gate`, `initialGain : Fin 2 → Nat`, `help`, `threshold`, `trainError`, `testError`, `dose`, `maxWrites`
  and `rail`, all per cell. So the dose is per cell, unlike the two-layer `Parameters`.
- **Score.** `score w x = help + gain(0) [if port 0] + gain(1) [if port 1]` (T:64–68).
- **Stop.** `stop g` is the first k ≤ maxWrites at which the group score reaches the threshold (T:76–78).
- **Expected writes.** They add up the groups (T:80–82). An `either` cell writes port 0 in group 0 and port 1 in
  group 1. Group 1's writes count group 0's settled writes first (`writesBefore`, T:100–101).
- **`Cell.Valid` (T:84–92).** Its checker is `Checker.cellValid` (C:20–30). The conditions:
  - a positive dose, for every cell, `on` and `off` included;
  - for each active group: 0 < stop ≤ maxWrites, robust silence below the stop and robust firing at it, with
    `trainError`;
  - every trained gain below the rail;
  - every mask x with `gate.eval x = false` silent, with `testError`;
  - every anchor firing, with `testError`.

### Node (T:116–129)

- **Fields.** `cell`, `source : Fin 2 → Option (Fin N)` (a cell of the layer just below), `delay : Fin 2 → Rat` and
  `stimulus : Fin 2 → Pattern M`, one external pattern per group.
- **`Node.Valid` (T:125–129).** Its checker is `Checker.nodeValid` (C:32–36). The conditions:
  - the cell is valid;
  - `source a` is present exactly when the gate uses port a;
  - every delay is ≥ 0;
  - for each active group, the predicted outputs of the sources on `stimulus g` equal the group mask **exactly**.

### Cascade (T:132–146)

- `inductive Cascade M : L → N → Type`, with constructors `input : Cascade M 0 M` and `layer lower timing nodes`
  (T:132–134).
- There is **one `SlotTiming` per layer**, and `nodes : Fin B → Node M N` read only from the layer just below. No
  wire skips a layer [K: `source : Fin 2 → Option (Fin N)`, N being the lower width]. A copy is the only way to carry
  a signal across a layer (T:24–25, docstring).
- `Cascade.predict` is at T:136–139. `Cascade.Valid` (T:141–146) is the lower layer valid, the timing valid, and
  every node valid.

### Traces (T:148–157)

- **`ReadTrace`** (T:148–151):
  - `input` gives the external arrivals, `Fin M → Option Rat`;
  - `layer` gives `ReadTrace lower × (Fin N → ReadObservation 2) × (Fin N → Pattern 2 → Int)`, that is, one dated
    two-port read per cell of the layer and one table of 4 reference scores per cell.
- **`TrainingTrace`** (T:153–157):
  - `input` is `Unit`;
  - `layer` gives `TrainingTrace lower × (Fin N → Fin 2 → Nat → ReadTrace lower) × (Fin N → CellTrain)`.
  - For each cell, group and round there is one full replay of every lower layer, plus the addressed read
    (`CellTrain := Fin 2 → Nat → ReadObservation 2`, T:62).
- **Example.** LC/LayeredMonotoneExample.lean:103–133 writes these with anonymous constructors, as
  `⟨lower, reads, scores⟩`.

### Premises and checkers

- **`TrainingSeparation`** (T:238–241) is checked by `checkLayeredSeparation` (C:90–93), built on
  `Checker.orderedBatches` (C:41–43) and `externalSeparation` (C:45–47). Section 3 covers it.
- **`TrainingCalibration`** (T:200–211) is checked by `checkLayeredTrainingCalibration` (C:95–107). For each cell,
  active group and round r ≤ maxWrites:
  - the replay passes the **test** rules of the lower layers (`oneRead`, C:70–80);
  - the addressed read is routed (`Checker.routed`, C:49–51);
  - the addressed read is additive and two-sided, at `writesBefore`, with `trainError` (`additiveSlot`, C:53–57).
- **`ReadCalibration`** (T:186–198), over the whole external cube, is checked by `checkLayeredReadCalibration`
  (C:109–111). For each cell of each layer:
  - the read is routed;
  - if `gate.eval` of the observed mask is true, `firingSlot` applies (C:59–68): the decoder, measured = scoreAt,
    the firing submasks below the measured score, and the anchor lower bounds;
  - otherwise `additiveSlot` applies, with `testError`.

### The theorem and its lemmas

- **The theorem.** `layered_monotone_recognition_one_sided` (LC/LayeredMonotoneRecognition.lean:246) is of type
  `LayeredMonotoneRecognitionOneSided` (T:249–256). It concludes `c.Trained train ∧ ∀ x, observed c (test x) = c.predict x`.
- **Soundness lemmas** used by a derivation: `layered_valid_checker_sound`, `layered_separation_checker_sound`,
  `layered_training_calibration_checker_sound` and `layered_read_calibration_checker_sound`
  (LC/LayeredMonotoneCheckerProofs.lean:129–150, with the `_complete` lemmas there too).
- **Usage.** The arities appear at LC/LayeredMonotoneCheckerExamples.lean:71–77.
- **Characterization.** `layered_monotone_characterization` (LayeredMonotoneCharacterization.lean:367) says that the
  class computes exactly the monotone functions. `canonical g` (LayeredMonotoneCharacterization.lean:42–51) is a
  valid cell for every gate (`canonical_valid`, :53).
- **Imports.** A gate file needs `LayeredMonotoneCheckerProofs` and `LayeredMonotoneRecognition`. Their chain is
  `LayeredMonotoneTarget` → `MonotoneOneSidedTarget` → … plus `MonotonePremiseTargets`, `MonotonePremiseSoundness`
  and `MonotonePremiseCompleteness` [K, the imports of each file].

## 2. The smallest networks

### 2.1 Method

- [K] A local script enumerates layered networks over M = 3 inputs, with the gate semantics, sources and port rules
  of section 1:
  - depth 1;
  - depth 2 with layer-1 width 1 to 3 and an output layer of 1;
  - depth 3 with widths up to (3, 2, 1).
- It keeps a node only if each active group has at least one external stimulus giving exactly its group mask
  (`Node.Valid`'s last clause).
- It does not check the cell parameters. `canonical_valid` gives a valid cell for every gate, and the campaign fit
  will give its own.
- **Minimal size**, within that range: 3 cells for A∧B∧C and A∨B∨C (48 minimal wirings each), and 6 for majority
  (1344).
- [I] **No smaller network exists at greater depth.** A layer of width 1 below the top makes everything above it a
  function of one cell. The output is then that cell or a constant, which is a depth-2 network the search already
  covers. With 5 or fewer cells and depth 4 or more, some lower layer has width 1.
- [I] **Majority needs at least 3 layer-1 cells.** With 2 layer-1 cells f₁ and f₂, every cell above computes a
  monotone function of (f₁, f₂). That is 0, 1, f₁, f₂, f₁∧f₂ or f₁∨f₂, and with two-input f's none of these is
  majority. The search confirms this within its range [K].

### 2.2 The networks

- [K, search] Each network computes its function, and each trained group has a valid stimulus. The stimuli are listed
  as one valid choice per group; the search gives all of them.
- "Inputs driving 2 ports" counts cell ports, so `both(C, C)` counts C twice.

| Function | Network (layers; L1.i is the i-th cell of layer 1) | Cells | Trained groups | Inputs driving 2 ports | Stimuli, one per group in node order |
|---|---|---|---|---|---|
| A∧B∧C, a | L1: both(A,B), copy(C). L2: both(L1.0, L1.1) | 3 | 3 | none | AB; C; ABC |
| A∧B∧C, b | L1: both(A,B), both(C,C). L2: both | 3 | 3 | C | AB; C; ABC |
| A∧B∧C, c | L1: both(A,B), both(B,C). L2: both | 3 | 3 | B | AB; BC; ABC |
| A∨B∨C, a | L1: either(A,B), copy(C). L2: either | 3 | 5 | none | A / B; C; A / C |
| A∨B∨C, b | L1: either(A,B), both(C,C). L2: either | 3 | 5 | C | A / B; C; A / C |
| A∨B∨C, c | L1: either(A,B), either(B,C). L2: either | 3 | 6 | B | A / B; B / C; A / C |
| Majority, a | L1: both(A,B), both(A,C), both(B,C). L2: either(L1.0, L1.1), copy(L1.2). L3: either | 6 | 8 | A, B, C | AB; AC; BC; AB / AC; BC; AB / BC |
| Majority, b | the same, with L2.1 = both(L1.2, L1.2) | 6 | 8 | A, B, C, plus L1.2's output on 2 ports | as a |
| Majority, c | L1: both(A,B), either(A,B), copy(C). L2: copy(L1.0), both(L1.1, L1.2). L3: either | 6 | 8 | A, B | AB; A / B; C; AB; AC; AB / AC |

What each cell learns, in majority a:

- the three layer-1 cells learn a pair: AB, AC and BC, each a pair read like campaign 6's cells a and b;
- L2.0 learns "AB or AC" as two single lines, like campaign 6's cell c;
- L2.1 learns to pass on BC, as a single-port lesson;
- L3 learns "L2.0 or L2.1" as two single lines, like c.

**Checked against Cascade.Valid as stated** [K for the stimulus clause, by search; I for the rest]:

- **Port presence.** `source a` is present exactly when the gate uses port a. For `copy`, port 1 must have no source.
- **Delays.** Each is ≥ 0. The campaigns used 3/2.
- **Timing.** The `SlotTiming` of every layer must be valid.
- **Cells.** Each `Cell.Valid` holds for parameters of the `canonical` kind [K, `canonical_valid`]. For measured cells
  it is what the gate decides.
- **The copy cell.**
  - `Cell.Valid` asks that the mask {1} be silent with `testError` (T:91), even though port 1 never receives a pulse
    (`Routed` with no source gives no arrival, T:166–168) [K].
  - So port 1's `initialGain` is a parameter of the spec with no reading behind it. Setting it to 0 satisfies the
    clause [I].
- **Majority b.** `both(L1.2, L1.2)` needs one routed pulse to drive both ports of L2.1. Both arrivals then have the
  same date, a pair read with no skew [I].

**Recommendation.**

- **A∧B∧C: a or b.** No shared input with (a), and no copy with (b).
- **A∨B∨C: a or b.** These have 5 groups, against 6 for (c).
- **Majority: a.** Its cell kinds match campaign 6's (see 5 for positions), it has no internal fan-out, and it uses
  one copy. Use b if a `copy` cell is unwanted on the bench, at the cost of one internal fan-out.

The choice between copy and both(X, X) is a circuit question (section 5). The generator supports both.

## 3. The calendar

**What the theory imposes** [K, LayeredMonotoneTarget.lean:213–241]:

- **Batches.** `trainingBatches` makes one batch per (layer, cell, active group, round r ≤ maxWrites), in that order:
  - lower layers first (`trainingBatches lower ++ …`);
  - then cells in index order, groups in order, and rounds in order.
- **Batch contents.** A batch holds the windows of the lesson's full lower-layer replay: every lower cell's window
  `[start, start + duration]` of its layer, plus the external arrivals as points `(t, t)`, plus the addressed read's
  window.
- **The premise.** `(trainingBatches c train).Pairwise BatchBefore`: every window of an earlier batch ends at or before
  the start of every window of a later batch (T:234–241).
- **Tests.** Every training batch must end before every test window. There is **no** condition between two test
  replays (T:237–241: "Replays of separate test patterns are independent").
- **Consequences:**
  - **No two addressed reads may overlap.** One slot cannot hold the training of two cells, nor two groups or two
    rounds of one cell.
  - **Within one batch nothing is ordered.** The lower replay and the addressed read share the lesson's slot,
    governed only by routing, as campaign 6's `teach` rows were.
- **Against the bench.**
  - The two-layer premise allowed several first-layer cells in one round slot. Its first clause compares round r with
    round r + 1, for all a and b (MonotoneTarget.lean:147–148). Campaign 6 used this for a and b
    (`dnf.calendar`: "layer 1, both cells in one slot").
  - Under the layered premise, that schedule fails `orderedBatches` [K]. Its round-r batches of a and b would overlap.

**What it costs.** For a network, the training batches number Σ over trained cells of (groups × R_cell), with
R_cell = maxWrites + 1. Then come 2^M = 8 tests. At R = 7 for every cell (campaign 6's write limits were 5 to 7, so
R from 6 to 8 [K, C6 PREDICTED files]), in slots of 22 units:

| Network | Training batches | Tests | Slots per run |
|---|---|---|---|
| A∧B∧C (a or b) | 3R = 21 | 8 | 29 |
| A∨B∨C (a or b) | 5R = 35 | 8 | 43 |
| Majority (a, b or c) | 8R = 56 | 8 | 64 |
| Campaign 6, measured | (Q1+1) + 2(Q2+1) = 19 to 23 | 16 | 35 to 39 |
| Campaign 6's shape under the layered calendar | 2(Q1+1) + 2(Q2+1) ≈ 26 to 30 | 16 | 42 to 46 |

- [I] **Slot length.** A lesson at layer d spans about (d − 1)(latency + delay) plus the read duration of layer d. In
  campaign 6's units (latencies ≤ 1.1, delay 3/2, durations 22 and 19), a layer-2 lesson fits a slot of 22 units, as
  c's lessons did.
- [G] **Layer-3 lessons** (majority only) start their read about 4 to 5 units after the slot. With a layer duration of
  19, they need a slot of about 24. Over 16 layer-3 batches that adds about 32 units, under 3 % of the run.
- [G] **Simulated cost of a run.** Roughly slots × cells. Against campaign 6 (37 slots × 3 cells): A∧B∧C ≈ 0.8×,
  A∨B∨C ≈ 1.2×, majority ≈ 3.5×. The circuit side must measure this.

**Options for the calendar.**

1. **Keep the premise.** Train cells one after another, at the costs above. This needs no Lean change and is my
   recommendation for step 2.
2. **Widen the premise to let independent cells share a slot.** This is a new frozen target with a new checker and new
   soundness and completeness proofs. The recognition proof itself would not change, since it ignores the premise [K].
   The checker's proofs would be new work [G: moderate]. It saves about R slots per extra cell in a layer: about 14 of
   56 batches for majority's layer 1. A physical claim would rest on it: that two cells trained in one slot do not
   disturb each other. Campaign 6 relied on that claim for a and b.

## 4. The writer

**Spec.** One JSON per instance. The first part describes the network:

```
{ "tag", "M": 3, "inputs": ["A","B","C"],
  "layers": [ { "timing": {"skew","deadline","duration"},
                "nodes": [ { "name", "gate": "both|either|copy|on|off",
                             "initialGain": [g0, g1], "help", "threshold", "trainError", "testError",
                             "dose", "maxWrites", "rail",
                             "source": [i|null, i|null], "delay": ["r","r"],
                             "stimulus": [[input indices]|null, ...] } ] } ],
```

The second part holds the observations. A ReadTrace is serialized as
`{"arrivals": [M], "layers": [[{"read": read, "scores": [4 ints]}] per cell] per layer}`.

```
  "training": [ [ [ [ {"replay": ReadTrace below, "read": read} per round ] per active group ] per node ] per layer ],
  "tests": [ ReadTrace of the whole network ] * 2^M (maskIndex order),
  "budgets": { "K0": {"trainError": [[..] per layer], "testError": [[..] per layer]}, ... },
  "verdicts": optional, "lean": {...} }
```

- Values are exact rationals and integers, as in GEN/spec.py.
- **Missing rows are refused.** Every active group needs maxWrites + 1 rounds, each replay needs every lower cell,
  and there are 2^M tests.
- **Inactive groups and rounds beyond maxWrites** are not read by any checker. The writer fills them with a fixed
  empty value, as the `TrainingTrace` function types require [K, T:153–157], and refuses any value given for them.
- **Budgets.** They live in each `Cell`, so a named budget yields its own `Cascade`.

**Lean output.** Under `LearnedCoincidence.Layered.Generated`:

- Nodes as `⟨⟨.both, gains, …⟩, source, delay, stimulus⟩`.
- The cascade as `.layer (.layer .input t₁ n₁) t₂ n₂`. Per-node fields use `Vector` tables or constants, as in GEN/emit.py.
- The traces as anonymous constructors over list tables, like LayeredMonotoneExample.lean:103–133. Each layer gets an
  empty default `ReadTrace`.
- `test : Pattern M → ReadTrace circuit` through `maskIndex`.
- Per budget, these theorems, each `= true|false := by decide +kernel`:
  - `valid_*` (`checkLayeredValid`);
  - `separation_*` (`checkLayeredSeparation`);
  - `training_*` (`checkLayeredTrainingCalibration`);
  - `reads_*` (`checkLayeredReadCalibration`);
  - and the conjunction `checks_*`.
- When `checks_*` is true, the generator also writes:
  - `outputs_*`: the conclusion of `layered_monotone_recognition_one_sided M L N` through the four soundness lemmas;
  - `function_*`: `(patterns M).all fun x => circuit.predict x 0 == f x`, with f stated independently.
- The convention of the two-layer generator is kept: the file compiles only if Lean agrees with every asserted value.

**Mirror.** A Python transliteration, in exact `Fraction`, of:

- `Cell.stop` and `expectedWrites`, `groupObserved`, `writesBefore`, `settledWrites`;
- `Cascade.predict`;
- `cellValid` and `nodeValid`;
- `trainingBatches`, `readWindows`, `orderedBatches` and `externalSeparation`;
- `oneRead`, `routed`, `additiveSlot` and `firingSlot`.

Like GEN/mirror.py, it records each condition with its kind and place. The decoder (`checkThresholdRead`) is the
two-layer one, so GEN/mirror.py's `threshold_read` is reused.

**Compile list.** gencheck.sh compiles only the 13 two-layer modules. The layered gate needs those plus
`LayeredMonotoneTarget`, `LayeredMonotoneRecognition`, `LayeredMonotoneCheckerTargets` and
`LayeredMonotoneCheckerProofs`.

- LC/check.sh compiles them, in an order that now includes `TwoRailsTarget` and `TwoRails` (#184).
- C5/check.sh does not [K, its module list]. The frozen campaign harness therefore **cannot** check a layered file.
  A layered campaign needs a new check script; C5/check.sh stays as it is.
- I propose `gencheck_layered.sh`: the same steps 1 and 3, with the 17 modules [I: 13 + 4; checked by compiling].

**Tests.** The same scheme as the two-layer phase.

- **(a) Reference reproduction.** There is no committed layered gate file to match byte for byte. The reference is
  the repository's own example (LayeredMonotoneExample.lean, `circuit`, `train`, `test`):
  - written as a spec, emitted and compiled, all four checkers must be true;
  - the five rejection fixtures of LayeredMonotoneCheckerExamples.lean:55–68 must each come out false, in the mirror
    and in Lean: replay 0 as test, silentOutsideBudget, firingAnchorBelowBound, submaskAboveObserved,
    lowerReplayOutsideBudget;
  - the mirror must agree with the four accepted theorems (:47–53).
- **(b) Synthetic cases.** The nine networks of 2.2, with additive-model traces at the four residual rules. Units as
  in the campaigns (THETA = 100 000, C5 timings). Each trained group's need is about 3. The calendar is strictly
  sequential. Each spec asserts the per-checker theorems and `outputs_*` and `function_*`, against
  `x 0 && x 1 && x 2`, `x 0 || x 1 || x 2` and `decide (2 ≤ card x)`.
- **(c) Mutations.** Each is meant to break one kind:
  - cell margin: early silence, stop, silent mask, anchor, rail;
  - node wiring: a source present on copy's port 1, a negative delay, a stimulus giving the wrong mask;
  - batch order: two cells' rounds placed in one slot, campaign 6's schedule, expected to fail `orderedBatches`;
  - external separation: a test inside training;
  - route; the residual of an addressed read; the residual of a read inside a replay;
  - submask; anchor; scoreAt = value; FIRE bit; emission window; one emission; v ≤ t; skew; timing invalid.

  Each case asserts `= false` and the per-checker values. The mirror must fail only the intended kind.
- **Controls.** Flip copies, diffed and error-located as in GEN/tests/flip_check.py. A missing row must be refused.
  Hashes of every generated file, with a regeneration test.
- **Times.** Each compile timed, with a 30-minute stop per case.
  - [G] Separation dominates. The bench measured 1.8 s at 3 layers with 12 batches on integer dates
    (LAYERED_MONOTONE_CHECKERS.md:70–74). Majority's 56 batches, at about 10 windows each, with rational dates, should
    take tens of seconds to a few minutes.

## 5. What the circuit side would need

All of the following is [I] unless marked.

- **Cells and routing, majority a.** 6 cells in 3 layers.
  - L1 to L2: AB → port 0 of L2.0, AC → port 1 of L2.0, BC → port 0 of L2.1 (the copy).
  - L2 to L3: L2.0 → port 0, L2.1 → port 1.
  - Each external input drives two layer-1 ports: A to AB and AC, B to AB and BC, C to AC and BC.
  - For A∧B∧C and A∨B∨C: 3 cells in 2 layers, one wire per port in variant a.
- **Kinds of cell.**
  - `both`: a pair read. At layer 1 this is campaign 6's a/b. At L2 (A∧B∧C), and at L3 in other majority variants, it
    becomes a pair of routed pulses with the skew of their upstream latencies. The two-layer note flagged that read as
    never calibrated (DESIGN_NOTE_WIDEN.md A.4, "Not proposed").
  - `either`: two single-line lessons, like c.
  - `copy`: a single-port lesson. It needs a firing single read on port 0, so a line-like amplitude.
    - At layer 2 (majority a), a copy cell receives a routed line pulse from a layer-1 cell, so its lesson is a
      single-line lesson like c's. Campaign 6 measured that read. This differs from a unary first-layer cell of
      step 1, which receives an external input alone (coordinator's remark at review).
    - At layer 1 (A∧B∧C a, A∨B∨C a), the copy receives an external input alone. No campaign has run it.
  - `both(X, X)`: one source on two ports, a pair with no skew.
- **Measures per cell kind**, by analogy with campaign 6's decks, scans and one-sided sets:
  - `both`: its pair scan and one-sided set, as for a and b;
  - `either`: two line scans and its both-lines FIRE check, as for c;
  - `copy`: one single-port scan.
  - Majority a needs 3 pair scans, 2 × 2 line scans and 1 single-port scan. Campaign 6 needed 4 scans.
- **Per lesson,** every cell of every lower layer is read and recorded, as campaign 6's `teach` rows were. **Per
  test,** the whole network is read.
- **Every non-addressed cell must be read-only in every slot.** The theory tracks only the addressed cell's writes; the
  other cells' reads during a layer-1 lesson are not in the trace. The read-only gate of `dnf.py` and campaign 5's
  "G, MOVE_BOUND_MV" check carry that assumption.
- **One `SlotTiming` per layer.** All cells of a layer share skew, deadline and duration, so the copy and the either
  cell at L2 share one timing.
- **Calendar and cost:** section 3. At R = 7 a run is 29, 43 or 64 slots, against 35 to 39 for campaign 6.

## 6. Plan of phase 2 (after review)

The work happens in `research/learned-dnf-generator/layered/`, on the same branch or a new one, as the owner decides.

1. `lspec.py`, `lemit.py`, `lmirror.py` and `gencheck_layered.sh`, then test (a) on the repository's example.
2. `lsynth.py`, `lmutate.py`, and the cases of 4(b) and 4(c), with the controls, hashes and times.
3. A README with [K]/[I]/[G] and the interpreter of each result. Nothing is committed or pushed before the owner's go.

## 7. Not checked

- I compiled nothing in this phase. In particular I did not compile a layered file with Rat dates and 56 batches, and
  the kernel times of 4 are guesses.
- Whether `decide +kernel` evaluates the nested `TrainingTrace` and `ReadTrace` of a 3-layer, 6-cell network, written
  as list tables with `getD`, without the elaboration problems the example avoided by writing functions.
- The minimal-network search: it covers depth ≤ 3 and widths up to (3, 2, 1); the claims outside that range are
  arguments [I]. It checks only the stimulus clause of `Node.Valid`, not the parameters.
- Whether the copy cell's unused port 1 can take an initial gain of 0 in a fit from measures. That depends on how the
  campaign maps the cell.
- Whether a routed pulse can physically drive two ports (both(X, X)), or two cells: an external input on two ports.
- Read durations and latencies for layer-3 reads, the slot length they need, and the simulated cost per slot of a
  6-cell deck.
- The proofs of LayeredMonotoneCheckerProofs.lean beyond their statements and names.
- The cost of option 2 of section 3, a widened separation premise. I did not read the separation proofs.
- Step 1's choices ("Function family on the circuit"), which this note does not know. For example, whether step 1
  wires a shared input, which would decide variant c of A∧B∧C.
