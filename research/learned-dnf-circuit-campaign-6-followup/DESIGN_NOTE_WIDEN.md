# Design note: widening the learned circuit, and room for cell c under noise

**Status.** A written study, for review by the coordinator. It sets no rule and preregisters nothing. No simulation
was run, nothing was pushed, no session was created. Date: 2026-11-20. **Second version**, after the coordinator's
review of the first (SHA-256 `4f37493d…2d9a`); the changes are listed at the end.

**How to read the marks.**

- **[K] known**: read directly in a file, at the commit named.
- **[I] inferred**: my own reasoning or arithmetic on those files. Not reviewed by anyone.
- **[G] guess**: plausible, not supported by anything I read.

**Refs used.** `main` = `fc3cd895`. `C6` = `research/learned-dnf-circuit-campaign-6` at `2164b5a4`. `IMPL` =
`research/learned-dnf-circuit-campaign-6-impl` at `ecfcd1c1`. `ANA` =
`evidence/learned-dnf-circuit-campaign-6-c1-analysis` at `feb0927f`. "LC/" means `research/learned-coincidence/`,
"C5/" means `research/learned-dnf-circuit-campaign-5/`, "C6/" means `research/learned-dnf-circuit-campaign-6/`.
The 18 Lean files of LC/ that I cite have the same blob on `main` and on `IMPL` [K, compared blob by blob]. For a
Lean file, "commit" below is the last commit that touched it on `main`.

**A warning about the letter K.** Two different things are called K. In the claims, `K = 0` and `K = 3` name the
error budget: `beta_K = epsilon + K x sigma` (C5/PREDICTION.md lines 264 to 267, `IMPL`). In `MAPPING_U.md`, `K` is
an anchor constant of layer 1 (`K = max(8 - s*, s*)`). This note writes "budget K3" for the first and never uses the
second.

---

## The three findings, in plain words

1. **The Lean theory is already general; the campaign's gate generator is not.** The recognition theorem and its
   three checkers hold for any number of first-layer cells, outputs and inputs. But `gate4.py`, which writes the
   Lean file of each instance, is written for exactly one shape: two pair cells and one OR cell on four inputs. A
   second, more general theory (layers of two-input gates, PR #179) is proved with its checkers, and no campaign
   code uses it yet.
2. **Cell c has no room at budget K3 for a structural reason, not by bad luck.** One training step of a line of c
   is one dose on one port. Against it, the rules ask for a one-port noise budget below the crossing and a two-port
   noise budget above it. Those two budgets add up to 98 to 99.7 % of the step on every instance I could compute.
   So the crossing of each line must land in a window of 0.3 to 1.8 % of a step, on both lines at once.
3. **Three of the six levers can be evaluated on evidence that already exists.** The others need new runs. The
   cheapest decisive step is an audit of the noise actually seen in the 12 noisy runs of attempt c1.

---

## Part A. A family of functions

### A.1 Inventory of the Lean side

All files are in LC/. Every theorem below is listed in the audit `LC/Audit.lean` with its frozen type, and the
audit allows only `propext`, `Classical.choice` and `Quot.sound` [K, `Audit.lean` on `main`]. **I did not compile
anything**: "proved" below means "a `theorem` with that name is in the source and in the audit list".

| What | File, theorem | Commit, PR | Shape covered |
|---|---|---|---|
| One layer of AND cells | `Recognition.lean`, `learned_coincidence_recognition` | `18659a45` | Any N cells, any M inputs. Each cell learns the AND of its target ports. Targets must have at least 2 ports (`Parameters.jointTargets`, `Target.lean`, `bc4c1154`) |
| AND of ANDs, two layers | `TwoLayerTarget.lean`, `TwoLayerCoincidenceRecognition` | `18659a45` | **A frozen statement only.** I found no theorem that proves it (search over all `.lean` and `.md` files of `IMPL`: the name appears in its definition and in `TWO_LAYERS.md`, nowhere else) |
| AND then OR, two layers, two-sided calibration | `MonotoneRecognition.lean`, `two_layer_monotone_recognition` | `c45c0f71` (last touch; proved in #171) | Any A first-layer cells, B outputs, M inputs (`Cascade A B M`, `MonotoneTarget.lean`, `b0f6850e`) |
| Which functions that class can express | `MonotoneCharacterization.lean`, `monotone_characterization` | `a616cd0a`, #171 | A function is monotone exactly when some valid `Cascade A B M` computes it. One first-layer cell per minimal term; no bound on their number (`MONOTONE_DNF.md`) |
| **AND then OR, one-sided on firing masks** (the campaign's theorem) | `MonotoneOneSidedRecognition.lean`, `two_layer_monotone_recognition_one_sided` | `c45c0f71`, #177 | Same generality: any A, B, M. A firing read of the OR cell needs only a lower bound on each arrived line alone, and "the observed mask scores at least as much as any firing submask" (`MonotoneOneSidedTarget.lean`, `FiringMaskRead`, `a4e03280`) |
| Its three premise checkers, sound and complete | `MonotonePremiseSoundness.lean`: `cascade_valid_checker_sound`, `training_separation_checker_sound`, `cascade_calibration_one_sided_checker_sound`; `MonotonePremiseCompleteness.lean`: the three `_complete` | `24985071` (last touch); proved at `2e586aa2`, #178 | Any A, B, M. The checkers are `checkCascadeValid`, `checkTrainingSeparation`, `checkCascadeCalibrationOneSided` (`MonotonePremiseTargets.lean`, `423a24fd`) |
| **Any number of layers of two-input gates** | `LayeredMonotoneRecognition.lean`, `layered_monotone_recognition_one_sided` | `24985071`, #179 | Any M inputs, L layers, width N. Each cell is one of five gates: off, on, copy, both (AND), either (OR) (`LayeredMonotoneTarget.lean`, `Gate`, `0e849f2d`). Each cell has its own dose, threshold, budgets, write limit and rail (`Cell`) |
| Which functions the layered class can express | `LayeredMonotoneCharacterization.lean`, `layered_monotone_characterization` | `b5dd045a`, #179 | Exactly the monotone functions |
| Its four checkers, sound and complete | `LayeredMonotoneCheckerProofs.lean`: `layered_valid_`, `layered_separation_`, `layered_training_calibration_`, `layered_read_calibration_checker_sound` and `_complete` | `24985071`, #179 | Any cascade. Measured kernel times are in `LAYERED_MONOTONE_CHECKERS.md` (3 layers: at most 1.8 s per checker on its fixture) |
| A worked three-layer example | `LayeredMonotoneExample.lean`, `three_layer_example` | `24985071`, #179 | `(A and B) or (C and D)` as AND, copy, OR, with a full synthetic trace |

**Two structural limits of the two-layer theory** [K, `Target.lean`, `MonotoneTarget.lean`]:

- One `dose`, one `maxWrites` and one `rail` per layer (`Parameters.dose`, `Disjunctions.dose` are not indexed by
  cell). The campaign lives with this through `MAPPING_U.md`: each cell's stored voltage is counted in its own
  doses, and one score dose `d` is shared (`C6/drafts/MAPPING_U.md`, `b825d6aa`, section 1).
- One `trainingError` and one `testingError` per cell. This matters in part B.

The layered theory has per-cell doses, but also one `trainError` and one `testError` per cell
(`LayeredMonotoneTarget.lean`, `Cell`).

**What the physical cell allows** [K]: the simulated cell has two ports (`research/learned-dnf-circuit/dnf.py`
docstring, `IMPL`: "the cell of `../circuit/cell.spice` has two ports"). So, in the two-layer theory, a first-layer
term has at most 2 inputs and the OR cell selects at most 2 lines [I]. An OR of three terms, such as majority of
three, needs either a three-port cell or the layered theory with copy cells [I].

### A.2 What campaign 5's kernel gate assumes, exactly

The gate has three parts: `C5/check.sh`, `C5/gate4.py` and the per-instance file `Gate6_<seed>.lean` that
`predict6.gate_each` writes with `gate4.lean_file` (all at `b825d6aa` or earlier on `IMPL`; the four files of
attempt c1 are at `b6e319f6`).

**`check.sh`** [K]:

1. compiles 13 modules of LC/, from `Target` to `MonotonePremiseCompleteness`. **No `Layered*` module is
   compiled**;
2. regenerates campaign 5's reference cases and mirror mutations from phase 0's nominal calibration, and requires
   them byte-identical to `C5/expected/`. These fixtures are cases of `(A and B) or (C and D)` (`C5/cases.py`
   docstring: P0 to P6p);
3. for each extra file given: refuses `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`,
   `extern`; compiles it with warnings as errors; requires every theorem's axioms within the three allowed.

Step 3 says nothing about the function. Any file that imports the 13 modules passes through it unchanged [I].

**`gate4.py`** [K] hard-codes the shape:

- the type `Cascade 2 1 4`: two first-layer cells, one output, four inputs;
- the terms: cell 0 reads inputs 0 and 1, cell 1 reads inputs 2 and 3 (`term`);
- the gain table `[[a1, a2, 0, 0], [0, 0, b1, b2]]`; one dose for layer 1 (`dose := d['a']`); `maxWrites := Q1`;
- the OR cell selects both lines (`lines := fun _ _ => true`), never constant (`alwaysFire := false`);
- a wire delay of 3/2 on both lines; an empty held-out list;
- two fixed slot timings: skew 1/50, deadline 11/10, duration 22 for layer 1; 11/10, 11/5, 19 for c;
- tables of 16 patterns keyed by the letters `ABCD`, and four reference scores of c per pattern (none, line 2,
  line 1, both);
- for each instance and each budget (K0, K3), one theorem `checks_<seed>_K<n> : checks ... = true` or `= false`,
  as the Python says. So the file compiles only if Lean agrees with the Python, in both directions;
- when the verdict is true, a second theorem `outputs_<seed>_K<n>` applies
  `two_layer_monotone_recognition_one_sided 2 1 4`.

Example [K, `C6/stages/c1/Gate6_7804.lean`, `b6e319f6`]: three theorems, `checks_7804_K0 = true`,
`outputs_7804_K0`, `checks_7804_K3 = false`; its log `check_7804.log` ends "check.sh: passed".

**Answer to the question.**

- *Another monotone DNF on three cells, unchanged?* **The theory and `check.sh`'s audit step: yes. `gate4.py` and
  its Python mirror: no** [I]. A new generator is needed, with the terms, the gain table and the table sizes as
  parameters. With two-port cells, the three-cell functions the two-layer theorem covers are: an OR of at most two
  terms of at most two inputs each. Examples: `(A and B) or (B and C)`, `(A and B) or C`, `A or B` [I].
- *Larger networks?* **Not with this gate** [I]. The two-layer theorem would need an OR cell with more than two
  ports. The layered theorem (#179) covers them, but `check.sh` does not compile it, no generator writes its
  traces, and no Python mirror of its four checkers exists in the campaign code.

### A.3 Inventory of the code: specific or generic

From docstrings, function lists and targeted reading. I read `predicted.py`, `gate4.py`, `predict6.py`, `c4.py`
and the start of `dnf.py` in full; the others through their docstrings and searches (see "Not checked").

| Code (`IMPL`) | Specific to `(A and B) or (C and D)` | Generic |
|---|---|---|
| `research/learned-dnf-circuit/dnf.py` | `INPUTS` (one cell per input), `LINES`, `truth`, the 16 `patterns`, `calendar` (both layer-1 cells trained in one slot, then the two lines alternately), `zero_error` | the timing constants |
| `C5/predicted.py` | `LAYER1`, `LAYER2`, `TARGET`; `needs` (pair for a and b, single line for c); the budget rule of c in `instance`; every clause of `room`; `learning_ports` (line 1 comes from a, line 2 from b); `observation` (letters `ABCD`, masks "1", "2", "12") | exact arithmetic: `solve`, `ceil_sum_sqrt`, `noise_square`, `read_budget`, `sensitivity` |
| `C5/gate4.py`, `C5/cases.py`, `C5/mirror_mutations.py`, `C5/expected/` | everything (A.2) | nothing |
| `C6/batch/predict6.py` | `CROSSINGS`, `NEEDS`, `BOTH`, `ALONE`; `anchors` (the pair rule of layer 1, the two-line rule of c); the decoder clauses of `measure_instance` | `deck_w` (the stored-voltage coordinate), `u0_check`, `gate_each` (one Lean file and one `check.sh` call per instance) |
| `C6/batch/scan6.py` | the three-cell deck and the amplitudes by cell (0.49 on a and b, 1 on c) | the robust scan itself: it takes a cell, a set of moving ports and a read kind (`READS`, `MOVING`) |
| `C6/batch/schedule6.py`, `C6/campaign6/stages6.py`, `inputs6.py`, `meas6.py` | the nine measure runs per instance and their dependencies | the stage files, manifests, two-shard rule, costs and limits |
| `C5/plans4.py`, `C6/campaign6/net6.py` | built from `dnf`'s tables and `c4.CELLS = (a, b, c)` | `net.deck(cells=...)` takes any list of cells (`research/network-circuit/net.py`) |
| `C5/analyze.py`, `C6/campaign6/analyze6.py` | `word_claims` and `n_own` over the six named ports, M4, M8's `run_observation` | the reproduction check, the minimum of 2 instances, the refusal of unknown run ids |
| launch kit, `marker_check.py`, `publish_evidence.py`, `collect.py`, `c6.py` | the seed lists | everything else |

In short [I]: the measurement method, the kit and the audit are reusable. The network description is spread over
about eight modules as constants and hand-written clauses, not held in one table.

### A.4 Candidate next functions

Costs are rough and relative to campaign 6, whose batch had 90 runs and whose attempt c1 had 62
(`C6/BATCH_REPORT.md` section 1; `C6/REPORT.md` section 1). I give no calendar time: I have no basis for one.

**Candidate 1: `(A and B) or (B and C)`, the same three cells, one shared input.**

- *What it is.* Input B feeds a port of cell a and a port of cell b. The function is "B and (A or C)". Its truth
  table is over the 8 patterns of the three inputs A, B, C, from none to ABC; it fires on AB, BC and ABC.
- *Reused.* The theorem and the checkers, unchanged: the two terms AB and BC do not contain each other, which is
  what `Cascade.reachable` asks (`MonotoneTarget.lean`). The cells, the amplitudes, all nine measure runs, the
  scan, `MAPPING_U`, the kit, the stages.
- *New in Lean.* No theory. A generated file of type `Cascade 2 1 3`.
- *New in code.* A generator with the terms as parameters, and its mirror; `dnf`'s tables with one input feeding
  two cells; the truth table, the calendar and `observation`; the claims' port list.
- *What it would show that campaign 6 did not* [I]. While line a is taught with pattern AB, cell b receives B
  alone. So a single-port read of a trained pair cell happens inside the training, not only in the tests. The
  one-sided sets already measure that bound (`MAPPING_U.md` section 2), so the prediction exists; the network has
  never exercised it during teaching.
- *What must be checked for that read, beyond the one-sided sets* [I]. In the Lean statements the read is already
  a row: every lesson holds one `teach` read per first-layer cell, the calendar premise quantifies over all of them
  (`TrainingSeparation`, through `endsBefore`, "for all a"), and so does the calibration premise
  (`CascadeTrainingCalibration`: a `CalibratedAdditiveRead` of every first-layer cell on the taught line's
  pattern, with the testing budget). In campaign 6 that row of the other cell is an empty read. Here it becomes a
  real pulse on b in every lesson of a, and on a in every lesson of b. So three things need their own check: the
  calendar premise with those pulses present, since each pair cell is now pulsed in every teaching slot and not in
  every other one; the bench's separation hypothesis H for the same reason (`dnf.separation`, 16 units; the slots
  are 22 apart, so it should hold, by arithmetic only); and the residual of that single-port read at the trained
  stage against the testing budget.
- *Cost.* Code: moderate, mostly the generator and the function tables. Compute: about one campaign 6 (the deck
  and the run kinds are the same). Lean: none.
- *Limit.* It is a small step: same cells, same depth. Cell c has the same noise problem as today.

**Candidate 2: the same function through the layered theory (#179).**

- *What it is.* `(A and B) or (C and D)` again, but certified by `layered_monotone_recognition_one_sided` and its
  four checkers, as two layers: two `both` cells, one `either` cell. The copy layer of `LayeredMonotoneExample` is
  not needed, because both lines come from the layer just below [I, from `Node.source`].
- *Reused.* All measures, all evidence formats, the kit. Possibly the existing records of the batch, as
  development data, and those of attempt c1 if the owner allows it: see the catch below.
- *New in Lean.* No theory. `check.sh` must also compile the `Layered*` modules, which changes a frozen file, so it
  would be a new check script. New reference cases and mutations for the four layered checkers.
- *New in code.* A generator for the layered trace format (`TrainingTrace`, `ReadTrace`: one replay of the lower
  layers per lesson) and a Python mirror of four checkers.
- *The catch* [I, from `trainingBatches`]. The layered separation orders the training batches by layer, cell,
  group and round, each batch ending before the next begins. Campaign 6's calendar trains a and b **in the same
  slot** (`dnf.calendar`, "stage 1: layer 1, both cells in one slot"). So either the calendar changes (each cell
  trained in its own slots: new decks, and the existing network runs cannot be reused), or the Lean separation is
  generalized. I did not check whether the theorem's proof needs that order.
- *Cost.* Code: large (generator, mirror, cases). Lean: small if only the check script changes, unknown if the
  separation must be generalized. Compute: one campaign 6 if the calendar changes.
- *Why do it.* It is the door to every larger network (candidate 3), and it has per-cell doses.

**Candidate 3: majority of three, `(A and B) or (A and C) or (B and C)`: the first function three cells cannot
compute.**

- *What it is.* Three AND cells, then an OR of three lines. With two-port cells this is three layers: three `both`
  cells; one `either` and one `copy`; one `either`. Six cells [I].
- *Reused.* The method, the scan, the kit. Candidate 2's generator and mirror.
- *New in Lean.* Nothing beyond candidate 2.
- *New in code.* A copy cell has no precedent in the campaigns: a one-port read trained alone, at a line
  amplitude. A six-cell deck. A calendar with lessons on three layers.
- *Cost.* Compute: a six-cell deck is at least twice the three-cell one per run [G], with more scans per instance
  (about 8 scans against 4 [I]). Eligibility falls: the batch had 6 of 10 eligible with three cells
  (`BATCH_REPORT.md` section 1); with six cells it could be near a third [G]. Under noise it has two OR cells, so
  the problem of part B twice.
- *Why wait.* It needs candidate 2 first, and a solution to part B, or its noise claims are empty in advance.

**Not proposed: the four-input AND, `(A and B) and (C and D)`.** It looks cheap (same three cells) but is not
[I]. The two-layer statement for it is not proved (A.1). The layered theorem covers it, but c would have to need
both lines to fire, whereas today both lines of c fire together already at the preset (`MAPPING_U.md` section 1:
"the both-lines model score at `s = 0` is exactly THETA"). So the line amplitude must be lowered, and the two
routed pulses then arrive with the skew of their upstream latencies, a pair read that no campaign has calibrated.

---

## Part B. Room for cell c under noise

### B.1 Why c has no room at budget K3

**The rules** [K]:

- The budget of one port at K3 is 3 sigma in score units: `3 x s x sqrt(w^2 + b^2 + n x d^2)`, where `s` is the
  score per mV of stored voltage, and `w = 0.094`, `b = 0.111`, `d = 0.009` mV. "For a read of two ports, the two
  terms are added linearly" (C5/PREDICTION.md lines 264 to 268; `predicted.read_budget`).
- Each cell has one training budget and one testing budget, "the largest per-read budget over the reads that the
  kernel checks with that field". For c, the training budget covers its single-line teaching reads; the testing
  budget covers its test reads, **which include the both-lines read** (C5/PREDICTION.md lines 279 to 284). In the
  code: `tr` of c is a one-port budget, `te` of c is `read_budget(eps, [sens1, sens2], [n1, n2], ...)`, a two-port
  one (`predicted.instance`).
- For each line of c, the kernel's validity check asks three things (`MonotoneTarget.lean`, `lineCheck`): silent
  with the training budget at every stage below the need; firing with the training budget at the need; **firing
  with the testing budget at the need**.

**What follows** [I]. Call "step" the score that one dose adds to a line (`d_c`). Then:

- below the crossing, the line must be more than `tr` under the threshold;
- above it, at least `te` over the threshold;
- the two stages are one step apart. So `tr + te` must fit inside one step, and the crossing must land in what is
  left.

In numbers: 3 sigma on one port is about 0.44 mV, and a dose is about 1.35 mV, so `tr` is about 0.33 step and
`te` about 0.66 step. **What is left is about 0.01 step.**

**Checked on the pushed records** [I: my arithmetic on K records; the script is not kept anywhere].

- The nominal cell, from `BATCH_REPORT.md` section 2: budgets 4 603 and 9 145, step 13 943. Sum 13 748. Left: 195,
  which is **1.4 % of a step**.
- Attempt c1, from `C6/stages/c1/PREDICTED.json` (`b6e319f6`, SHA-256 `a8e1751e…aab8`), fields `guarded.dose.c` and
  `budgets.K3.c`:

  | Seed | Step | `tr` | `te` | `tr`/step | `te`/step | Left |
  |---|---|---|---|---|---|---|
  | 7802 | 19 243 | 6 336 | 12 555 | 0.329 | 0.652 | 1.8 % |
  | 7803 | 13 329 | 4 405 | 8 719 | 0.330 | 0.654 | 1.5 % |
  | 7804 | 12 037 | 4 041 | 7 955 | 0.336 | 0.661 | 0.3 % |
  | 7805 | 14 475 | 4 803 | 9 489 | 0.332 | 0.656 | 1.3 % |

- The batch, from `C6/rehearsal/PREDICTIONS_BATCH.json` (`b825d6aa`, SHA-256 `e2e9e572…cc89`), the seven instances
  with budgets: left between 0.4 % and 1.6 %.
- My reconstruction of each line's own room agrees with the record's `learning_ports` on all four c1 instances
  (c1 of 7802, c2 of 7803, c1 of 7804, none on 7805), and with the 9 port-runs N-own counted on c
  (`REPORT.md` section 2).
- Over the 22 lines of those 11 instances: 8 have their own room (both sides with `tr`); 7 clear `te` above; **1
  does both** (line 1 of 7701, which landed at 0.659 step above its crossing, inside a window from 0.656 to 0.668).
  No instance has both lines.

**Why a and b are better off** [I]. A training step of a pair moves two ports, so it is two doses. Their budget is
also a two-port budget, on both sides. So the budgets take 0.33 + 0.33 of the step and leave about 0.34. Observed:
a or b has room at K3 on 7 of 22 cells (5 of 14 in the batch, 2 of 8 in c1), which is 0.32.

**So c is the only cell that pays a two-port budget against a one-port step** [I]. That is the whole cause.

**What it implies for the claims, if crossings land anywhere in a step with equal chance** [I, and the equal
chance is a G]:

- N-out of a, or of b: about one eligible instance in three counts. With 4 eligible instances, two or more count
  with probability about 0.42. Attempt c1 had exactly one for each.
- N-out of c needs a, b and c together: about 0.34 x 0.34 x 0.012 x 0.012, **two in 100 000**. No campaign size
  reaches it.

### B.2 The levers

The useful number is **r = 3 sigma of one port, in doses**. Today r is about 0.33. The windows are: `1 - 2r` for a
pair cell; `1 - 3r` for a line of c under today's rule; `1 - 2r` for a line of c if lever 1 is applied.

| # | Lever | What it does | What it costs | What it would break | Evidence |
|---|---|---|---|---|---|
| 1 | **The budget rule of c**: a one-port testing budget for the single-line reads, the two-port budget kept only for the both-lines comparison | A line's window goes from about 1 % to about 34 % of a step | A new prediction module (campaign 5's `predicted.py` is frozen) and a new preregistered rule. No new Lean theory | Nothing in the theorem, if my reading holds: see below | **Existing**: computable on development records (the batch's) |
| 2 | **The dose**, made larger against the same noise | r falls in proportion. At twice the dose: windows 0.67 (pairs), 0.50 (lines, today's rule), 0.67 (lines, lever 1) | A cell design change. Every per-cell result so far is at about 1.35 mV | Needs fall (from 3 to 5 in attempt c1 to 2 or 3), so the prediction says less; the noise constants and the 1 % dose constancy must be measured again; the layout track's dose criterion | **New runs** |
| 3 | **Where the crossing lands**: bring each stored voltage to a chosen place in its step before training | Replaces chance by placement. Works only if the window is wider than the placement error | The scan driver already moves a port to a state within 2 uV (`scan6.py` docstring), through an imposed leak | The claim "not tuned by hand" (`README.md` section 1). The imposed leak is a testbench device, not a circuit one | **New runs** |
| 4 | **The noise constants** | A smaller measured sigma lowers r directly | An audit of existing runs first; then an owner's decision, since decision 5 fixed them | The comparability with campaigns 4 to 6 | **Existing** for the audit; a decision for the rest |
| 5 | **Thresholds, the step `d_c`, the line amplitude** | Nothing for r | | | **Existing**: see below |
| 6 | **Routing and the number of lines** | Under today's rule, a third line makes it impossible | | | **Existing**: see below |

**Lever 1 in detail** [I]. In the theorem, c's testing budget is used in three places only: the firing of each
line alone at its need (`lineCheck`), the silence of the empty read (`Disjunctions.check`), and the lower bound on
each arrived line alone in a firing read (`FiringMaskRead`, the clause on `singleton a`). All three are reads or
reference scores of **one line or none**. The both-lines read enters only through "the observed mask scores at
least as much as any firing submask", which carries no budget in Lean. So a one-port testing budget for c seems
enough for the theorem's premises; today's two-port value comes from the wording "the largest per-read budget over
the reads that the kernel checks with that field". The Python `room` has one more clause, "the pair is at least
`max(Z_1, Z_2) + beta`"; it can keep the two-port budget, and its margin is large (on the nominal cell the pair
exceeds the larger line by 0.67 of the FIRE level, `research/learned-dnf-circuit/DECISIONS.md`, `IMPL`).
**This reading must be reviewed**: it is the central inference of this note, and I am not the author of the
theory.

*One independent confirmation, at the level of the statements.* The coordinator checked the same reading against
the Lean source on `main` (`fc3cd895`) and agrees: the second layer's `testingError` appears in
`MonotoneTarget.lean` (the single-line and no-line checks), in `FiringMaskRead` (the empty reference and
`scoreAt (singleton a)`), and in the calibration only on the branch where no selected line arrived. Neither of us
read the proofs. This is not a proof review.

*What this says about campaign 6's rule, and what it does not.* The preregistered text (C5/PREDICTION.md lines
279 to 284) has two sentences that do not point the same way [K for the text, I for the reading]:

- the general one: each budget is "the largest per-read budget over the reads that the kernel checks with that
  field". If the kernel never applies `testingError` to the both-lines read, this sentence points to a one-port
  value for c;
- the specific one, just after: "For `c`, [...] `testingError` [covers] its `secondTest` reads". The both-lines
  read is a `secondTest` read, so this sentence points to the two-port value.

The frozen `predicted.instance` computes the two-port value. So the frozen code follows the specific sentence, and
is more conservative than the general sentence read alone: it can only count fewer runs, never more. Three things
must be said with it:

- (a) **It changes no verdict of campaign 6.** The counted runs were judged by the frozen code, as preregistered.
- (b) **It is a post-hoc observation, not a claim.**
- (c) **Whether it deserves a note in campaign 6's record is the owner's call.**

This note does not compute what campaign 6 would have counted under another rule (see "Changes" at the end).

What lever 1 gives on development data only, the batch's seven instances with budgets [I]: c would have room on
1 of 7 (7710, both lines with own room), and on that instance b has no room. With lever 1 alone the expected rate
for a, b and c together is about 0.34 to the fourth power, 1.3 %. Lever 1 is necessary, cheap, and not
sufficient.

**Lever 2 in detail.** The combined rate for a, b and c, with crossings landing with equal chance [I, G as above]:

| Dose (or noise divided by) | r | Today's rule | With lever 1 |
|---|---|---|---|
| x 1 | 0.33 | 0.002 % | 1.3 % |
| x 2 | 0.165 | 11 % | 20 % |
| x 3 | 0.11 | 27 % | 37 % |
| x 4 | 0.083 | 40 % | 49 % |

How the dose is set [I, from `research/circuit/cell.spice` on `IMPL`: `vhi=0.6`, `vlo=0.5`, `cs0=400f`,
`cf0=30p`]: `(vhi - vlo) x cs0 / cf0` is 1.333 mV, close to the measured 1.339 to 1.356 mV (`MAPPING_U.md`). So
the two levels or the capacitor ratio would set it. That formula is my reading of four parameters, not a statement
of the repository. Whether the noise in mV stays the same at a larger dose is a guess [G]; the per-dose term `d`
may well grow with it.

**Lever 4 in detail.** Three facts from attempt c1's analysis (`ANA`, `RESULTS.json`, SHA-256 `1b6e21f2…98e8e2`)
[K for the numbers, I for the reading]:

- Comparison M1: the outputs that did **not** count for N-out answered as predicted in every noisy run, 30 of 30.
  With the 6 counted ones, all 36 output-runs under noise were as predicted, most of them without room.
- Comparison M7: over each port's three noisy runs, the spread of the stored voltage at the end of training is
  0.002 to 0.068 mV (median 0.028), against a model sigma of 0.146 mV. The largest is 0.46 of the model's.
- Comparison M6: no word differed from its primed word in any noisy run.

This suggests that the budget is wide for this deck, perhaps by a factor of two or more [I]. It does not prove it:
three runs per port is a small sample, and M7 measures the stored voltage, not the noise of the read itself (the
constant `w`). Against it [K]: decision 5 raised the constants "to the values campaign 3 measured"
(`DECISIONS.md`); `README.md` says that in campaign 3 "the measured noise was larger than those constants"; and the
independent noise model of the noise study is "not validated" (commit `fd25955a` on `main`, by its message). So
the constants cannot simply be lowered. They can be measured on this deck.

**Lever 5.** The step `d_c` is a unit, not a quantity: the sensitivity is `d_c` divided by the dose in mV
(`predicted.sensitivity`), so the budgets scale with it and the ratio does not change [K for the code, I for the
conclusion]. A threshold or an amplitude changes how many doses a line needs, and where its crossing lands, but not
r [I]. A cell has one threshold for two lines, so a threshold shift cannot place both crossings [I].

**Lever 6.** Under today's rule the testing budget of c grows with the number of selected lines. With three lines
it would be about 0.99 step and the sum with `tr` exceeds one step: no position works [I]. Under lever 1 the
number of lines no longer enters. Teaching the lines together is not an option: that is an AND.

**Not a lever: more instances.** They help a and b (with about 10 eligible instances, each of N-out a and N-out b
would have two counted instances with probability about 0.9 [I]). They do nothing for c.

### B.3 What existing evidence tells, and what needs new runs

| Question | Answered by existing evidence? |
|---|---|
| Why c has no room | **Yes** (B.1) |
| What lever 1 gives on the batch's development instances | **Yes** (B.2). Its reading of the theorem now has one independent confirmation on the statements |
| Whether the noise seen in the c1 runs is smaller than the budget | **Partly** (M1, M6, M7); fully by an audit of the pushed traces, with no simulation |
| Whether a larger dose keeps the cell's laws (constant dose, clean scans, same noise in mV) | **No**: new runs, first on the nominal cell |
| Whether a port can be placed within a step, and stay there | **No**: new runs |
| Whether N-out of c holds when it has room | **No**: it has never had a counted run |

---

## Part C. A second simulator, or a chip

**What a second simulator would test.** Today "the per-cell measures and the network runs use the same simulator
and the same deck" (`C6/PREDICTION.md` section 11). The claim is that the network does what its cells, measured
alone, say. A second simulator asks two different questions [I]:

- *Same method, other solver*: measures and network both in simulator B. This tests that the result is a property
  of the circuit and not of one solver's numerics.
- *Crossed*: measures in A, network in B. This is the closest a simulation gets to "measure the chip, then run
  it". I expect it to be much harder [G]: thresholds are scanned to 1/256 of a step, about 5 uV, and two solvers
  may differ by more than that.

**Its main obstacles.**

- The instances would not be the same cells. Mismatch is drawn by the simulator from the PDK's `tt_mm` section
  (`c4.SECTION`); another simulator draws other samples, unless each device's drawn parameters are exported [I].
- The injected noise is ngspice's own: `trnoise` sources seeded through a process-number shim
  (`C5/noisemodel.py` docstring). It has no direct equivalent elsewhere [I].
- The scan drives one interactive simulator session and imposes states step by step (`scan6.py` docstring). A
  simulator without that control needs a different scan [G].
- Solver fragility is already visible with one simulator: 7707's operating point did not converge
  (`BATCH_REPORT.md` section 5.1), and campaign 4 was lost to time limits (`CAMPAIGNS_4_AND_5.md`).
- I did not check which other simulators can read the SKY130 models.

**What a chip would test.** Everything section 11 lists as out of reach: real mismatch, real noise, wires, a real
router, and leakage of the stored voltage (the deck's leak resistance is `rlk=1e18`, `cell.spice`).

**Its main obstacles.**

- **The measurement itself** [I]. The method reads each stored voltage to 20 uV and brings a port to chosen states
  through an imposed leak. On silicon the stored node is not visible without a buffer that loads it, and the
  imposed leak does not exist. A chip version of the method would have to measure thresholds from outside, by
  counting pulses or by sweeping a pulse amplitude [G]. That is a new method, to be shown first in simulation.
- **Noise** [K]. No validated noise model exists (`fd25955a`), so the budgets of part B cannot be set for silicon
  in advance.
- **Layout** [K]. One cell has been laid out, not a network; the extraction is capacitance only, with ideal
  capacitors and resistors; 7 of 16 ports were certified again, and the dose moved to 1.309 mV on one layout
  before it was repaired (`research/sky130-layout/CONCLUSION.md`, `main`).
- **Ideal parts** [K]: the router and the pulses are ideal (`README.md`, Limits).
- Cost and delay of a fabrication run: I have no information.

**My reading** [I]: a second simulator is premature while the noise claims are structurally empty for c, and a
chip is premature while the measurement method needs access that a chip does not give. Both become meaningful
after part B is settled.

---

## One recommended first experiment

**A noise audit of attempt c1's pushed runs, with no new simulation. Subject to the owner's decision**: it uses
campaign 6's runs as development data, and only he can allow that. The coordinator will put the question to him.
Without that decision, nothing of it is done.

*What.* On the 4 quiet runs and the 12 noisy runs of attempt c1 (evidence branches listed in `REPORT.md` section
13), for every read: the difference between the noisy run and the quiet run of the same instance, in stored
voltage and in read score, converted to doses. From it, the measured r per port, to compare with the 0.33 of the
budget. The audit measures noise. **It does not recount campaign 6's claims under another rule.** What the
measured r would give is then worked out on the windows of B.2, and on development records only.

*Why this one.*

- It costs no compute and spends no new seed. Campaign 6 is closed; whether its runs may serve as development
  data is the owner's decision, as said above.
- It separates the two families of levers. If the measured r is near 0.1, the path is "measure the constants on
  this deck, apply lever 1", with no change to the cell, and the rates of B.2's table at "x 3" apply. If it is
  near 0.33, the cell itself must change (lever 2), and the first simulation is then a nominal-cell run at a
  larger dose.
- Every later choice needs this number: the size of a campaign, the choice among the candidates of part A, and
  whether a wider OR is worth building.
- It also forces the review of lever 1's reading of the theorem, which is the weakest link of this note.

*What it cannot do.* It establishes no claim. It is exploratory, on instances selected by eligibility, with three
noisy runs each.

---

## Not checked

- **I compiled no Lean file and ran no `check.sh`.** No Lean toolchain was used. "Proved" rests on the source text
  and the audit list.
- I did not read the proofs, only the statements and the checker definitions. For the layered theory I read the
  target file and the end of the characterization, not the recognition proof or the checker proofs.
- Lever 1's reading of where the testing budget enters the theorem is mine, from `MonotoneTarget.lean`,
  `MonotoneOneSidedTarget.lean`, `MonotoneOneSidedRecognition.lean` and `MonotonePremiseTargets.lean`. The
  coordinator confirmed it on the statements. No one has checked it against the proofs.
- For candidate 1, I did not work out a calendar or compute its separations; the "should hold" on H is the
  difference of two constants.
- The nominal cell's figures (4 603, 9 145, 13 943) are taken from `BATCH_REPORT.md`; I did not open the evidence
  at `4495394`.
- Of the evidence branches I opened only the c1 analysis (`feb0927f`), and in it only `RESULTS.json`. I opened no
  trace, so I do not know whether the audit's per-read quantities are all recorded.
- Read only through docstrings and searches: `analyze.py`, `cases.py`, `mirror_mutations.py`, `run4.py`,
  `plans4.py`, `stages6.py`, `analyze6.py`, `meas6.py`, `net6.py`, `inputs6.py`, `schedule6.py`, `scan6.py`, the
  launch kit, the tools. Campaign 5's `PREDICTION.md` was read only around its budget rules (lines 50 to 66 and 255
  to 310).
- The attribution of commits to PRs #171, #177, #178 and #179 is from the merge titles on `main` and the commit
  messages, not from the PR pages. I did not look at PR #182.
- The room tables of B.1 and B.2 come from a short script of mine run on the pushed JSON records. It was not kept
  and not reviewed. The percentages of B.2 assume that a crossing lands anywhere in its step with equal chance.

---

## Changes since the first version

The first version is SHA-256 `4f37493d4fac866ddc01decc48aef9b09f1e3098b6381c4b03d6eb244b4e2d9a`. After the
coordinator's review:

1. **B.2, lever 1**: added the coordinator's independent confirmation of the reading, on the statements only; added
   what the reading says about campaign 6's preregistered rule, with the three statements (a), (b), (c). I wrote
   that the rule's two sentences point in different directions and that the frozen code follows the specific one;
   the review had put it as "the frozen code is more conservative than the rule's text", which I found true of the
   general sentence only.
2. **A post-hoc count removed, and declared.** The first version said what lever 1 would give "on the existing 11
   instances", which included attempt c1's four campaign instances, and concluded that N-out of c "would still
   count nothing". That was a count of campaign 6 under another rule, which this project avoids. It is removed
   here: lever 1's arithmetic now uses the batch's development instances only. The first version was sent, so the
   sentence exists; it is withdrawn, not erased. For the record, it changed nothing: it counted no run.
   The descriptive table of B.1 (c1's budgets against its step, from the pushed record) is kept: it describes the
   frozen rule and recounts nothing.
3. **A.4, candidate 1**: the truth table's pattern set is stated; a paragraph says what the teaching read of the
   other cell needs checked, in the calendar premise, in H and in the calibration premise.
4. **The recommended experiment** is marked "subject to the owner's decision" in its first line, and no longer
   includes a recount on the campaign's records.
