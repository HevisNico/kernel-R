# A circuit network that learns (A and B) or (C and D), campaign 5: predictions

**Draft for review, fourth version** (after the coordinator's reviews of the drafts at `eefeb2b`, `f89c23c` and
`edb7438`), on the work branch `research/learned-dnf-circuit-campaign-5-wip`. Once the review gives a go,
this text, byte for byte, becomes `research/learned-dnf-circuit-campaign-5/PREDICTION.md` and is pushed alone on
`research/learned-dnf-circuit-campaign-5`, before any implementation of campaign 5. Nothing in it may be changed
afterwards. A wrong rule is corrected by an amendment file, pushed alone before the run or the computation it
concerns. This file is written so that it needs no amendment.

Campaign 5 tests the same claim as campaign 4, with the same theorem and the same kernel gate. Campaign 4 tested
nothing: every guard-on calibration deck of its stage M reached its 660 s time limit, so no instance was measured.
This file folds into one text campaign 4's `PREDICTION.md`, its amendments 1 to 11, the lessons of its report, and
the owner's decisions for campaign 5 of 2026-11-17. Each rule names its source in brackets:

- **[C4 §x]**: campaign 4's [`PREDICTION.md`][c4p] (commit `1596b36`, SHA-256 `714cb6b7…7ee69c34`), section x;
- **[C4-An §y]**: campaign 4's amendment n ([`AMENDMENT_n.md`][c4dir]), section y;
- **[C4 report]**: campaign 4's [`REPORT.md`][c4r];
- **[D5-k]**: the owner's decision k for campaign 5 (2026-11-17, listed below);
- **[L: …]**: a lesson of campaign 4, from its report and its sessions, built in from the start;
- **[new]**: a rule this file sets for a point the sources leave open.

The files of campaign 4 are cited at commit `6232e16` of the closed branch `research/learned-dnf-circuit-campaign-4`.
Campaign 4's branches are not touched.

Everything here is a transistor-level simulation (ngspice 42, SKY130 models) of three R cells of
[`../circuit/cell.spice`](https://github.com/HevisNico/kernel-R/blob/8bcd3d744f101378c308a0af9da80631dded715f/research/circuit/cell.spice), with the junction areas of stage J, joined by an ideal router
outside the simulator. There is no layout, no wire between the cells and no silicon. The circuit does not verify
the proved read window, and nothing here says that it does. [C4 §intro]

## 1. What is tested

The guarded theory (#168 to #171, and #177) says that an AND-OR cascade trained only by its own emitted pulses learns
exactly the monotone Boolean functions. This campaign asks whether three circuit cells with mismatch that no one has
looked at, trained by their own pulses, **learn `(A and B) or (C and D)` and answer every one of the 16 input patterns
as computed beforehand from per-cell measures**. [C4 §What is tested; D5-2]

The theorem this campaign stands against is `TwoLayerMonotoneRecognitionOneSided`, proved by
`two_layer_monotone_recognition_one_sided` in `research/learned-coincidence/MonotoneOneSidedRecognition.lean` of
#177, **cited by its commit `c45c0f716164c4bc7d2371f65676b8ab77f767a2`** (merged into `main`). Its premise
`CascadeCalibrationOneSided` keeps the symmetric `CalibratedAdditiveRead` for every read of layer 1, for the teaching
reads of layer 2 and for the test reads of layer 2 that contain no selected line. For the test reads of layer 2
predicted to fire (`FiringMaskRead`), it requires three things: the dated threshold decoder; a measured score of the
test mask never below the score of any submask that reaches the threshold; and, for each trained line, a singleton
score at least its guarded line score minus the test budget. [C4 §What is tested]

The campaign has two families of claims, **each with its own verdict, fixed here**: the learned function (a
noise-free primary claim and per-output claims under noise), and the per-port claims N-own and N-word under noise, on
`R = 3` noisy runs per instance. A failure in one family changes no verdict of the other. [C4 §What is tested] The
claims under noise hold for the injected noise model only (section 6). [D5-3]

## 2. Decisions this file applies

**Carried from campaign 4** ([`DECISIONS.md`][decisions], #172, commit `49684af`; [C4 §Decisions]):

1. Read-only tests by the testbench gate (`idis` off), every test read checked for writes in each run.
2. Layer-1 pulse amplitude **0.49**, fixed from the nominal cell; layer 2 at amplitude 1.
3. A calibration covering every stage up to the maximal write count, with the geometric gain path, and a
   calibration and validation split fixed here.
4. The saturated pair of the OR cell under the one-sided premise of #177.
5. Per-output claims under noise need room on their training reads as well as on their test reads, under `K = 3`,
   with the noise constants **`b = 0.111` mV between runs, `w = 0.094` mV within a run, `d = 0.009` mV per dose**.
6. Size: one run without noise and `R = 3` noisy runs per measured instance; up to 8 h of expected compute with the
   measured cost model ([`BUDGET_DECISION.md`][budget], commit `db4638b`; [`COST_MODEL_DECISION.md`][costdec],
   commit `2ffe04d`); two machines `a` and `b`; the launch kit unchanged; every stage's manifest within the kit's
   aggregate cap of 14 400 s over both machines.
7. Controls: the untrained network, the skewed coincidence, the nominal predictor.

**The owner's decisions for campaign 5 (2026-11-17):**

- **D5-1.** The preregistration is prepared first.
- **D5-2.** The same test as campaign 4: the learned AND-OR circuit, the same theorem and the same kernel gate.
- **D5-3.** Noise: the injected model only, with the constants of decision 5. No dependence on any other study. The
  device model is not validated ([`REPORT_A2.md`][noise-report], commit `fd25955`) and is not used.
- **D5-4.** Time limits: 2 times the cost model, fixed in advance, with no ratio taken from the rehearsal.
- **D5-5.** The number of instances follows the usual rule, within an 8 h budget of expected compute, with these
  limits.
- **D5-6.** The rehearsal runs in the real conditions of the campaign: 2 or 3 mismatched development instances (not
  campaign seeds), four runs at a time, every kind of run of every stage. A preregistered rule: if any rehearsal run
  uses more than 0.75 of its limit, nothing is launched until an amendment.
- **D5-7.** One `PREDICTION.md`, which folds in campaign 4's `PREDICTION.md`, its amendments 1 to 11 and the lessons,
  with no amendment planned.
- **D5-8.** The code is campaign 4's frozen implementation (`093995b`, on `research/learned-dnf-circuit-campaign-4-wip`),
  adapted only where the rules change (limits, one noise model, new seeds and folders, and what this file requires
  beyond campaign 4's rules), then frozen and rehearsed again.
- **D5-9.** New sessions run campaign 5. Campaign 4's sessions are archived.

## 3. What was run before this file

- Phase 0 of #172, on the nominal cell only (model section `tt`, no mismatch, no seed). The theory of #168 to #171,
  #177 and #178. Campaigns 1 to 3 (seeds 7101 to 7103, 7201 to 7206, 7301 to 7306, 7401 to 7412). [C4 §What was run]
- Campaign 4: its rehearsal on the nominal cell, and its stage M on seeds 7501 to 7512, of which 11 calibration decks
  completed and 13 reached their limit. **No output of any campaign-4 run was read** in writing this file. Only the
  statuses and wall times in its report and its amendment 11 are cited. [C4 report; C4-A11]
- **No seed of 7601 and above has ever been simulated.** The repository was searched for mismatch seeds 7601 to 7699
  (section 14, item 5). Seeds 7501 to 7512 are spent and are never used again.
- **The pre-run of the gate cases and of the sizing** (2026-11-17), asked for by the coordinator's review of this
  file's first draft and run before this file was pushed. It used no campaign data and simulated nothing.
  - **What ran.** Campaign 4's frozen `c4.py`, `predicted.py`, `gate4.py`, `plan.py` and `cases.py` (copied unchanged
    from `093995b`), with two new scripts. `cases5.py` builds the cases of section 7.4. `size5.py` runs campaign 4's
    sizing with the limits of section 10.4 and the seeds from 7601. `prerun.sh` drives both. All of it sits in
    `drafts/prerun/` of `research/learned-dnf-circuit-campaign-5-wip`, committed at
    `39747d70c4d2c07d5980de375b6f5ca234cba4cc` before it ran. SHA-256:
    `cases5.py` `62ad77f2f9f8e13180800486e93828619040907cb8aae6436ba3e556729f6815`,
    `size5.py` `e8f85666380933589ac6dcdb996ad83232de6dca35539cdb1f75b40bad640b51`,
    `prerun.sh` `7f7ab504bb7d5b1a8ca3660402ba52daa9054d8594bbef48abc88bfdb23ed7f5`.
  - **Input and toolchain.** The only input was `CALIBRATION.json` of #172 (commit `49684af`). The toolchain was the
    pinned one of section 10.2: the kit's `identity` passing on all seven pins, Lean 4.35.0, and OpenBLAS's SkylakeX
    kernel on an AVX-512 Xeon.
  - **Outputs.** In `drafts/prerun/out/`, committed at `bf8be75766ba5bd71cef91880afd74af5ef63cdc`, with their
    SHA-256 in its `SHA256SUMS`:
    `CASES.json` `ef0f4c9f0ba5b82441a2939e316736d653c616f78c89290803d9b2e51b08947c`,
    `Gate5Cases.lean` `141f2070e94ac1a0635bf8dc170c8e64c85dcdfa3be1ffa1f99b97d9f98bbb4c`,
    `Gate5CasesTargets.lean` `e099f107a163a9b545e256f6e5a9626816a5393784c5f3b6661ff1a493ffe83d`,
    `python.log` `21e44f1b4301dfbfdfb1190fad7dbf27fb6065e4cac75b9cb78bc787bcf344cf`,
    `SIZE.json` `2bfac65c22d1df8fe6c00d2a772047ca5d8c82b14a9f28d6f408fce87c0e70a8`.
  - **What was seen.** Every case gave the verdict of section 7.4, failing on exactly the conditions written there.
    The two Lean files compiled, and each of their 33 and 85 theorems depends on a subset of `propext`,
    `Classical.choice` and `Quot.sound`. P1′'s interval had the eligible scores 98 550 to 98 601. P2′'s interval
    had the eligible scores 102 339 and 102 341 to 102 410: the set is not contiguous, and 102 340 is not eligible.
    Under `beta_3`, every case was "no". The sizing gave `I = 12` and 28 788.89 s (section 10.5). Section 7.4 was
    written from the first draft's rules, and only the failing conditions and the values of P1′ and P2′ were filled
    in from what the pre-run printed. No rule was changed after it.
- **The second pre-run** (2026-11-17), asked for by the coordinator's review of the second draft. It used no campaign
  data and simulated nothing.
  - **What ran.** `diag5.py` takes P0 with a's pair score at stage 4 set to 102 338 to 102 342, and reports for each
    the exact layer-1 fit before rounding, the budgets, the mirror's failing conditions, and the Lean gate and
    per-checker targets. `budget5.py` passes the rehearsal's run lists (section 11.2) to the kit's own `check_budget`.
    `prerun2.sh` drives both. They are in `drafts/prerun/`, committed before they ran at
    `71ee48c27ffe923d25c30a490038378cf4c584d1`. `diag5.py` was fixed at
    `cf9521ad539222e16a1dd8fe31cb321aeba14d7e` (SHA-256
    `5b2d92f93d94303d2814329fd30e40fe56ac7de1f85ccb1846bd47e4da2aa654`), after a first attempt whose targets file
    did not compile: my cut of the placeholder P4 theorems left two `set_option … in` lines before `end`. That
    attempt's Python output was the same, and its log is kept in `out2/failed-first-attempt/`.
    `budget5.py` has SHA-256 `5501b70001f957fccc6bdc2114130843a90513590d1a6153564322e97608a93d` and `prerun2.sh`
    `ffacce280a8e507cb6efc0571f7438a74f2e3854f42c19ee565c945a171b3ea6`.
  - **Outputs.** In `drafts/prerun/out2/`, committed at `21e7adbba790e6b3f77ba6518e30b33140cad299`:
    `DIAG.json` `4f14328babefd79e6be57ff233a5850b1a45ede3d552d18eb153bb937ca9e59c`,
    `Diag5.lean` `5fe9a476e5e3fe1b38c32157b28e2a1b93c95bb83618a02e09838e4c26c85b78`,
    `Diag5Targets.lean` `9d1b8a3abb3cc63808db44543e07f7c5ceb3c9990004adeeb42ce13253aecbe7`,
    `BUDGET.json` `c6def649086039b3a3f2cc36ba309efdc386c429aff33f38ce942032f8917935`.
  - **What was seen.** The cause of the gap at 102 340 (section 7.4): a tie of a's port-1 gain rounded to even.
    Both Lean files compiled. Every rehearsal stage of section 11.2 was accepted by `check_budget`, with the bounds
    given there. These results filled in section 7.4's sentence on the gap and section 11.2's figures. No rule was
    changed after them.
- **A defect of campaign 4's frozen code, and the third pre-run** (2026-11-17).
  - **The defect**, found by the coordinator's review of the third draft from `DIAG.json`. In `predicted.py` at
    `093995b`, `guarded()` built its rows as `[0.0] * len(names)`, and `solve()` multiplied `F(r[i]) * r[j]`. In
    Python a `Fraction` times a float is a float, so the normal equations, and the guarded tuple, were computed in
    binary floats. C4-A3 §2 required exact rationals. Campaign 4 never computed a prediction, so no campaign-4
    result depends on this.
  - **The audit** of `predicted.py`, `cases.py`, `gate4.py` and `cases5.py`, looking for every float that reaches an
    integer, found no other:
    - the scores (`zint`), the dates and latencies (`q`) and the doses (`exact`, from `Decimal`) are Fractions;
    - the timing constants are Fractions, and the slot length is an int;
    - the budgets use `math.ceil` of a Fraction, which is exact, and `ceil_sum_sqrt`'s float is only a starting
      point that an exact predicate corrects;
    - the cases and the mirror read every number through `Fraction` or `Decimal`;
    - the floats left are the geometric fit and M5, which decide nothing.
  - **The fix**, as adaptation under D5-8, in `drafts/prerun/predicted5.py` (SHA-256
    `b0e2ae8ca6b5aa5e73512028b2b8a23f0a563c0664771fc59382abe9f698967a`), with its patch against `093995b`'s
    `predicted.py` (`predicted5.patch`, `d4e706975c29c65b4679edcca5ba6eef4f2d6e8ed319c85f790cbf41c3b28a54`):
    - the rows are integer;
    - both factors of every product are converted;
    - a float in a row or in the right-hand side is refused;
    - a solution that is not all `Fraction` is refused.
    It is the rule of section 4.2.
  - **What ran.** `prerun3.sh` (`01deb30b7a4a3e60928f4bb06eed6b046c10babc01167aa5316e39b510600122`) runs everything
    of the first two pre-runs again, with `predicted5.py` in place of `predicted.py`, and checks that a float in a row
    is refused. `diag5.py`'s rows were made integer too
    (`908b9ce21dd08029806c082253da009da09857ad4f1dc7da6b7f0ae248686b57`). All of it was committed before it ran, at
    `67acd3c859784440d0ea9ffa7f999fb355c64efb`. The outputs are in `drafts/prerun/out3/`, committed at
    `80d292454e1a23c23bb46942eff70ec5ffed926b`.
  - **What was seen.** A row holding a float was refused.
    - **Nothing changed.** `CASES.json`, `python.log`, `Gate5Cases.lean`, `Gate5CasesTargets.lean`, `SIZE.json` and
      `BUDGET.json` are byte-identical to the first two pre-runs. So are the Lean files of the diagnostic and every
      verdict, budget and failing condition of `DIAG.json`, whose fit values are now printed as fractions. This
      covers every verdict, failing condition, Lean result, `s1*` = 98 601, `s2*` = 102 339, the gap at 102 340, `I`
      and the stage bounds.
    - **The tie at 102 340 is exact.** a's port-1 gain there is 77 315/2. The neighbours are not ties: 1 082 407/28
      at 102 338, 2 164 817/56 at 102 339, 2 164 823/56 at 102 341 and 1 082 413/28 at 102 342.

## 4. Definitions

**Time unit.** 20 us, the length of a pulse. [C4 §Definitions]

**Instance.** One deck with three cells `a`, `b`, `c`: `net.deck` of `../network-circuit/net.py` with the model
section `tt_mm`, 27 C, the junction areas of stage J, and the simulator command `setseed` with the seed of the
instance. [C4 §Definitions] **Campaign seeds: 7601 to 7600 + `I`** (`I` by section 10.5), the lower half (rounded up)
on machine `a` and the rest on machine `b`. Each instance is measured and run on its own machine. [D5 seeds; C4
§Definitions] **Development seeds: 7691, 7692 and 7693**, for the rehearsal only (section 11). They never enter a
claim. [new; D5-6]

**Ports and lines.** Input A is port 1 of `a`, B port 2 of `a`, C port 1 of `b`, D port 2 of `b`, all at amplitude
0.49. Line `a` is port 1 of `c` and line `b` is port 2 of `c`, both at amplitude 1. A **mask** of a cell is the set of
its ports pulsed in one read. [C4 §Definitions]

**The gate.** Before a slot, with the cell at rest, 3 units before the slot, the dose source of every port that may
not write in that slot is set to zero (`alter i.x<cell>.x<port>.idis dc = 0`). It is restored to 8.2 nA for the ports
that may write. A **gated read** is a read of a cell whose ports are all gated. [C4 §Definitions]

**FIRE**: the protection latch of the cell rises through 0.9 V within one unit and 2 us after the start of the read
(the **decision window**; for `c` in a routed slot, its deadline, section 5). **Write**: the write signal of the port
rises through 0.9 V during the cycle of the pulse. **Write'**: a write that stays above 0.9 V for at least 1 us.
[C4 §Definitions]

**Word** of a port of `a` or `b` in training, or of a line of `c` in teaching: one letter per read of that port. The
letter is `s` for no FIRE and exactly one write on that port, `F` for one FIRE and no write, and any other read has its
own letter. **Output** of a cell on a test pattern: whether it fires in the decision window of its test read.
[C4 §Definitions]

**Score.** The score `Z` of a read is the peak, over the read, of the main charge `q` of the cell (0.1 at rest, 1 at
the FIRE level). It is given by the matched guard-disabled probe of the calibration (the same deck with `vfire` at
0 V). Guarded integer units: per cell, `Z` times 100 000, so the threshold is **`theta = 100 000`**. [C4 §Definitions]

### 4.1 Measures, each cell alone in its slot

Each instance has two calibration decks with the same calendar: **guard on** (FIRE bits and latencies) and **guard
off** (scores), on the deck of the three cells. At each dose stage `k = 0, ..., 7`, under the gate, reads are 22 units
apart: the empty read; port 1 alone; port 2 alone; both ports at one date; and, on `c`, also both lines with the
second 0.3 unit late. Cells `a` and `b` run at amplitude 0.49, `c` at amplitude 1. Then one clock-only dose is given
on both ports of each cell, with writes enabled: the next stage. Every emission of a calibration read is recorded over
the whole physical slot of 22 units. [C4 §Measures; C4-A1 §1]

An instance is **measured** when three conditions hold: both decks count (section 9), the guard-on FIRE bit of every
read equals `Z >= 1` of the guard-off read of the same stage and mask, and every stage has its reads. Otherwise it is
**not measured**: it has no prediction, gets no network run and enters no claim. A deck that reaches its time limit
does not count. [C4 §Measures; C4-A11 §3] **If no instance is measured**, there is no `PREDICTED.json`, no kernel
gate on a prediction and no stage Q, N1, N2 or N3, and every claim is "not established". [C4-A11 §3]

### 4.2 Needs, the gain path and the budgets

**Need.** For `a` and `b`: the least stage whose pair read fires (guard on). For each line of `c`: the least stage
whose single read of that line fires. A cell or line with no firing stage up to 7 has no need. [C4 §Needs]

**Write budget.** `Q = need + 2` per layer (the largest need of the layer, plus 2), and `Q <= 7` is required. Each
layer is trained for `Q + 1` presentations. [C4 §Needs]

**An instance without a need.** A measured instance with a cell or line that does not fire up to stage 7 runs **the
need-7 calendar of that layer** (a missing need counts as 7 in `dnf.calendar`). Such an instance is **not eligible**,
has no predicted words, gets no guarded tuple and no Lean check, and enters **M2 only**. "Every measured instance" in
the kernel gate means every measured instance with all its needs. [C4-A1 §5]

**Calibration and validation split.** For each cell, the geometric gain path `Z(S, k) = h + sum over j in S of
g_j r_j^k` is fitted (least squares, `h` on a grid) on the singles and aligned pairs of the even stages 0, 2, 4, 6:
this is the **calibration**. The odd stages 1, 3, 5, 7 are the **validation**, and their residuals are reported (M5).
For `c` only the single lines are fitted. Its pairs enter the one-sided premise, not the additive fit. [C4 §Needs]

**Guarded tuple.** Per cell, the guarded tuple is `help`, `initialGain` per port and the layer's common `dose`, in
integer units, with the threshold `theta`. It is fitted by least squares on stages 0 to `Q` on **exactly the reads its
residual bound covers**: for `a` and `b`, the empty read, the singles and the aligned pairs; for `c`, the empty read
and the single lines. It is computed as **the exact rational solution of the normal equations** on the integer
scores, then rounded to the nearest unit, ties to even. [C4 §Needs; C4-A1 §7; C4-A3 §2] **The frozen code enforces
it.** Every entry of the fit's rows and right-hand side must be an `int` or a `Fraction`, and a float is refused.
Both factors of every product are converted to `Fraction`. Every entry of the solution must be a `Fraction` before
rounding. CI checks on every push that a row holding a float is refused. Campaign 4's frozen code did not meet this
rule (section 3, the third pre-run). [new; coordinator's review 3, B3]

**Residual bound** `epsilon` of a cell: the largest `|Z - G|` over the reads its fit covers (with the empty read of
each cell), stages 0 to `Q`. `G` is the score of the guarded tuple. [C4 §Needs; C4-A1 §4]

**Rail** = **1 000 000** (10 times `theta`) in both layers. The Python requires every guarded gain to be below the
rail and reports the largest gain-to-rail ratio. [C4-A1 §2]

**Per-read budgets.** The noise-free budget is `beta_0 = epsilon + 0.030 mV x s`, where `s` is the sum over the
active ports of the read of the measured sensitivity (the score step of one dose divided by the measured dose in mV).
The noisy budget, at `K = 3`, is `beta_3 = epsilon + 3 x sigma`, with `sigma = s x sqrt(w^2 + b^2 + n x d^2)` mV and
`n` the writes of the port at that read. For a read of two ports, the two terms are added linearly. The constants are
those of decision 5 and nothing else: `b = 0.111`, `w = 0.094`, `d = 0.009` mV. [C4 §Needs; D5-3; C4-A7 §2]

**Exact arithmetic for every integer.** Every measure is converted exactly to a rational: a float at its exact
binary value, and a decimal read from a file at its exact decimal value. JSON is read with decimals parsed as
`Decimal` and never as binary floats. `epsilon`, the sensitivities, the budgets, the integer scores and the dates are
computed in rationals. Rounding to the nearest uses ties to even. Noise terms are rounded up exactly: for `beta_0`,
the least integer at least `0.030 mV x s`; for `beta_3`, the least integer `m >= 0` with `m >= 3 sigma`. For one
port this means `m^2 >= 9 s^2 (w^2 + b^2 + n d^2)`. For two ports, with `X = x^2` and `Y = y^2` the rational squares
of the two terms, it means `m^2 >= X`, `m^2 + X - Y >= 0` and `(m^2 + X - Y)^2 >= 4 m^2 X`. Floats remain only where
nothing becomes an integer: the geometric fit and its validation residuals. [C4-A3 §2; L: JSON read as `Decimal`]

**Budgets per cell, by Lean field.** The kernel holds one `trainingError` and one `testingError` per cell. Each is
**the largest per-read budget over the reads that the kernel checks with that field**, for `beta_0` and `beta_3`
alike. For `a` and `b`, `trainingError` covers its `firstTrain` reads and `testingError` its `teach` and `firstTest`
reads. For `c`, `trainingError` covers its `secondTrain` reads (both lines) and `testingError` its `secondTest` reads.
These per-cell numbers are the only budgets the Python uses: for eligibility, room at `K = 3`, own room and room up
to a learning port. [C4-A1 §3]

**Room.** A read predicted silent has room under `beta` when `G + beta < theta`. A read predicted to fire has room
when `G - beta >= theta`. Let `n_1` and `n_2` be the predicted writes of lines `a` and `b`, and `Z_j` the guard-off
score of line `j` alone at stage `n_j`. A test read of line `j` alone has room when `Z_j - beta >= theta`. The test
read of both lines has room when each line alone has room and the guard-off pair at stage `min(n_1, n_2)` is at least
`max(Z_1, Z_2) + beta`; the pair here is the lower of the aligned and 0.3-late pairs. The silent test read of `c` (the
empty mask) keeps the symmetric read, at stage `max(n_1, n_2)`. [C4 §Needs; C4 §The kernel gate]

**Declared assumption on `c`.** Each line alone is taken at its own stage `n_j`, measured with the other line at the
same stage `n_j`. It is assumed that the stored voltage of the other, inactive line does not change the score of a
line alone by more than the residual bound. M8 reports this assumption against the runs. [C4 §Needs]

**Relevant reads of an output.** For `a` (`b`): its training reads (the pair at stages 0 to `need - 1`, silent; at
`need`, FIRE) and its test reads at the trained stage `need` (the empty read and each single read silent; the pair
FIRE). For `c`: its teaching reads (each line alone, silent at stages 0 to `need_line - 1` and FIRE at `need_line`)
and its test reads at the trained stages (empty silent; each line alone and both lines FIRE). [C4 §Needs]

An instance is **eligible** when it is measured, has all its needs, has `Q <= 7` in each layer and every guarded gain
below the rail, and every relevant read of its three outputs has room under `beta_0`. An output has **room at
`K = 3`** when every relevant read of it has room under `beta_3`. [C4 §Needs; C4-A1 §2, §5]

**Learning ports.** Six per instance: ports 1 and 2 of `a` and of `b` (trained jointly, as a pair) and the two lines
of `c` (each taught alone). The **own reads** of a learning port of `a` (`b`) are the pair reads of its cell at stages
0 to `need`; for a line of `c`, its single reads at stages 0 to `need_line`. A port has **own room** under a budget
when every own read has room. **Room up to** a learning port has two cases. For a port of `a` or `b` it is own room.
For line `a` (`b`) of `c` it is three things together: own room, own room of both ports of `a` (`b`), and room of the
trained pair read of `a` (`b`) at stage `need`. [C4 §Needs]

**Control instance.** Among the eligible instances, the one whose layer-1 pair at stage 0 has the highest score, the
lowest seed in case of a tie. If no instance is eligible, it is the lowest measured seed. [C4 §Definitions; new: the
case of no eligible instance, which campaign 4 left open]

## 5. The calendar, routing and timing

`calendar` of [`research/learned-dnf-circuit/dnf.py`][dnf] (#172, commit `49684af`), with the needs of the instance:
one slot every **22 units**, with gates set 3 units before each slot. [C4 §The calendar]

1. **Layer 1**, `Q_1 + 1` rounds: A, B, C, D at one date; `a` and `b` write; nothing is routed.
2. **Layer 2**, `Q_2 + 1` rounds of two slots: AB in the first, CD in the second; `a` and `b` gated; `c` writes;
   routed.
3. **Tests**, 16 slots: each pattern of {A, B, C, D}, its inputs at one date; every cell gated; routed.
4. **Skew control**, 2 slots (in the run without noise only): AB with B 2 units late, and CD with D 2 units late;
   every cell gated; routed.

**Routing.** A FIRE of `a` (`b`) rising within the decision window of a routed slot sends one pulse of amplitude 1 to
port 1 (port 2) of `c`, **1.5 units after the FIRE**. An upstream silence sends nothing. The read of `c` in a routed
slot starts at its first arrival. The skew bound is **1.1 units** and the deadline is **2.2 units** after the first
arrival. An output of `c` is a FIRE rising after its last arrival and before its deadline. Two pulses of a cell are at
least 18.9 units apart by construction. [C4 §The calendar]

**Timing in the kernel.** `firstTiming` (`left`) is `⟨1/50, 11/10, 22⟩`. `secondTiming` (`right`) is
`⟨11/10, 11/5, 19⟩`: the read of `c` starts at most about 2.6 units into its slot, and 22 − 2.6 ≈ 19.4. The Python's
separation check uses 19 as well. A late FIRE cannot hide in the shorter window, because every emission of `c` is
recorded over the whole physical slot. [C4 §The kernel gate; C4-A1 §1]

**Run positions** (the index `k` of a run in its instance's list): calibration guard on (0), calibration guard off
(1), run without noise (2), N1 (3), N2 (4), N3 (5), the untrained control run (6). Under the injected model they
place nothing in time. They are recorded for the order of the runs only. [C4 §Run positions; new: their role under
the injected model only]

**The untrained control run**: the 16 test slots only, on the preset state, with every cell gated. [C4 §Definitions]

## 6. Noise: the injected model only

**The model.** Every noisy run is under the **injected model** of [`research/circuit/noise.py`](https://github.com/HevisNico/kernel-R/blob/8bcd3d744f101378c308a0af9da80631dded715f/research/circuit/noise.py),
used in campaigns 1 to 3. It consists of `trnoise` sources that the deck adds at the input of each block. It is not
the device noise of the transistor models: ngspice 42 adds no device noise to a transient. There is no noise-model
extraction, no E stage, no `filesource` source, no samples file, and no `xtrtol` setting. The rules of V2, V2b and
the isolation check do not apply. The claims under noise hold for this model only. [D5-3; C4 §Noise model; C4-A7 §2]

**The implementation keeps one noise model.** The frozen code accepts only the injected model. The runner refuses a
run that asks for any other model, before any simulation, which RG tests (section 11.2). Campaign 4's
device-model code (`noise/`, the extraction runs, the samples generator) is removed from the frozen implementation
only where it is a whole file, together with its call sites. Where removing it would touch a function that other
code uses, the code is kept and the runner's refusal is the barrier. Every file removed or changed against
`093995b` is listed at the freeze. No check of the rehearsal concerns the device model. [D5-8; L: every check of
the rehearsal tied to the model it concerns, C4-A9; coordinator's review 1, choice 7]

**Noise seed.** The noisy run of round `n` (1, 2, 3) of the instance of seed `S` has the noise seed **`10 x S + n`**,
written into `PREDICTED.json` by the frozen code: 76011 to 76013 for seed 7601, up to `10 x (7600 + I) + 3`. The
development seeds have 76911 to 76933 (rehearsal only). The noise seed is applied as the **imposed process number**
of the simulator process (`noise_id` of `net.Session`, the `fakepid` shim of `research/circuit/repetition`), set by
the frozen runner on its simulator process only. The launcher's own environment is unchanged. [C4 §Noise seed] The
noisy run of the chain test, on the nominal cell, has the noise seed **90 961** on both machines (section 11.3).
[new]
These numbers were never used to fix the noise of any run. The numbers fixed elsewhere lie in 1 to 707, 201 to 9 920,
706 002 to 706 082, 900 000 to 900 002, 75 011 to 75 123 (campaign 4, never run: no noisy run took place) and 90 951
to 90 953 (campaign 4's rehearsal, nominal cell). Campaign 5 fixes 76 011 to 76 123 (at `I = 12`), 76 911 to 76 933
and 90 961. A process number chosen by the system in an earlier run may have taken any value; such a draw was not
fixed and is not a use of the number. [C4 §Noise seed; new: the ranges of campaigns 4 and 5 added]

**Every noisy run is reproducible from its seed.** The same deck, instance seed and noise seed give the same run.
Between the records of two such runs, only these fields may differ: `id`; `wall_s`; `peak_rss_MB`; `files.trace.raw`,
whose `Date:` line is the start time; `files.result.json`, which holds `wall_s`; and `files.session.log`, whose
` Reference value : ` progress lines depend on wall-clock timing. Every other field must be equal. The three files are
compared apart: `trace.raw` byte for byte without its `Date:` line, `result.json` equal as data without `wall_s`, and
`session.log` line for line without the ` Reference value : ` lines. [C4 §Noise seed; C4-A6 §2–3; L: what two runs of
one seed may differ in] The same list applies to two runs of one calibration deck or one run without noise.
**Across two machines** the same comparison is made in the rehearsal and is reported, not required (section 11.5):
the two machines may differ in CPU. [new]

## 7. The kernel gate

A gate on the launch of the network runs, **not a claim**. [C4 §The kernel gate]

### 7.1 The predicted observation

The predicted observation of a measured instance with all its needs is the `Observations` of #177, built by the
frozen code from `PREDICTED.json`. Times are in time units as rationals, with latencies rounded to 0.0001 unit, ties
to even. Scores are in the integer units of the guarded tuple. [C4 §The kernel gate; C4-A3 §2]

- **Reads and dates**: one `ReadObservation` per slot of the calendar and per cell (`firstTrain`, `teach`,
  `secondTrain`, `firstTest`, `secondTest`). The start of a read of `a` or `b` is the date of its slot, and the
  arrival of each active input is that date. The arrival of a line on `c` is the predicted emission of its upstream
  cell plus `delay = 3/2`. The start of a read of `c` is its first arrival. A `secondTest` read with no arrival
  starts at its slot's date plus 3/2.
- **Inputs**: the input of a layer-1 read is every active external input of its slot, with a guarded gain of 0 on the
  inputs the cell has no port for. So `b`'s `teach` reads during line `a`'s lessons, and `a`'s `firstTest` reads on C
  and D, are physically empty reads, and their scores are those of the empty read at the trained stage. In
  `firstTrain`, a cell's input is its target.
- **Emissions**: one emission per predicted FIRE, at the start of the read plus the guard-on latency of that cell,
  mask and stage, and none for a predicted silence. For `c`'s test read on both lines, the emission is the first
  arrival plus the guard-on latency of `c`'s pair at stage `min(n_1, n_2)`: the aligned pair's latency when the two
  arrivals are at most 3/20 unit apart, and the 0.3-late pair's latency otherwise.
- **Scores**: the guard-off calibration score of that cell and mask at the stage of its predicted writes. On `c`,
  each line alone is taken at its own stage `n_j`; the pair at `min(n_1, n_2)`, taking the lower of its aligned and
  0.3-late scores; and the empty mask at `max(n_1, n_2)`. These also give the `scores` function of `FiringMaskRead`
  on every submask.

[C4 §The kernel gate; C4-A1 §4, §6; C4-A2 §4]

### 7.2 Every field of the kernel's objects, with its source

[L: a table "Lean field → source" for every field; C4-A1 §6]

| Lean field | Value | Source in this file |
|---|---|---|
| `first.target` | a: {A, B}; b: {C, D} | 4, Ports and lines |
| `first.tests` | `[]` (`Cascade.check` uses `checkConjunctions`, which does not read it) | 7.2 |
| `first.initialGain` | the guarded initial gain of each port; 0 on the inputs the cell has no port for | 4.2, Guarded tuple; 7.1, Inputs |
| `first.help` | the guarded help of each cell | 4.2, Guarded tuple |
| `first.threshold` | 100 000 | 4, Score |
| `first.trainingError`, `first.testingError` | per cell | 4.2, Budgets per cell |
| `first.dose` | the guarded common dose of layer 1 | 4.2, Guarded tuple |
| `first.maxWrites` | `Q1` | 4.2, Write budget |
| `first.rail` | 1 000 000 | 4.2, Rail |
| `second.lines` | c: both lines | 1 (the OR) |
| `second.alwaysFire` | false | 1 |
| `second.initialGain`, `second.help`, `second.dose` | the guarded tuple of c | 4.2, Guarded tuple |
| `second.threshold` | 100 000 | 4, Score |
| `second.trainingError`, `second.testingError` | per cell | 4.2, Budgets per cell |
| `second.maxWrites` | `Q2` | 4.2, Write budget |
| `second.rail` | 1 000 000 | 4.2, Rail |
| `delay` | 3/2 | 5, Routing |
| `heldOut` | `[]` (the recognition theorem does not use it) | 7.2 |
| `left` (`firstTiming`) | `⟨1/50, 11/10, 22⟩` | 5, Timing |
| `right` (`secondTiming`) | `⟨11/10, 11/5, 19⟩` | 5, Timing |
| `firstTrain r a` | slot `r` of layer 1; input the target of a; its pair score at stage `min(r, need)`; an emission at start + latency if `r ≥ need` | 7.1 |
| `teach n a` | lesson `n` (line a, then line b, each round); input the target of the lesson's line; the cell's pair or empty read at its trained stage | 7.1 |
| `secondTrain n` | c's read of lesson `n`: the arrival of the line at its upstream emission + 3/2; its single read at the line's writes so far | 7.1 |
| `firstTest x a` | test pattern `x`; input `x`; the cell's empty, single or pair read at its trained stage | 7.1 |
| `secondTest x c` | arrivals from `firstTest` + 3/2; start at the first arrival, or at slot + 3/2 if none | 7.1 |
| `scores x c` | empty mask: c's empty read at `max(n1, n2)`; one line: that line's single read at its writes; both: the lower of the aligned and 0.3-late pair at `min(n1, n2)` | 7.1 |

### 7.3 What Lean checks, and when the gate holds

For each measured instance with all its needs, and for each of the two budgets (`beta_0`, `beta_3`, as the errors
of the guarded tuple), the Lean file decides **each of the three checkers separately**: `checkCascadeValid` of the
guarded tuple, and `checkTrainingSeparation` and `checkCascadeCalibrationOneSided` on the predicted observation.
These are Boolean checkers proved sound and complete against their definitions at commit
`2e586aa20857c61814aa94ee3b1a227ad113e998` (#178, merged into `main`). The soundness theorems are
`cascade_valid_checker_sound`, `training_separation_checker_sound` and
`cascade_calibration_one_sided_checker_sound` in `MonotonePremiseSoundness.lean`. The completeness theorems are
`cascade_valid_checker_complete`, `training_separation_checker_complete` and
`cascade_calibration_one_sided_checker_complete` in `MonotonePremiseCompleteness.lean`. A `true` proves the property
and a `false` proves that it fails. [C4 §The kernel gate; C4-A2 §3]

**One set of numbers.** `PREDICTED.json` holds the predicted observation, the guarded tuples and the budgets as exact
numbers only: dates as rationals, and scores, residual bounds and budgets as integers. The Python computes room and
eligibility on exactly these numbers, in exact arithmetic. The Lean file is written from the same numbers.
[C4 §The kernel gate; C4-A3 §2]

**The Python's list.** The Python reports **the complete list of its failing conditions, read by read**. Each
condition is named with its read (layer, cell, slot, stage, mask) and its kind (guarded margin, residual, decoder,
route, separation, submask comparison), and is assigned to the Lean checker that holds it. Its verdict per checker
must equal Lean's. [C4-A2 §3]

**The gate holds** when three things are true: every check compiles; on every measured instance with all its needs,
each checker's verdict in Lean equals the Python's; and the conjunction under `beta_0` holds exactly when the Python
says the instance is eligible, and under `beta_3` exactly when the Python says all three outputs have room at
`K = 3`. If Lean fails or disagrees on any instance, **no network run is launched**. Per-output room at `K = 3` for a
single output is checked by the Python only. [C4 §The kernel gate; C4-A2 §3]

**What the gate gives.** When it holds, the predicted words and outputs of every eligible instance follow from the
measures by kernel check, with `two_layer_monotone_recognition_one_sided` (#177, `c45c0f7`). It checks the derivation
of the prediction from the measures. It says nothing of what the circuit does, which the network runs test.
[C4 §The kernel gate]

**The audit** (`check.sh`). No `sorry`, no `native_decide`, and no `run_cmd`, `addDecl`, `sorryAx` or
`warningAsError` in any campaign Lean file. Every theorem's `#print axioms` must be **a subset** of `propext`,
`Classical.choice` and `Quot.sound`, so a theorem on no axiom passes. `check.sh` takes several files. Its negative
cases run in CI from the start, and each must be refused **on the check of the axioms**, naming its axiom, and not on
the token filter: NegNative (`native_decide`'s auxiliary axiom, declared in an imported module), NegSorry (`sorryAx`)
and NegOwnAxiom (an axiom of our own in an imported module). These test files are written by hand and are never
written by the campaign code. [C4-A8 §2; L: the audit's negative cases from the start]

### 7.4 The gate on "no" cases

The cases use no campaign data. They are built from the nominal cell of phase 0 (`CALIBRATION.json` of #172, commit
`49684af`; need 4 on each pair and each line), with the conventions of campaign 4: Z rounded to the file's four
decimals in integer units; `c`'s 0.3-late pair, which phase 0 did not measure, equal to its aligned pair; and the dose
of a port at stage `k` equal to the difference of the stored voltages of stages `k` and `k + 1` (at stage 7, that of
stage 6). [C4 §The kernel gate; C4-A1 §8 item 5]

**No case is built on a symmetric cell.** In the nominal table `a` and `b` are the same cell, so their arrivals on
`c` coincide, and a case aimed at the decoder can pass for that reason alone (campaign 4's P4 did). So the **base
case P0** is the nominal table with **`b`'s guard-on latency increased by 1/10 unit on every read** (every stage and
mask), a constant of the case table and not a data value. The frozen prediction code recomputes everything from it.
Every other case is P0 plus one change. P1 to P3 are measure changes, after which the frozen code recomputes the fits,
residual bounds, guarded tuple, room and predicted observation. P4 to P6 are changes of the predicted observation.
[L: no case built on a symmetric cell; C4-A2 §1, §6 item 3]

**Each "no" case has its exact target and a control.** A "no" case must fail **for its target and only for it**, in
both the Python and Lean. Its control applies a change of the same kind to the same object that stops short of the
target condition, and must give "yes". [L: each "no" case with its exact target and a control; C4-A2 §2–3]

| Case | Change from P0 | `beta_0`: Lean false | `beta_0`: Lean true | The Python's failing conditions, and no other |
|---|---|---|---|---|
| P0 | none | none | all three | none |
| P1 | the score of a's pair read at stage 3 (its last silence) raised to `theta − 1` | `checkCascadeValid` | the other two | the guarded margin of a's early silence at stage 3, and nothing else |
| P1′ | the same score set to `s1*` = **98 601**, the largest integer in `[Z, theta − 1]` for which the frozen code gives the instance eligible | none | all three | none |
| P2 | the score of a's pair read at stage 4 (its first FIRE) lowered to `theta` | `checkCascadeValid` | the other two | four guarded margins, through the joint fit of layer 1: the early silences of a and of b at stage 3, a's stop (training) and a's positive test read at stage 4; no timing condition |
| P2′ | the same score set to `s2*` = **102 339**, the least integer in `[theta, Z]` for which the frozen code gives the instance eligible | none | all three | none |
| P3 | c's aligned pair at stage `min(n_1, n_2)` set to the score of line a alone minus 1 (the test pair's score is the lower of the aligned and 0.3-late pairs) | `checkCascadeCalibrationOneSided` | the other two | c's two submask comparisons (submasks a and b) on its test read ABCD |
| P3′ | c's aligned and 0.3-late pairs at stage `min(n_1, n_2)` both set to `max(Z_1, Z_2)` plus c's `testingError` under `beta_0` (102 017) | none | all three | none |
| P4 | the emission of c's test read on ABCD placed at the midpoint of its two arrivals (39 719/50 and 19 862/25) | `checkCascadeCalibrationOneSided` | the other two | `v ≤ t` for line b's arrival on c's test read on ABCD |
| P4′ | the same emission placed at its last arrival (19 862/25) | none | all three | none |
| P5 | the arrival of line a on c in test slot AB (the first slot where a fires) moved 1/10 unit later | `checkCascadeCalibrationOneSided` | the other two | the route of line a in test slot AB |
| P5′ | the emission of a in test slot AB and the arrival of line a on c moved together, 1/10 unit later | none | all three | none |
| P6 | the start of a's `firstTest` read in the first test slot (pattern `-`, the empty one) moved 1/100 unit earlier | `checkTrainingSeparation` | the other two | the separation of that read from the last lesson (lesson 13), from a's and from b's `teach` read |
| P6′ | the start of a's `firstTest` read in the second test slot (pattern A) moved 1/100 unit earlier | none | all three | none |

`Z` in P1′ and P2′ is that read's score in P0 (98 550 and 102 410). The case builder finds P1′ and P2′ by trying
every integer of their interval. The values in the table are those the pre-run found (section 3), and the frozen
code must reproduce them. The eligible scores of P2′'s interval are not contiguous: 102 340 is not eligible. At
102 340 the exact least-squares gain of a's port 1 is 77 315/2 = 38 657.5, an exact tie. Ties to even round it to 38 658, which raises
a's guarded pair score at stage 3 from 99 207 to 99 208. The training budget stays 792, so the room of that early
silence, `theta − (G + beta_0)`, is 0, and the strict `G + beta_0 < theta` fails. The mirror's only failing condition
is a's guarded margin (early silence) at stage 3. Lean gives `checkCascadeValid` false and the other two checkers
true. At 102 339 and at 102 341 the room is 1. This follows from the rules of section 4.2 (exact fit, ties to even, a
strict inequality) and is not a defect (second and third pre-runs, section 3). P2′ is the least eligible score, as
defined.
For P4, the Lean
file also decides, as propositions on c's test read on ABCD (start `s`, emission `t`): `∀ j v, arrival j = some v → v
≤ t` is **false**; `s ≤ t ∧ t ≤ s + deadline` is **true**; and every arrival lies in `[s, s + skew]` is **true**. Only
the first test slot can break the separation: `TrainingSeparation` orders every test read after every training slot
and lesson, but does not order the test slots among themselves. That is why P6 and P6′ differ only in the slot. The
1/100 unit is below the layer-1 skew bound of 1/50. [C4-A2 §3, §5; new: P0's asymmetry and the controls P1′, P2′,
P3′, P5′, P6′; P4′ redefined]

Under `beta_3`, on every case, the Python and Lean must give the same verdict per checker, with no fixed expected
value. In the pre-run every case was "no" under `beta_3`, as P0 is: no output of the nominal cell has room at
`K = 3`. So the cases try only the false path of the `beta_3` conjunction: Lean and the Python are shown to agree
on "no" there, never on "yes". The true path is tried only if a development instance has room at `K = 3`
(section 11.5). **In the rehearsal and in CI**, every case must give its expected verdict under `beta_0`, fail for its target
only in both, and agree under `beta_3`. Otherwise nothing is launched. [C4-A2 §3]

**The mirror mutations** of campaign 4 (`mirror_mutations.py`) are kept: each mutation of the Python mirror of a
checker must be detected by a disagreement with Lean. [C4 implementation at `093995b`; D5-8]

## 8. Predictions

**Primary claim, without noise.** For every eligible instance, in its run without noise: [C4 §Predictions]

- **L1, layer-1 stops.** The word of each port of `a` is `need_a` letters `s` then `Q_1 + 1 - need_a` letters `F`,
  and the same for `b`.
- **L2, layer-2 per-line counts.** The word of line `a` of `c` over its teaching slots is `need_c1` letters `s` then
  letters `F`, and the same for line `b`.
- **T, the outputs.** On each of the 16 test patterns, `a` fires exactly when A and B are both in it, `b` exactly
  when C and D are, and `c` exactly when `(A and B) or (C and D)`.

The primary claim is refuted by one letter of L1 or L2, or one output of T, that differs, on one eligible instance.
With no eligible instance it is **not established**. [C4 §Predictions; new: the case of no eligible instance stated]

**G, read-only, with its own verdict.** In every run without noise, across every gated read, no stored voltage moves
by more than 0.01 mV, and no write and no write' rises. In every noisy run, across every gated read, no write and no
write' rises. One gated read that fails refutes G. [C4 §Predictions]

**H, hypotheses, observed and reported, never refuting the primary claim.** Two pulses of a cell are never less than
16 units apart. No FIRE comes after the decision window in the cycle of a read. Every arrival on `c` is a FIRE of `a`
or `b` plus 1.5 units, within the skew bound, and an upstream silence sends nothing. A FIRE of `c` comes after its
last arrival and before its deadline. Every pulse is delivered and nothing is queued at the horizon. [C4 §Predictions]

**N-out, the learned function under noise, per output.** For every measured instance, every output that counts and
every one of its counted noisy runs, the output answers as predicted on every one of the 16 test patterns. An output
of `a` (`b`) counts when it has room at `K = 3`. An output of `c` counts only when `c`, `a` and `b` all have room at
`K = 3`. One pattern answered otherwise refutes the claim of that output. Each output (`a`, `b`, `c`) has its own
verdict, over its counted output-runs. A claim with no counted output-run is not established. [C4 §Predictions]

**Per-port claims at `K = 3`**, over every measured instance and each of its counted noisy runs: [C4 §Predictions]

- **N-own.** A learning port with own room under `beta_3`, in a noisy run in which it receives at least `need`
  pulses in its training (teaching) slots, has a word of exactly `need` letters `s` followed only by letters `F`.
  Port-runs with fewer than `need` pulses do not count, and their number is reported.
- **N-word.** A learning port with room up to it under `beta_3` reads exactly its zero-error word over its `Q + 1`
  training (teaching) slots.

Each is refuted by one port-run that fails it, and is not established without a port-run that counts. Words are read
with the write. The word' (with write') of every port-run is reported in M6, never in place of the word.

**The verdicts are separate**: the primary claim (L1, L2, T), G, N-out per output, N-own and N-word. None of them
changes another. [C4 §Predictions]

**Controls.** [C4 §Predictions]

- **U, the untrained network.** In the untrained control run, no output fires on any of the 16 patterns. On the
  nominal cell the pair at stage 0 is 0.12 of the FIRE level below threshold.
- **S, the skewed coincidence.** In the two skew slots, `a` and `b` stay silent. The predictor that ignores timing
  says FIRE. S can fail without touching the other claims.

**Declared comparisons, not claims**, as counts: [C4 §Predictions; C4-A5 §6]

- **M1**, for the outputs that do not count for N-out: the test patterns answered as predicted in their noisy runs.
  For the learning ports without own room, or with own room but no room up to them: the port-runs with the
  zero-error word.
- **M2**, for the run without noise of the measured instances that are not eligible: L1, L2 and T against their
  zero-error words and outputs.
- **M3**, the latencies of every FIRE and the arrival skews on `c`, against the decision window and the skew bound.
- **M4**, the **nominal predictor** (need 4 for each pair and each line, the outputs of the truth table): the letters
  and outputs where it differs from the measured predictor, and where it differs from the runs.
- **M5**, the residuals of the validation stages, against `epsilon`.
- **M6**, every write-signal crossing that is not a write', with its date in the cycle and its width; and, per
  port-run of the noisy runs, whether its word and its word' differ.
- **M7**, per instance and per learning port, the spread over its `R` noisy runs of the stored voltage at the end of
  training, against the model's `sigma`, and of the FIRE latency of its first `F`, reported alone (the model gives no
  latency spread).
- **M8**, the kernel checkers on the runs without noise of the eligible instances, under `beta_0`, after the one
  analysis. Dates come from the run's record. Scores: for the observed mask of a read, the run's peak of `q` in
  integer units, and for a read that fires, the larger of that peak before the FIRE crossing and `theta`; for every
  other submask, the calibration score of the predicted observation. **Stated in advance**, from campaign 4's smoke
  run on the nominal cell: the guard stops the charge at the FIRE, so the residual of every firing read, `c`'s
  anchors and the submask comparison of its pair are expected to fail. The simulator places each routed pulse on its
  0.02-unit grid (`net.snap`), so exact route equality is expected to fail on every routed read. M8 also reports the
  declared assumption on `c` for each eligible instance with `n_1 != n_2`. M8 refutes nothing, and each of its
  results is reported with these reasons beside it. **M8's file is checked by `check.sh` on both paths**: with no
  eligible instance (a theorem on no axiom) and with an eligible one. Both paths run in CI from the start. [C4-A5 §6;
  C4-A8 §2; L: both paths of M8 in CI]

## 9. Rules of the analysis

One analysis, at the end, frozen with the implementation. **No word, output or score of any network run is looked at
before the last stage has ended on both machines.** Between stages, only the launcher's status of each run (complete
or missing) is checked. [C4 §Rules of the analysis]

The analysis first checks that `PREDICTED.json` is exactly what the frozen prediction script gives from the evidence
of the measures, byte for byte, under the pinned interpreter and the SkylakeX kernel (section 10.2). If it is not,
every claim is "not established". [C4 §Rules of the analysis; C4-A8 §3]

**A run counts** when the launcher recorded it complete and its own record says that it reached its last date. Any
other run, a run stopped at its time limit included, is **missing**, never failed, and is never replaced or rerun.
There is no re-scoping: the eligible instances, the needs, the budgets, the room and the control instance are those
of `PREDICTED.json`. Failures are reported as they are. [C4 §Rules of the analysis; C4-A11 §1]

**Reporting.** This campaign is reported on its own, with its own verdicts. Nothing is pooled with campaigns 1 to 4.
[C4 §Rules of the analysis]

## 10. Execution

### 10.1 Sessions and machines

- **Executor.** Claude Code cloud sessions on behalf of the owner: the campaign director on machine `a` and a second
  session on machine `b`, two cloud containers whose inventories are recorded. [C4 §Execution; D5-9]
- **A session with a run in progress stays active.** It waits in the foreground, in loops of at most 10 minutes per
  wait, and never ends its turn before the run ends. [L: infrastructure]
- **Every long run is detached** (`setsid nohup … < /dev/null &`), never a session task, since session tasks stop at
  2 h. That it is alive outside the session is checked right after its start. [L: infrastructure; C4 report,
  rehearsal attempt 1]
- **`uptime -s` is recorded at the start and at the end of every stage on every machine**, and by a recorder every 5
  minutes during it. A restart during a stage makes the runs in progress missing. A restart between stages is
  reported, with the machine's inventory checked again before the next launch. [L: infrastructure; C4-A11 §1]
- **The inventory of each machine is written just before each stage's manifest, and the launch follows at once.** If
  anything but the boot time differs from the inventory of the previous stage (CPU model, processors, memory, kernel,
  system, the pinned environment), nothing is launched on that machine until an amendment. **M1's reference
  inventory on each machine is the one written for that machine's last rehearsal stage**, since the rehearsal's wall
  times hold only for that CPU. So if a container is replaced between the rehearsal and M1 by one with another CPU
  model or another processor count, nothing is launched on it until an amendment. [L: infrastructure; C4-A11 §1;
  coordinator's review 1, R7]
- **Packages are installed with `venv/bin/python -m pip`**, never by a script whose shebang would enter numpy's
  `RECORD` hash. [L: infrastructure; C4 report, machine `b`'s numpy]
- The remote of every clone is `https://github.com/HevisNico/kernel-R`, checked before every launch. [C4-A11 §1]

### 10.2 Environment and numerics

- **Environment, identical on both machines and checked by the launcher**: ngspice 42
  (`820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45`), PDK commit
  `1232782c1b9fab3aacda74d67ce7c92bf7da8105`, Python 3.12.3
  (`e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f`), numpy 2.3.5 (`RECORD`
  `064003bdb6f9f7bb06e46e07cc3398cbfdc3c114dfe55b89d239e564917be2fb`) in `/home/user/owner-prep/venv312`, Lean 4.35.0.
  **Four runs at a time on each machine.** [C4 §Execution; C4-A3 §3]
- **The interpreter is pinned and checked by every script** of the campaign code (prediction, cases, mutations, gate,
  rehearsal, manifests, analysis, collection), which refuses any other. [C4-A3 §3; L: numerics]
- **`OPENBLAS_CORETYPE=SkylakeX` on a CPU with `avx512f`** for anything that computes or compares floats, refused
  otherwise with a clear message. `PREDICTED.json` is computed on machine `a`. CI compares the generated JSON
  structurally on a runner without AVX-512: integers, strings, Booleans and nulls exactly; floats with
  `math.isclose(rel_tol=1e-9, abs_tol=1e-15)`, the floats deciding nothing. CI compares the Lean files byte for byte on
  every runner. The structural path is exercised on every runner by a Haswell-kernel file that must be accepted and a
  copy with one integer changed that must be refused. [C4-A8 §3; L: numerics]

### 10.3 Cost model

These are wall times **measured on the nominal cell**, on decks of three cells, four runs at a time, each scaled to
the calendar of a run by the ratio of `dnf.cost` for that calendar to `dnf.cost` for the need-4 calendar (the
owner's cost-model decision, [`COST_MODEL_DECISION.md`][costdec], commit `2ffe04d`). [C4 §Execution, Cost model]

| Run | Expected cost | Measured where, and under which conditions |
|---|---|---|
| calibration deck | **925 s** | 125.1 s for phase 0's one-cell deck, nominal cell, scaled to the three-cell deck by `dnf.cost` ([`COST_MEASURES.json`][costmeas], commit `3144c57`) |
| run without noise | **814 s** at need 4; **845.3149 s** with the skew slots (814 × 1.0384703, the ratio of `dnf.cost` for `dnf.calendar(4, 4, 4, 4, "skew")` to `dnf.cost` for `dnf.calendar(4, 4, 4, 4)`, `dnf.py` at main `8bcd3d7`) | nominal cell, need-4 calendar ([`COST_C4_need4.json`][cost4], commit `4d3b5a1`) |
| noisy run, injected model | **1 316 s** at need 4 | nominal cell, need-4 calendar, injected model (`COST_C4_need4.json`, commit `4d3b5a1`) |
| untrained control run | **369.2 s** | `COST_MEASURES.json`, commit `3144c57` |

**Expected compute**: for each stage and each machine, the sum of the expected costs of its runs divided by four
(four at a time), plus three quarters of its largest expected cost, summed over every stage and both machines.
Instances are costed at the need-4 calendar. [C4 §Execution]

### 10.4 Time limits

[D5-4] **The time limit of a run is twice its expected cost, rounded up to the next 10 s**:
`limit = 10 x ceil(2 x expected / 10)`. The expected cost is computed for the run's own calendar, from the needs of
`PREDICTED.json`. No ratio from the rehearsal or from any other run enters a limit. The kit's estimate of a run is its
expected cost rounded up to the next 10 s. The limits at need 4: **calibration deck 1 850 s**, run without noise with
the skew slots 1 700 s, noisy run 2 640 s, untrained control run 740 s. At need 7 in both layers: 2 130 s and
3 340 s. [D5-4; new: the rounding and the kit's estimate]

**The margins, against what they were measured under.** [L: review]

- **Calibration deck.** The limit is 1 850 s. Campaign 4's smoke runs on the nominal cell (outside the kit, four at a
  time) took 588 s guard on and 449 s guard off [C4-A5 §7]. At stage M of campaign 4 (mismatched cells, through the
  kit, four at a time), guard-on decks ran past 660 s, by an amount not recorded, and guard-off decks took 551 to
  595 s in 11 of 12 cases, one reaching 660 s [C4-A11 §1]. So the guard-on cost under the campaign's real conditions
  is **not known**: it is above 660 s. The limit is 2.8 times 660 s. The rehearsal's 0.75 rule (section 11.4)
  measures it before any launch.
- **Run without noise and untrained run.** Campaign 4's smoke runs, nominal cell: 672 s (need 4, with skew) and 142 s
  [C4-A5 §7], against limits of 1 700 s and 740 s. No mismatched run was ever made.
- **Noisy run.** Campaign 4's smoke run, nominal cell, injected model, beside four extraction runs: 1 120 s [C4-A5 §7],
  against 2 640 s. No mismatched noisy run was ever made.
- None of these figures was measured on a mismatched instance through the kit under the campaign's load, except
  campaign 4's stage M decks. That is what the rehearsal is for.

### 10.5 Number of instances, stages and caps

**The rule** [C4 §Execution, Budget; D5-5]: `I` is the largest instance count whose expected compute, with
`round(0.92 x I)` measured instances (campaign 3: 11 of 12) and one untrained control run, all at need 4, is at most
8 h, and **every stage of which, with the limits of section 10.4, fits the kit's bound**. The kit bounds each manifest
by the sum over both machines of `sum(caps) / 4 + max(caps)`, each cap being a run's time limit plus 10 s, at 14 400 s.
A stage that does not fit is split by seed (below).

**The result**, computed by the pre-run (section 3) with campaign 4's `plan.py` (`093995b`), these limits and seeds,
under the pinned interpreter: **`I = 12`**, seeds 7601 to 7612 (7601 to 7606 on `a`, 7607 to 7612 on `b`), 11
expected measured. The expected compute is **28 788.89 s = 7.9969 h** (13 instances would need 8.458 h), in six
stages:

| Stage | Runs | Limits | Cap (kit bound) | Expected per machine (a, b) |
|---|---|---|---|---|
| M1 | the 12 calibration decks of 7601–7603 (a) and 7607–7609 (b) | 1 850 s | 9 300 s | 2 081 s, 2 081 s |
| M2 | the 12 calibration decks of 7604–7606 (a) and 7610–7612 (b) | 1 850 s | 9 300 s | 2 081 s, 2 081 s |
| Q | the runs without noise (with skew) of the measured instances, and the untrained control run | 1 700 s, 740 s at need 4 | 8 310 s at need 4 | 1 994 s, 1 691 s |
| N1, N2, N3 | the noisy run of round 1, 2, 3 of every measured instance | 2 640 s at need 4 | 12 588 s at need 4 | 2 961 s, 2 632 s |

The 2× limits split stage M in two, so 12 instances fit within 11.1 s of the budget. That margin is far above the
precision of the arithmetic. **The frozen code must reproduce `I = 12` and 28 788.89 s** (to 0.01 s). This is checked
at the freeze and by CI on every push. A mismatch is a defect of the code, fixed before the freeze. It never changes
`I`. [coordinator's review 1, R2]

**Splitting a stage, a fixed rule.** Each machine's runs of a stage, in seed order, are cut into the fewest
consecutive parts such that every part, the `j`-th parts of both machines together, fits the kit's bound. This applies
to M (M1, M2, as computed above) and, with the needs of `PREDICTED.json`, to Q and to each N stage (named Q.1, Q.2,
…, N1.1, N1.2, …). At need 7 the noisy runs of six instances on one machine (limit 3 340 s) exceed the bound, so this
split can arise. The parts of N1 run before those of N2. The split is computed by the frozen code from
`PREDICTED.json` alone, and every manifest after M is pushed before the first launch of Q. Splitting adds no run and
removes none. The actual compute can then exceed the 8 h of the sizing, which is costed at need 4. [C4 §Execution,
Stages; new: the split of Q and N]

**The fixed sequence of stages.** M1, M2, Q (its parts), N1, N2, N3 (their parts), **whatever the results**: no
early stop, no added stage, no change of any manifest, limit, run or order between stages. A stage that is not
launched, or whose launch on a machine reaches its cap, is missing on that machine, never failed. [C4 §Execution]

### 10.6 Stage protocols and the launch kit

- **The launch kit** is `research/sky130-supervisor-closure/launchkit/launch.py`, unchanged, with one launch per
  machine and per stage. **A started run is never relaunched.** [C4 §Execution; method]
- **One protocol file per stage**, `research/learned-dnf-circuit-campaign-5/STAGE_<name>.md`, written by the frozen
  code and pushed alone before the stage's launch, since the kit claims a machine once per protocol file. It names
  the stage and its **governing protocol**, with that file's commit and SHA-256: `PREDICTION.md` for M1 and M2;
  `PREDICTED.json` for Q, N1, N2, N3 and their parts. The rehearsal's stages (section 11.2) are governed as follows:
  RC and RM by `PREDICTION.md`; RQ, RN and RMEM by the rehearsal's own `PREDICTED.json` of the development
  instances. RG is not a kit stage: its checks are direct calls to the frozen code, under `PREDICTION.md`. The frozen code maps **every stage name explicitly** to its
  governing protocol, from this closed list of names, and refuses an unknown name. It never infers the mapping from a
  first letter. [C4-A5 §1; C4-A8 §1; L: one protocol file per stage]
- **Safeguard (i).** At launch, the frozen runner checks that the governing protocol in the repository still has the
  SHA-256 written in its stage file, and refuses the run otherwise, before any simulation. [C4-A5 §1]
- **Safeguard (ii).** Each stage's source commit differs from the frozen implementation commit in no frozen file, byte
  for byte. Every other file in which it differs is in this **closed list**, all under
  `research/learned-dnf-circuit-campaign-5/`: the stage files and their run lists; the records written by the frozen
  code (`BEFORE_M.md`, `PREDICTED.json`, the Lean file of the kernel gate, `REHEARSAL.json`); the inventories; the
  manifests and attempt markers; the evidence of earlier stages and its collection records; any `AMENDMENT_*.md`; and
  `REPORT.md`. No file outside that folder differs. The frozen code checks this when it writes a stage's manifest, and
  refuses otherwise. **CI must be green on that exact commit.** [C4-A5 §1; C4-A6 §5; L: the closed list]
- **A `RUN_ATTEMPT_<name>.json` marker** is pushed before each launch. [method]
- **The seed guard.** The frozen runner accepts a campaign seed only from 7601 to 7600 + `I` and only inside a launch
  of the kit. It accepts a development seed (7691 to 7693) only inside a launch of the kit for a rehearsal stage (a
  stage name in the rehearsal's closed list), and the nominal cell (no seed) only for the rehearsal and CI. It refuses
  every other seed, 7501 to 7512 included, before any deck is written. [C4 §Noise-model extraction; C4-A5 §7; new:
  the development seeds]
- **The noise-model guard.** The frozen runner refuses a run that asks for any noise model but the injected one (or
  none), before any simulation. [D5-3; coordinator's review 1, R5]

### 10.7 Evidence

As in campaigns 2 to 4: the decks of every run, logs, records, fingerprints and SHA-256 lists on the campaign
branch; waveforms of 10 MB and more on `evidence/*` branches with no shared history; a file above 100 MiB in parts of
90 000 000 bytes listed in `PARTS.json`, with the SHA-256 of every part and of the whole. [C4 §Execution, Evidence;
L: tooling]

**Collection handles runs stopped at their limit.** A run stopped at its limit can leave symbolic links (campaign 4:
`evidence/pdk -> /home/user/campaign/pdk`). The kit's `collect` refuses them. So every stage is collected by the frozen
collector, built from campaign 4's `collect_with_links.py`. It copies every regular file byte for byte with its
SHA-256, records each link as text (its path and target) without following it, writes `COLLECTED.json`, and checks
that the evidence folder is unchanged before and after. It is part of the frozen implementation and is tested in the
rehearsal on a run stopped by a deliberately short limit (section 11.3). [C4-A11 §2; L: collection built in]

### 10.8 The record before stage M

`BEFORE_M.md`, written by the frozen code and pushed alone after the rehearsal's record and before the first launch of
M1, records **what the code really uses**: [C4 §The record before stage M; C4-A10; L: `BEFORE_M.md`]

1. the noise model: injected, by this file (no choice remains);
2. the noise constants `b`, `w`, `d` of decision 5;
3. the costs of section 10.3;
4. `I`, the seeds per machine, the expected compute, and the expected counts (measured, eligible, noisy runs);
5. the function that sets each time limit (section 10.4) and its values at need 4 and need 7; **the exact time limits
   and caps of M1 and M2**, which depend on no need and are those their manifests will hold; and the caps of Q and N1
   to N3 at need 4, marked as the figures the frozen code recomputes from `PREDICTED.json`;
6. the rehearsal's record (`REHEARSAL.json`), by its commit and SHA-256, and its verdict.

Nothing in it is chosen by hand. The rehearsal changes no rule. It can only stop the launch (sections 11.4 and 11.5).

## 11. The rehearsal

The frozen implementation is rehearsed **in the real conditions of the campaign** before any launch. [D5-6] It runs
through the launch kit, on the campaign's two machines, four runs at a time, after the freeze and with CI green on
the frozen commit. Its own limits are three times the expected cost (section 11.2). The campaign's limits judge it
(section 11.4).

### 11.1 What it is made of

- **The development instances**: seeds **7691, 7692, 7693**, model section `tt_mm`, the deck of the campaign. They are
  never simulated before the rehearsal and never enter a claim. [D5-6; new: their seeds and number]
- **The nominal cell** (section `tt`, no seed): the gate cases, the mutations, and the chain test. [C4 §The kernel
  gate]

### 11.2 The rehearsal's limits and stages

**The rehearsal's own limit of a run** is `min(10 x ceil(3 x expected / 10), 3 580 s)`. The kit's cap of a run is its
limit plus 10 s. A slow run is then measured rather than cut, up to the bound of the kit. [C4-A5 §5; coordinator's
reviews 1 and 2, R1 and B1]

**Why 3 580 s.** The kit refuses a manifest whose two machines' bounds sum above 14 400 s, each machine's bound being
`sum(caps) / 4 + max(caps)` (`launch.py`, `check_budget`). It also refuses a manifest without runs on both machines
(`read_manifest`). A stage with four runs on each machine can therefore have no cap above 3 600 s. The limits are:

- calibration deck 2 780 s;
- run without noise (with skew) 2 540 s at need 4 and 3 200 s at need 7;
- untrained control run 1 110 s;
- noisy run 3 580 s at need 4 and at need 7.

The cap measures a noisy run up to 2.72 times its expected cost at need 4, which is 1.36 times its campaign limit,
and up to 2.14 times at need 7, which is 1.07 times its campaign limit. The 0.75 thresholds of section 11.4 for those
runs, 1 980 s and 2 505 s, lie well inside. A noisy run that reaches its rehearsal limit has already failed the 0.75
rule. [coordinator's review 2, B1]

**Each rehearsal stage is one manifest over both machines, with the same runs on each** (four at a time on each
machine, the campaign's load), its own protocol file, run list and attempt marker. The figures below are the kit's
own `check_budget` on these run lists, computed by `budget5.py` in the second pre-run (section 3):

| Stage | Runs on each machine | Of the kind of | Bound per machine; both (kit) |
|---|---|---|---|
| RC | the chain test, section 11.3, on the nominal cell: the two calibration decks; a third calibration deck limited to 120 s; the run without noise at need 4 with skew; the untrained control run; one noisy run at need 4 (noise seed 90 961) | every kind, and a stopped run | 6 832.5 s; 13 665 s |
| RM | the 6 calibration decks of 7691 to 7693 | M1, M2 | 6 975 s; 13 950 s |
| RQ | the run without noise (with skew) of each development instance at its own needs (need 7 if it has none); **one run without noise of 7691 on `dnf.calendar(7, 7, 7, 7, "skew")`**; the untrained control run on the development control instance | Q, at both ends of its calendar | 6 205 s; 12 410 s (every instance at need 4) to 6 700 s; 13 400 s (at need 7) |
| RN | round 1 of 7691, 7692 and 7693; a second run of round 1 of 7691 (the same noise seed) | N1 to N3 | 7 180 s; 14 360 s |
| RMEM | four noisy runs on `dnf.calendar(7, 7, 7, 7)`: round 1 of 7691, 7692 and 7693, and round 2 of 7691 | the longest N run | 7 180 s; 14 360 s |

**RG is not a kit stage**, since it has no run. Its checks are direct calls to the frozen code, on each machine:

- the seed guard's refusals (a campaign seed outside the kit; seed 7501; a development seed in a campaign stage);
- the noise-model guard's refusal of a run that asks for another model;
- safeguards (i) and (ii) on deliberately altered copies.

Every bound is within the kit's 14 400 s. Campaign stages are unaffected. Each of their parts keeps runs on both
machines, and a part with fewer than four runs on a machine is a lighter load than the rehearsal's, which is
conservative.

RQ and RN use the development instances' own `PREDICTED.json`, computed on machine `a` from RM's evidence on `a`,
with the kernel gate run on it. RM's evidence on `b` is compared with `a`'s (section 11.5) and does not enter that
prediction. If a development instance is not measured, the next one replaces it in RQ, RN and RMEM, in seed order.
If none is measured, RQ and RN run on the development decks with the need-4 calendar, which is declared in the
record. RQ's run at need 7 makes the 0.75 rule try the limit formula of the runs without noise at both ends of its
calendar. RMEM tries the noisy limit at need 7. [new; coordinator's review 1, R4]

**Expected rehearsal compute** under the cost model, per machine, both machines in parallel:

| Stage | Expected compute |
|---|---|
| RC | about 2 112 s |
| RM | 2 081 s |
| RQ | about 1 790 s at need 4 |
| RN | 2 303 s |
| RMEM | 2 922 s |
| Total | about 3.1 h |

All of it is outside the 8 h budget of the campaign. [new]

### 11.3 First, the chain test on a short run

Before the long stages, **the end of the chain is tried once on each machine**, in stage RC (section 11.2). On
machine `b` this is also its first run through the kit. The deck limited to
120 s stops at its limit and leaves the links a stopped run leaves. Then, in order:

1. the collection, with the links of the stopped run;
2. the prediction (`PREDICTED.json`);
3. the kernel gate and `check.sh`;
4. the generation of the manifests of Q and N, dry and not launched;
5. the analysis, with M8 on whichever path the nominal cell takes, and `check.sh` on M8;
6. the writer of the record.

The chain test checks only that each step runs and writes its output. Its wall times are reported and enter no rule.
Its stopped deck is outside the 0.75 rule. A defect found here is fixed and the implementation refrozen, which is
declared, before RM starts. [L: the end of the chain tried on a short run; C4-A8 §4; C4-A11 §2]

### 11.4 The 0.75 rule

For every run of RM, RQ, RN and RMEM on either machine, its wall time recorded by the kit is compared with **the
campaign's time limit for a run of its kind and calendar** (section 10.4, the 2× limit, not the rehearsal's 3×).
**If any run uses more than 0.75 of that limit, or does not complete, nothing is launched until an amendment.** [D5-6]

### 11.5 The checks, each tied to what it concerns

[L: every check of the rehearsal tied to the model it concerns; C4-A9]

| Check | Concerns | Passes when |
|---|---|---|
| limits (the 0.75 rule) | every run kind, both machines, both ends of the calendars | every run within 0.75 of its campaign limit |
| reproducibility | the injected model | on each machine: the two runs of round 1 of 7691 in RN are equal as section 6 allows; round 1 and round 2 of 7691 in RMEM (one deck, one calendar) give different noise; all start from the same operating point |
| determinism of measures | calibration and runs without noise | (reported, not required) the same deck on machines `a` and `b`, compared as in section 6 |
| memory | the injected model, need 7 | the machine's peak resident memory over RMEM, sampled by the frozen code every second, at most 80 % of the machine's memory in its inventory |
| the gate on the cases | the kernel gate | P0 to P6 and their controls as in section 7.4, under `beta_0` and `beta_3` |
| the gate on the development instances | the kernel gate on mismatched cells | Lean and the Python agree per checker on every development instance with all its needs, under `beta_0` and `beta_3`. Whether any of them has room at `K = 3` (so that the true path of the `beta_3` conjunction is tried) is reported. If none has, the record says that this path was not tried |
| the mirror mutations | the Python mirror | every mutation detected |
| the seed guard, the noise-model guard, safeguards (i) and (ii) | the runner and the manifests | every refusal of RG |
| the collection | runs stopped at their limit | `COLLECTED.json` of every rehearsal stage written, and the folder unchanged |
| the analysis | the end of the chain | `PREDICTED.json` reproduced byte for byte from the evidence; every record equal to its files; `check.sh` passes on the gate and on M8 |
| no campaign seed | the seed guard | no deck of the rehearsal sets a seed other than 7691 to 7693 or none |

If any check but the one marked "reported" fails, nothing is launched until an amendment. The memory figure expected
from campaign 4's rehearsal is 17.7 % to 21.5 % of the machine [C4-A9 §1], measured on the nominal cell.

### 11.6 Resumable, written as it goes

The rehearsal **writes each check to its record as soon as the check is done**, and each machine's samples of memory
as they are taken. A rehearsal that stops resumes from its last written check, on the same frozen commit, without
rerunning a completed stage. A stage stopped mid-way is missing and is run again under a new stage name, which is
declared. The record (`REHEARSAL.json`) states the frozen commit, the CPU model and the OpenBLAS core of each machine,
every wall time, and the verdict of every check. [L: resumable; C4-A8 §1, §4]

## 12. Order of the campaign

1. This file, pushed alone. [method]
2. The implementation: campaign 4's frozen code at `093995b`, adapted as D5-8 says and as this file requires, then
   frozen. The list of frozen files is sent at the freeze. Independent review by the coordinator, and CI green on the
   frozen commit. [D5-8; method]
3. The chain test (11.3), then the rehearsal (11.2, 11.4 to 11.6), and `REHEARSAL.json` pushed.
4. `BEFORE_M.md`, pushed alone. [10.8]
5. **Measures**: stages M1 and M2. [C4 §Order]
6. **Predictions**: `PREDICTED.json` and the Lean file of the kernel gate, computed on machine `a`, committed and
   pushed **before any network run**. The launcher of the network runs is bound to the SHA-256 of `PREDICTED.json`.
   If the gate fails, no network run is launched. All the manifests of Q and N are pushed before the first launch of
   Q. [C4 §Order; C4 §Execution]
7. **Network runs**: Q, then N1, N2, N3, each with its parts.
8. **One analysis**, after the last stage has ended on both machines. Then `REPORT.md`. [C4 §Order]

## 13. What this campaign cannot show

Nothing about silicon, a layout, wires between cells or a real router. Nothing about the noise of a fabricated cell,
or about any noise model other than the injected one. Nothing about a monotone function other than
`(A and B) or (C and D)`, or about more than three cells and four inputs. Nothing about the native cascade of
`research/recursive-learning`. Nothing about outputs or ports without room. Nothing outside 27 C and the typical
corner with mismatch. The per-cell measures are made on the deck of the network by the same simulator: the claim is
that the network does what its cells, measured alone, say it will. [C4 §What this campaign cannot show; D5-3]

## 14. Where campaign 4's rules went

| Campaign 4 | Here |
|---|---|
| `PREDICTION.md` | sections 1 to 13 |
| A1 (the kernel's fields, budgets per cell, rail, timing of `c`, instances without a need) | 4.2, 5, 7.1, 7.2 |
| A2 (P4, its control, targets per case, latency of `c`'s pair, P6) | 7.1, 7.4 (P0 now asymmetric; controls for every "no" case) |
| A3 (exact arithmetic, ties to even, the interpreter) | 4.2 (now enforced by the frozen code: campaign 4's guarded fit ran in floats, section 3), 7.1, 10.2 |
| A4 (which validation verdict decides) | not needed: no device model (6) |
| A5 (stage protocols, safeguards, limits, extraction costs, M8 and M7 as observed) | 10.6, 10.4 (replaced by D5-4), 8 (M7, M8); extraction not needed |
| A6 (what two runs of one seed may differ in; later amendments in safeguard (ii)) | 6, 10.6 |
| A7 (the injected model) | 6 |
| A8 (audit subset rule and negative cases, OpenBLAS pin, completion, memory record) | 7.3, 10.2, 11.6 |
| A9 (the zero-amplitude check concerns the device model only) | 6, 11.5 (no device-model check) |
| A10 (`BEFORE_M.md`'s caps upper bounds) | 10.8 (the exact M caps recorded) |
| A11 (collection with links; a run at its limit is missing) | 9, 10.7 |

Item 5 of section 3: the search for seeds 7601 to 7699 covered every file except waveforms and CSV tables, looking
for a seed passed to `setseed` or named as a seed. It ran on `main` at `8bcd3d7` and on the heads of the 31
`research/*` branches on 2026-11-17, each fetched by name with depth 1 (blobs above 5 MB were not fetched and may not have been searched), never an
`evidence/*` branch. On `main` it found 7601 to 7620 only as `noise_id` values of
`research/circuit/repetition/manifest.json`, which are noise numbers and not mismatch seeds. On the 31 heads it found
nothing outside this campaign's own folder. The noise seeds of campaign 5 (76 011 and above) lie outside that range of
noise numbers (201 to 9 920).

[c4p]: https://github.com/HevisNico/kernel-R/blob/6232e16859b09b58dffd25bafac114e05ed905cb/research/learned-dnf-circuit-campaign-4/PREDICTION.md
[c4dir]: https://github.com/HevisNico/kernel-R/tree/6232e16859b09b58dffd25bafac114e05ed905cb/research/learned-dnf-circuit-campaign-4
[c4r]: https://github.com/HevisNico/kernel-R/blob/6232e16859b09b58dffd25bafac114e05ed905cb/research/learned-dnf-circuit-campaign-4/REPORT.md
[decisions]: https://github.com/HevisNico/kernel-R/blob/49684afca5231c5497a77742d3eeb5b3d1ed64c3/research/learned-dnf-circuit/DECISIONS.md
[budget]: https://github.com/HevisNico/kernel-R/blob/db4638bf4ad583d8b6e07eccb0936cc308068e94/research/learned-dnf-circuit/BUDGET_DECISION.md
[costdec]: https://github.com/HevisNico/kernel-R/blob/2ffe04db391e9d0cd674c8e55419509e6b2fa0e1/research/learned-dnf-circuit/COST_MODEL_DECISION.md
[costmeas]: https://github.com/HevisNico/kernel-R/blob/3144c5731881707eb3723773de8f9ab0937069a9/research/learned-dnf-circuit/cost-measures/COST_MEASURES.json
[cost4]: https://github.com/HevisNico/kernel-R/blob/8bcd3d744f101378c308a0af9da80631dded715f/research/network-noise-study/phase0/COST_C4_need4.json
[dnf]: https://github.com/HevisNico/kernel-R/blob/49684afca5231c5497a77742d3eeb5b3d1ed64c3/research/learned-dnf-circuit/dnf.py
[noise-report]: https://github.com/HevisNico/kernel-R/blob/fd25955adcdcb85b874c1ba38c3891a7411410af/research/network-noise-study/validation/REPORT_A2.md
