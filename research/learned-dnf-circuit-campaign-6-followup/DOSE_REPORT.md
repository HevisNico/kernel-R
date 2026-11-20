# A dose twice as large on the nominal cell: what was run and what it showed

**Development work. Exploratory, not preregistered, and nothing here is a claim.** Simulation only, one simulator,
one noise model, the nominal cell, one larger dose. It recounts no claim of campaign 6 and says nothing of what
campaign 6 would have counted under another rule.

Status on 2026-11-20: steps A to D of [`DOSE_PLAN.md`](DOSE_PLAN.md) are done. This report and the files of
section 9 are local and not pushed when it is written.

Marks: **[K]** known, read from a file named in section 9; **[I]** inferred, my reading.

## 1. The result, in plain words

- **The dose can be doubled cleanly** [K]. With the window raised from 0.6 to 0.7 V, each silent read moves the
  stored voltage by 2.708 mV instead of 1.349 mV, as evenly as before. A write stays clear of the FIRE. Each need
  falls from 4 to 2. Without noise, the network learns the predicted words and gives the 48 expected outputs.
- **Under noise, 16 network runs of 16 learned the same words as the quiet run**, 8 at each dose, with no FIRE bit
  different [K].
- **The plan's test of the noise (G6) says "unclear"** [K]. In mV, by campaign 3's definition, the scatter within a
  run is 47 % larger at twice the dose; the run offset and the per-dose term are within 25 %. "Go" needed all three
  within 25 %; "stop" needed a growth above 60 %.
- **Counted in steps, the noise is smaller at twice the dose by every reading** [K]: 0.47 to 0.56 of its value by
  the audit's instrument, 0.58 and 0.73 by campaign 3's. A noise constant in mV would give 0.50.
- **Under campaign 6's frozen budget, cell c still has no room on the nominal cell, at either dose** [K]. The
  budgets of c fall from 0.99 to 0.49 of a step, but the nominal cell's crossing does not sit in the part of the
  step that leaves room.
- **Explored after the fact, not the frozen rule** [K for the figures]: if c's reads with a single line were judged
  with a one-port budget, c would have room at both doses on the nominal cell, by 0.08 to 0.12 step at the unchanged
  dose and by 0.008 to 0.045 at twice the dose, the smallest below the 0.03 mV by which identical cells differ.

None of this is established. Section 8 lists what was not checked.

## 2. What was run

All on the nominal cell, with the pinned environment of campaign 6 (Python 3.12.3, numpy 2.3.5, ngspice 42, the
device library at `1232782c`), from the frozen code as it stands at `ecfcd1c1` on the branch
`research/learned-dnf-circuit-campaign-6-impl` (that commit is the branch's tip, the manifest of attempt c1's stage
N3). The files called here were last changed earlier: campaign 5's code and campaign 6's batch code at `b825d6aa`
(2026-11-18, the first commit of that branch), `network-circuit/net.py` at `834971ea`, `measure.py` at `f1dbd84d`,
the cell at `518852d2`. No frozen file was edited: the wrapper `dosedev2.py` rewrites one line of the deck
(`vhi=0.6` to `vhi=0.7`) while a frozen function runs. "1x" is the unchanged dose, "2x" the window at 0.7 V.

| Step | Runs | When (UTC) | Outcome |
|---|---|---|---|
| A | the guard-on calibration deck at 1x and at 2x (the "smokes", already published) | 06:34 to 06:54 | complete |
| B | at 2x: the guard-off deck, four scans, the both-lines check, four one-sided sets | 07:07 to 07:22 | 10 of 10 complete |
| C | one quiet network run at each dose; three more scans, outside the plan | 07:27 to 07:41 | 5 of 5 complete |
| D | 16 noisy network runs, 8 at each dose | 07:59 to 09:03 | 16 of 16 complete |

- The 1x measures (decks, scans, one-sided sets) are those of campaign 6's rehearsal r3 on the nominal cell
  (instance `none-a`), read with the owner's permission. They were not run again, except one scan (step C).
- Runs were at most four at a time, each under a limit of twice its expected time. No run was cut; the longest
  used 36 % of its limit.
- **Noise seeds.** The 16 seeds were declared in `NOISE_SEEDS_DEV.txt` before any noisy run: 5100001 to 5100008 for
  1x, 5200001 to 5200008 for 2x. Each was used once. None is a seed of any campaign; a search of `main` by value
  found none (text files, at `1e2dc6e7`).
- **Order of work in step D.** The reader `g6.py`, the list of runs and the rule were reviewed and fixed before the
  first noisy run. The reader was not changed afterwards.

## 3. The plan's tests, one by one

| Test | What it asks | 1x | 2x |
|---|---|---|---|
| G0 | the wrapper changes nothing by itself | the doses equal r3's, string for string | not applicable |
| G1 | the dose | 1.34944 mV | 2.70767 mV, 2.0065 times larger; successive doses differ by 0.003 % at most |
| G2 | a write stays clean | ERROR entry at 1.780 units, 0.87 unit after the latest FIRE | at 1.524 units, 0.61 unit after |
| G3 | the need exists and falls | 4, 4, 4, 4 | 2, 2, 2, 2 |
| G4 | the scans are clean | go | **stop by the letter; go on the coordinator's reading, made after the result**; see below |
| G5 | the network does what the measures say | go: six words, 48 outputs | go: six words, 48 outputs |
| G6 | the noise in mV, per constant | reference | **unclear**, section 4 |

**G4 at 2x** [K]. Four consistent brackets, none contradictory; `ceil(s*)` equals the deck's first firing stage,
four of four; every `u(0)` within 0.06 µV of the deck's; single ports silent at their bounds; both lines fire at
the preset. The plan's letter asks for brackets "of 1/256 stage": at 2x the scans gave 1/512 stage. In mV the
bracket is the same, 10.58 µV against 10.54 µV at 1x. By the letter that clause fails; the coordinator's written
reading, made after the result, is that a bracket no wider than 1/256 stage meets the purpose. Both are recorded in
`G4_2x.json`. (The script computes the width in µV with the larger of the two ports' doses.)

**G2, and where its figures come from** [K]. The table's figures are the smokes' (`DOSES.json` of each
calibration deck, the test the plan names): the ERROR entry falls between 1.7802 and 1.7804 units at 1x and between
1.5236 and 1.5244 at 2x; the smallest distance to the latest FIRE of the same cell is on c, 0.866 unit at 1x and
0.612 at 2x (0.902 and 0.647 on a and b). The quiet network runs give the same (`G5_1x.json`, `G5_2x.json`): entry at
1.7797 to 1.7804 and 1.5241 to 1.5248, smallest distance 0.864 and 0.610. From the quiet network runs only: no gated
read moves a stored voltage by more than 0.00003 mV at either dose.

**The one-sided sets at 2x: two bound rules** [K]. The four sets of step B are two pairs. Campaign 6's frozen rule
bounds each port of a and b at `s* + K` stages plus the half bracket, with `K` the largest of `8 - s*` and `s*` over
the two cells. The pair "s8" is at that bound: 4097/512 for a and 4103/512 for b, about 8 stages. The pair "s4" uses
the same rule with 4 in place of 8: 2049/512 and 2055/512, about 4 stages. G4 used s4, as the plan's primary set;
s8 was run beside it and is labelled exploratory in `G4_2x.json`. All four sets are silent. Section 5.4 uses the s8
pair, because the frozen prediction accepts a one-sided set only at the frozen rule's own bound.

**G5, and the check a calibration deck cannot make** [K]. At each dose, 12 reads may write and do fire: none
writes. No gated read writes. The two skew slots leave a and b silent.

**Crossings** [K], in stages: 1x: pairs of a and b 859/256 = 3.355, lines of c 919/256 = 3.590. 2x: a 855/512 =
1.670, b 861/512 = 1.682, line 1 of c 921/512 = 1.799, line 2 917/512 = 1.791. Half the 1x values would be 1.678 and
1.795.

**An observation at 2x** [K]. Cells a and b are the same circuit, and at 1x their scans give the same crossing.
At 2x they differ by 6/512 stage, 32 µV; the two lines of c differ by 21 µV. This is not chance: the two pair scans
run a second time gave the same brackets exactly, and the 1x scan of a run here gave r3's bracket exactly. Probable
cause [I]: the solver's tolerance; not tested. Consequence [I]: at 2x, the measure term of any budget is at least
about 0.03 mV, not the 0.005 mV of the bracket.

## 4. Step D: the noise at each dose

The rule, as written in the plan before any run: `d`, `w` and `b` as campaign 3 defined them, each within 25 % of
its 1x value is "go"; `w` or `b` more than 60 % above is "stop"; otherwise "unclear". Fixed with the coordinator
before the runs: the slope is the secant of each dose's own calibration deck; all four kinds of read together, 32
rows per dose; a run counts for a kind only if its word equals the quiet run's exactly; a fall of more than 25 %
also gives "unclear" (this side of the band had not been foreseen as a concern).

**The runs** [K]. 16 of 16 reached their last date. The 16 noise fingerprints are distinct and none is the quiet
runs'. In all 16 the six words equal the quiet run's (`ssssFFF` at 1x, `ssFFF` at 2x), the test outputs equal the
quiet run's, and no FIRE bit differs. So all 32 rows count at each dose.

**The verdict** [K]:

| | 1x | 2x | 2x / 1x | 95 % interval of the ratio (section 5.2) |
|---|---|---|---|---|
| `d`, per dose | 0.0080 mV | 0.0067 mV | 0.83 | 0.73 to 0.94 |
| `w`, within a run | 0.0787 mV | 0.1153 mV | **1.47** | 1.25 to 1.70 |
| `b`, the run offset | 0.1008 mV | 0.1172 mV | 1.16 | 0.89 to 1.47 |

`w` is outside "go" and below "stop": **unclear**.

**Beside the verdict, not governing** [K]:

| Reading | `w`, 1x → 2x (ratio) | `b`, 1x → 2x (ratio) |
|---|---|---|
| three-point slope, mV | 0.0677 → 0.0947 (1.40) | 0.0867 → 0.0964 (1.11) |
| no slope, latency units | 0.00720 → 0.00886 (1.23) | 0.00927 → 0.00888 (0.96) |
| divided by the dose, in stages | 0.0583 → 0.0426 (0.73) | 0.0747 → 0.0433 (0.58) |
| pairs of a and b alone, mV | 0.0701 → 0.0825 (1.18) | 0.0839 → 0.1082 (1.29) |
| lines of c alone, mV | 0.0864 → 0.1406 (1.63) | 0.1153 → 0.1256 (1.09) |

- With the three-point slope the verdict is the same: it does not depend on the slope.
- The growth of `w` is in the lines of c. Taken alone, the lines are above the 60 % line; the rule fixed before the
  runs is on all kinds together, and it is kept.
- **The audit's own instrument** (the score of silent training reads and the FIRE level, in steps of the quiet
  run): pairs, three sigma 0.176 → 0.083 step; lines, 0.219 → 0.124 step. In mV of one port, lines: within a run
  0.067 → 0.062, run offset 0.072 → 0.092, total 0.098 → 0.112.
- The quiet run's own FIRE latencies are not all equal. That floor of `w`, not removed: 4 to 24 µV at 1x, 5 to 23 µV
  at 2x.
- At 1x this is the first measure of the three constants by campaign 3's definition on the nominal cell: `b` 0.101,
  `w` 0.079, `d` 0.0080 mV, against 0.111, 0.094 and 0.009 in the budget.

**A limit stated before the runs.** The secant runs from the trained state to the deck's next stage: 1.35 mV at
1x, 2.71 mV at 2x, and the latency curve is not straight. The slopes differ by 16 % (pairs) and 17 % (lines)
between the doses, against a "go" band of 25 %. This is not all of the growth of `w` [I]: on the lines it grows by
34 % in latency units, where no slope enters.

**The two instruments disagree on the lines** [I], as in the audit: the audit's instrument sees the lines' scatter
within a run as flat in mV, campaign 3's sees it 63 % larger.

## 5. Analyses made after the verdict

All of section 5 was asked for after G6 was read. It is descriptive and changes no verdict.

### 5.1 The weight of one run [K]

One run at 2x, seed 5200006, has the largest `within` on line 1. **It was singled out after seeing the data.**
Leaving out one run at a time, `w` at 2x goes from 0.108 to 0.120 mV (lowest without 5200006) and at 1x from 0.077
to 0.080. Without 5200006 the ratios are `w` 1.37, `b` 1.19, `d` 0.85: still "unclear". On the lines alone `w` goes
from 1.63 to 1.49.

### 5.2 How sure the ratios are [K for the figures]

The 8 runs of each dose drawn again with replacement, 10 000 times (generator seeded with 1). The intervals are in
the table of section 4. Others: in stages, `w` 0.62 to 0.85 and `b` 0.44 to 0.73; lines alone, `w` 1.32 to 1.98;
pairs alone, `w` 1.03 to 1.31. `w`'s ratio is above 1 in every draw, within 25 % of 1 in 2.7 % of them, above
1.60 in 13 %.

- Reading [I]: `w` grows beyond chance; `b` cannot be told from constant; `d` is slightly smaller.
- Limits: 8 runs per dose is few for such an interval; the draw is by run and carries neither the uncertainty of
  the slope nor that of the quiet run. The cuts "all", "pairs" and "lines" use the same draws.
- An earlier message gave two rough figures for the same question (18 % and 10 %). They were estimates made by hand;
  these intervals replace them.

### 5.3 The FIRE bits these figures predict [K]

As in the audit: if a firing read's margin moved by a Gaussian of `sqrt(b² + w²)`, how many FIRE bits would differ
from the quiet run? At 1x, 0.006 of 320 firing reads; at 2x, 0.16 of 288. None was seen. Here, unlike in the audit,
the FIRE bits do not contradict the figures; the test has no power on these runs [I]. It covers firing reads only.

### 5.4 What campaign 6's frozen budget gives [K]

The frozen functions themselves were called on the nominal cell's measures at each dose, with three sets of
constants. The budget of a read is `eps + 3 s sqrt(w² + b² + n d²)` per port, two ports added linearly, plus the
measure term (campaign 5's `predicted.py`, lines 220 to 230 and 268 to 280; campaign 6's `predict6.py`, lines 213
to 221). For c, the training budget is a one-port budget and the testing budget a two-port budget. In stages:

| Case | a, b: budget | c: training | c: testing | c: sum | c: margin above − testing | Room: a, b, c |
|---|---|---|---|---|---|---|
| 1x, the budget's constants | 0.330 | 0.330 | 0.656 | 0.986 | −0.246 | yes, yes, **no** |
| 1x, the constants read at 1x | 0.291 | 0.291 | 0.578 | 0.868 | −0.167 | yes, yes, **no** |
| 2x, the budget's constants | 0.164 | 0.164 | 0.326 | 0.490 | −0.125, −0.117 | yes, yes, **no** |
| 2x, the constants read at 2x | 0.185 | 0.185 | 0.367 | 0.552 | −0.166, −0.158 | yes, yes, **no** |
| 2x, the same, measure term 0.03 mV | 0.194 | 0.194 | 0.376 | 0.570 | −0.175, −0.167 | yes, yes, **no** |

- In all five cases the reads of c without room are the same: each line alone at test, and both lines, which
  requires the two. c's training reads have room everywhere, but by little: the smallest slack (margin above minus
  the training budget) is 0.080 stage at 1x with the budget's constants, 0.119 with the constants read, and at 2x
  0.037, 0.017 and 0.008 in the three cases. The last is as small as the smallest slack of section 5.5. Without
  noise (K = 0) all three cells have room.
- Where the crossings sit [K]: at 1x the lines of c are 0.410 stage below the need; at 2x, 0.201 and 0.209.
- The budgets do fall with the dose. The part of a step where a crossing can sit and leave room (one minus the
  sum, my reading of the checks [I]) widens from 0.014 to 0.510 with the budget's constants, and from 0.132 to
  0.448 with the constants read (0.430 with the 0.03 mV term). The nominal cell's crossing is outside it at both
  doses. Where a crossing falls in its step belongs to the cell and the dose; this experiment did not choose it.
- With the constants read instead of the budget's, 1x gets easier and 2x harder: the gain from the dose is smaller
  than the budget's constants would say.

### 5.5 Exploratory: a one-port testing budget for c's single lines [K for the figures]

**This is not campaign 6's rule.** One change: c's reads with one line or none are judged with the one-port budget
at that line's need; the both-lines read keeps the two-port budget. The empty reads have no line: they take the
larger of the two lines' one-port budgets. The frozen functions compute everything else.

| Case | c's testing budget, one port | margin above − testing | Room for c | Width, frozen rule | Width, this rule |
|---|---|---|---|---|---|
| 1x, the budget's constants | 0.330 | +0.080 | yes | 0.014 | 0.340 |
| 1x, the constants read at 1x | 0.291 | +0.119 | yes | 0.132 | 0.418 |
| 2x, the budget's constants | 0.164 | +0.037, +0.045 | yes | 0.510 | 0.672 |
| 2x, the constants read at 2x | 0.185 | +0.017, +0.024 | yes | 0.448 | 0.631 |
| 2x, the same, measure term 0.03 mV | 0.194 | +0.008, +0.015 | yes | 0.430 | 0.613 |

- The both-lines read, with its two-port budget, does not limit c: its score exceeds the larger single line's by
  7.6 stages at 1x and 3.8 at 2x, against budgets below 0.7.
- Reading [I]: on the nominal cell this change alone gives c room at both doses, and the dose alone does not. For
  a crossing anywhere in its step the two add up. On the nominal cell the slack is smaller at 2x than at 1x.
- The smallest slack, 0.008 stage at 2x with the 0.03 mV term, is 0.02 mV. **That is not room while identical
  cells differ by 0.03 mV in the 2x scans.**
- **What the Lean statement asks** [K], read on `main` in `research/learned-coincidence/`. Campaign 6's gate uses
  the one-sided theorem (`gate4.py`, `checkCascadeCalibrationOneSided`). There, a test read of the second layer
  whose mask holds a line of the cell is a `FiringMaskRead` (`MonotoneOneSidedTarget.lean`, lines 24 to 34 and 47
  to 48): the observed read is checked against the threshold and by a comparison of scores, with no error budget;
  the testing error enters only as a lower bound on the score of each single line (line 34). A read with no line
  of the cell keeps the testing error (lines 49 to 51). The checker does the same (`MonotonePremiseTargets.lean`,
  lines 101 to 107 and 164 to 170), and `Disjunctions.check` uses the testing error on one line's score at its need
  and on the empty mask (`MonotoneTarget.lean`, lines 59 and 68). So in the one-sided statement the testing error
  of c bears on single-line and empty reads only: a one-port budget is what the statement asks of it, and the
  two-port budget kept here on the both-lines read is an extra check outside Lean.
- The two-sided statement is different: it applies the testing error to every observed test read of the second
  layer, both lines included (`MonotoneTarget.lean`, lines 176 to 178). A later rule must say which one it uses.
- **Not checked: the gate itself.** No gate file was written with such a rule and no check was run.

## 6. What this says, and what it does not

- [K] On the nominal cell, in this simulator, a dose twice as large is clean, and the network learns under the
  noise model in 8 runs of 8.
- [K] The noise in steps falls, but not by half on campaign 3's definition: `w` in mV grows.
- [K] Under the frozen rule the nominal cell's c has no room at either dose.
- [I] The dose and the one-port budget are two separate levers. This experiment measured the first on one cell and
  only computed the second.
- [I] Under the one-sided theorem, the one-port rule for c's single lines is the one the statement itself
  constrains (section 5.5). The gate was not run with it.
- It does not say that any instance of campaign 6 would have had room: nothing here was computed on them.
- "Unclear" is not a reason to change a budget, and nothing was run at three times the dose.

## 7. Defects found on the way, all corrected before the result they touch

- `g5.py`, first version: it asked the predictor for the skew slots too, and two test outputs were overwritten,
  which gave a false "stop". Corrected before step C was judged; the predictor is now called without the control.
- A sentence of the step B message said the 2x scans were "repeatable to about 15 µV". Wrong: the repeats are exact.
  The observation of section 3 replaces it.
- `g6.py` before the runs: a word was compared with a prefix of the quiet word; now exact equality. The check of
  the noise fingerprints became a precondition. Both changed before any noisy run.
- `step_b.py` holds a loop that does nothing (lines 30 and 31). `post_d.py` defines a constant it never uses.
  Neither changes a figure.

## 8. Not checked, and limits

- One cell, one larger dose, one simulator, one noise model, 8 runs per dose.
- The cause of the 32 µV difference between identical cells at 2x. A run at a tighter tolerance would test it; it
  was not run.
- Why `w` grows on the lines of c. No waveform was opened by hand.
- No interval on the audit's instrument; no bootstrap over kinds or reads.
- The readers have no unit tests. `g6.py` was checked against the audit's script on one instance of campaign 6's
  development data (11 rows, identical); `post_d.py` stops unless its figures equal `g6.py`'s; `post_d_a5.py` stops
  unless its cases equal `post_d.py`'s.
- The 1x budget figures were not compared with a prediction record of the rehearsal: none was found for the
  nominal cell. The Lean gate was not run on any case of section 5; section 5.5's reading of the Lean statements
  is a reading of their text, not a run.
- The constants read went into the frozen formula rounded to 0.0001 mV, all kinds together. c's own lines read a
  larger `w` at 2x; that case was not computed.
- The seed search covered text files on `main`; not binary files, not evidence branches.
- The output files have not yet been searched for machine paths; that is done when a push is prepared.

## 9. Files

Scripts and inputs (SHA-256):

| File | What | SHA-256 |
|---|---|---|
| `dosedev2.py` | the wrapper: the window, scans, network runs, the runner | `b0999ebe54552f9b77a1d41c63ad6465b4d9db1081a6a54dff002c3a03b1ce58` |
| `test_dosedev2.py` | its 13 tests, no simulation | `fd39b404ade8320f9ad980508a03d37c280609be6f49545921847329a84f1686` |
| `NOISE_SEEDS_DEV.txt` | the 16 declared noise seeds | `b33b281d3407cde6717adef3b762c15dc6199f5dfd66361c2296ef74943a2967` |
| `step_b.py` | step B's runs | `0356028cca850a32d55a0f954d1ee63dd6add59dc25011ec08d3e58214c03be5` |
| `g4.py`, `g5.py` | the readers of G4 and G5 | `772475d1…6752`, `6d144868…6a74a` |
| `g6.py` | the reader of G6, fixed before the runs | `bd0a38b0e0a3d33ae73f7634ab286353ff39d0d204083920b71708f9875e67cb` |
| `JOBS_D.json` | the 16 runs of step D | `96a1fdf6ddc61259b01e3e9b23ad7d72a49a6d6a1ce6d1d63e8dd8f6055b8eb9` |
| `post_d.py` | sections 5.1 to 5.4 | `dc38aadfb1b2be28fdce0178564dd77d553b28bdd52216ef5ef60d85aac5477a` |
| `post_d_a5.py` | section 5.5 | `fece0fac9a88e16f4480d3cb8f66b50935c1e22e3a29e8393b9d85890988f25f` |

Results:

| File | What | SHA-256 |
|---|---|---|
| `G4_1x.json`, `G4_2x.json` | G4 | `3e584675…3354`, `c2aa7bb3…63bf` |
| `G5_1x.json`, `G5_2x.json` | G5 | `a5033f20…b990`, `0fb9786c…5b58` |
| `G6.json` | G6: the verdict, every row, the readings beside it | `447268932a9cae9d7a2bad91566b1b04e859ca4c3e7c9e02b5c9acc1fad4f833` |
| `POST_D.json` | sections 5.1 to 5.4 | `317703a5a516db2c64c68f7d7c7d56e746bc860472beae5a18f9ece82cb3cc36` |
| `POST_D_A5.json` | section 5.5 | `83e7b1e048c491f7b09d933fd392991507f1d8a035ef8def410098f845488cb4` |

The runs themselves (31 folders beside the two published smokes, about 2.4 GB with their waveforms) are for the
evidence branch.
