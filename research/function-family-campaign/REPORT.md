# Function family campaign (a): report

Final report, 2026-11-22. Every number below names its source: a commit, or a file with its SHA-256. Times are UTC,
on 2026-11-22.

**Names used throughout.** Several short names are reused in the campaign, so this report always qualifies them:

- **Stages.** "Stage D", "stage S" and "stage O" are the measure stages (decks; scans and checks; one-sided sets).
  "Stage Q" is the network stage without noise, with the untrained runs. "Stages N1, N2, N3" are the noisy network
  stages, rounds 1 to 3.
- **Comparisons.** "Comparison M1" to "comparison M8" are the declared comparisons, as campaign 6 names them
  (`PREDICTION.md` section 5.7). They are not machines.
- **Machines.** "Machine M1" to "machine M6" are the six cloud machines.
- **Members and cells.** The members are X1 = A, X2 = A∧B, F4 = A∨B, F2 = A∧(B∨C) and F3 = A∨(B∧C). "Cell a" and
  "cell b" are the first-layer cells, and "cell c" is the second-layer cell, with its lines 1 and 2 (`c1`, `c2`).

---

## 1. Start here

**What was claimed.** The preregistration is `PREDICTION.md` (SHA-256 `5f9cdfe6…`), on
`research/function-family-campaign`, with amendments 1, 2a, 2, 2c and 2b (tip `2274f8f3`).

- Simulated SKY130 cells, each with its own mismatch, are joined as a two-layer network: two cells (a and c) for X1
  and X2, three (a, b and c) for F4, F2 and F3. Each cell is trained only by its own pulses.
- Five monotone functions are studied, one per instance, three instances per member: 15 instances, seeds 8501 to
  8515, assigned by a published draw.
- Before any network run, each instance's answers are predicted from measures of each cell alone. Lean's kernel proves
  that the prediction implies the member's truth table at cell c. The network runs then test the prediction.
- The claims, each with its own verdict (`PREDICTION.md` section 5):
  - the primary claim, without noise, per member and for the family;
  - N-out, N-own and N-word, under the injected noise model, pooled over members;
  - the controls U and S;
  - G, read-only;
  - H, observed only.

**What ran.** 204 runs, all complete. None was cut at its limit, lost, replaced or rerun. Sources: each machine's
`STATE.json` files on its evidence branch (section 12).

| Stage | Runs | What |
|---|---|---|
| stage D | 49 | calibration decks, with M5's duplicate `8501-cal-on-unary-dup` |
| stage S | 99 | scans, both-lines and preset checks |
| stage O | 12 | one-sided sets |
| stage Q | 20 | 15 runs without noise and 5 untrained runs |
| stages N1, N2, N3 | 8 each | noisy runs, rounds 1 to 3 |

- The six machines' `NOT_STARTED_D.json`, `NOT_STARTED_S.json` and `NOT_STARTED_O.json` are all empty.
- The largest share of a run's limit is 0.592 (`8504-X1-n3`, machine M2). Section 8 gives the table.
- The rehearsal that the preregistration requires passed before the campaign (section 7).

**Eligibility and room.** Source: `PREDICTED.json` (`2849a614…`), on `evidence/function-family-campaign-predicted` at
`fd64602e` (stage files at `d7e4fcc2`).

- **All 15 instances are measured and eligible**: the kernel's `checks` holds at K = 0 on each.
- **8 instances have room** (the kernel's `checks` holds at K = 3): 8501, 8504 and 8512 (X1); 8502 and 8513 (X2);
  8507 (F4); 8510 (F2); 8509 (F3). The other 7 have no room, so no noisy run was made on them.
- So 44 network runs: 15 without noise, 5 untrained, and 8 × 3 = 24 noisy.

**The result, in the preregistration's words.** Source: `RESULTS.json` (section 2).

- **Established:**
  - the **primary claim**, for each of the five members (3 instances each, no discrepancy), and so "established for
    the family";
  - **N-out**, **N-own** and **N-word**, each "established, pooled over F2, F3, F4, X1, X2", with no failure.
- **Per member, for the noise claims:** X1 and X2 "established"; F4, F2 and F3 "held on one instance, not
  established", each with its one instance with room.
- **Held** (verdicts not judged by instance count): **G**, **U** (each of the five members) and **S**.
- **H**: "observed and reported, never refuting". No late fire, routing loss or queue (section 2).
- **Refuted:** nothing.
- **Reproduction:** the analysis regenerated the prediction record from the measure evidence and compared it byte for
  byte with the pushed record: `prediction_record_reproduced` true (186 312 bytes). `missing` is empty, and
  `observed_without_prediction` is empty.

**What was said before any data.** `PREDICTION.md` section 5, "Expected outcomes, stated before any data":

- "At three instances per member, the expected number with every cell's room is about 2.1 for X1, 1.8 for X2, 0.9
  for F4, 0.6 for F2 and 0.6 for F3."
- "So the pooled N-out of c is likely to reach N_N = 2 through X1 and X2."
- "F4, F2 and F3 are likely to read 'held on one instance' or 'not established'."

The outcome: 3, 2, 1, 1 and 1 instances with room. The pooled noise claims were established through all five
members, and F4, F2 and F3 read "held on one instance, not established", as stated.

**Comparison M8, in one line.** On all 15 runs without noise, two of the three kernel checkers are true at K = 0. The
calibration checker is false on all 15, as in campaign 6. Section 5 gives the reasons, and no verdict depends on it.

**Scope.** Simulation only, one simulator, one deck, one injected noise model (section 11). The claims are about
instances and ports selected by per-cell measures before any network run.

**Blinding** (`PREDICTION.md` section 9). No word, output or score of any network run was read before the last stage
had ended on every machine. Between stages, only statuses, wall times and shares of the limit were read.

**How to check this report in a minute.**

1. Fetch `evidence/function-family-campaign-analysis` by name. Its tip is `d7ab44bb`, and `SHA256SUMS` in
   `research/function-family-campaign/analysis/` passes.
2. `RESULTS.json` is `4943dade…`. Its fields `prediction_record_reproduced`, `missing` and `claims` give section 2's
   table.
3. `analysis_step.log` (`da2d3c92…`) shows the Lean checks, the six branch tips and their file counts, and the free
   space check.

**Map: what to read.**

1. This file, then `RESULTS.json`, `RUNS.json` and `NOISE_SENSITIVITY.json` on `evidence/function-family-campaign-analysis`
   (`d7ab44bb`).
2. The preregistration: `PREDICTION.md`, then amendments 1, 2a, 2, 2c and 2b, on `research/function-family-campaign`
   (tip `2274f8f3`).
3. The frozen code: `FREEZE.txt` on `research/function-family-campaign-freeze` (`df3851b2`), with the network code
   (`70d9d795`) and the implementation (`920413ec`). The noise code: `FREEZE_NOISE.txt` on
   `research/function-family-campaign-noise-freeze` (`7ad98b14`).
4. The prediction record and the stage files: `evidence/function-family-campaign-predicted` (`fd64602e`, then `d7e4fcc2`).
5. The evidence: one branch per machine, `evidence/function-family-campaign-Mn` (section 12).
6. The rehearsal: `evidence/function-family-campaign-rehearsal` (`a82c3c65`) and `-rehearsal-M1` to `-M6` (section 7).

---

## 2. Result

Source: `RESULTS.json`, SHA-256 `4943dade8f7b8411220fc7d4113ff1eae1d5e0db703228e7171247b4d882594b`, on
`evidence/function-family-campaign-analysis` at `d7ab44bb`, computed once on machine M6 (section 10).

- `prediction_record_reproduced`: true. `missing`: []. `observed_without_prediction`: [].
- The minimum rule: a claim is established for a member with at least 2 counted instances of it, and the noise claims
  pooled with at least 2 instances from at least 2 members (`PREDICTION.md` section 5).

**The primary claim**

| Member | Instances | Discrepancies | Verdict |
|---|---|---|---|
| X1 | 8501, 8504, 8512 | none | established |
| X2 | 8502, 8508, 8513 | none | established |
| F4 | 8505, 8507, 8514 | none | established |
| F2 | 8506, 8510, 8515 | none | established |
| F3 | 8503, 8509, 8511 | none | established |
| family | 15 | none | **established for the family** |

**The noise claims.** Each counted instance has three noisy runs, rounds 1 to 3.

| Claim | Pooled verdict | Counted instances, by output or port | Failures |
|---|---|---|---|
| N-out | established, pooled over F2, F3, F4, X1, X2 | cell a: 8; cell b: 3; cell c: 8 | none |
| N-own | established, pooled over F2, F3, F4, X1, X2 | a: 8; b: 3; c1: 8; c2: 3; 0 not counted | none |
| N-word | established, pooled over F2, F3, F4, X1, X2 | a: 8; b: 3; c1: 8; c2: 3 | none |

- The 8 instances are the instances with room (section 1). Cell b and line `c2` exist only on F4, F2 and F3, hence 3.
- **Per member**, for N-out, N-own and N-word alike:
  - X1: established (8501, 8504, 8512);
  - X2: established (8502, 8513);
  - F4: held on one instance, not established (8507);
  - F2: held on one instance, not established (8510);
  - F3: held on one instance, not established (8509).

**The controls and G**

| Claim | Verdict | Counts |
|---|---|---|
| G | held | failures: none |
| U | held for each of X1, X2, F4, F2, F3 | fires: none |
| S | held | fires: none |

**H (observed, never refuting).** Over the 39 trained network runs, 15 without noise and 24 noisy (`RESULTS.json`,
`claims.H`; the untrained runs have no training):

- the minimum separation was 22.0 units on cells a and b, except 20.0 on cell a in each of F2's three runs without
  noise (8506, 8510, 8515). On cell c it was 21.80 to 22.0;
- late fires, arrivals not routed, cell-c fires outside, undelivered and queued were all 0;
- skews above bound: 0 for F4, F2 and F3. For X1 and X2 the field has no meaning, since cell c has one line.

**Outside room, there is no prediction.** No noisy run was made on the 7 instances without room (`PREDICTION.md`
section 4, decision O6), so no output was observed outside room.

---

## 3. The declared comparisons M1 to M7

These are reported per member and count for nothing (`PREDICTION.md` section 5.7). Source: `RESULTS.json`,
`comparisons`.

- **Comparison M1**: no data for any member, since "every noisy run of this member is on an instance with room (O6),
  every output counts".
- **Comparison M2**: no data, since "no network run is made on an instance that is not eligible (section 5.7)".
- **Comparison M3** (timing, against window 1.1, deadline of c 2.2 and skew 1.1 units). The largest latencies were
  0.96 units on a first-layer cell (F2, cell a) and 0.97 on cell c (X1). The largest arrival skew was 0.20 units.
- **Comparison M4** (the nominal cell's words against the measured ones). On every instance the nominal cell's
  letters differ from the measured ones on one or more ports: 1 to 12 letter positions per instance, 85 in all. For
  each instance the list against the run equals the list against the measures. `tests_vs_measured` and
  `tests_vs_run` are empty on all 15: the nominal cell's test outputs agree with the run's.
- **Comparison M5**: "not computed: the frozen family_predict.py computes no validation residual of the geometric
  fits", on all 15 instances.
- **Comparison M6**: no narrow crossing. On the 24 noisy runs, the words with and without the prime reading are equal.
- **Comparison M7** (the spread of the noisy rounds against the model's sigma). Over 27 ports with room, each with 3
  noisy runs, the spread of `u_end` was 0.009 to 0.081 mV, against a model sigma of 0.146 mV from decision 5's
  constants. The spread of the first FIRE's latency was at most 0.018 units.

---

## 4. The controls

- **U**: one untrained run per member, on that member's first eligible instance in seed order: 8501 (X1),
  8502 (X2), 8503 (F3), 8505 (F4) and 8506 (F2). Its `2^M` test slots only, on the preset state, every cell gated. No
  output fired on any pattern.
- **S**: in each skew slot of the 15 runs without noise, the pair cell stayed silent.
- **G**: held, F2's partial teaching reads included.

---

## 5. Comparison M8, the descriptive kernel check

Comparison M8 runs campaign 5's kernel checkers on the 15 runs without noise, at K = 0 and K = 3. It refutes nothing.
On each run, at K = 0:

- `checkCascadeValid`: true;
- `checkTrainingSeparation`: true;
- `checkCascadeCalibrationOneSided`: false.

The kernel agrees with the mirror on all 15. Source: `RESULTS.json`, `comparisons.M8`.

**At K = 3**, `checkCascadeValid` is false on 7 runs: 8508, 8505, 8514, 8506, 8515, 8503 and 8511. These are exactly
the 7 instances without room in the prediction record. The failing items there are:
- 4 "second: line training";
- 3 "first: early silence";
- 2 "first: stops";
- 2 "first: positive margin".

**Failing items at K = 0, by kind.** All are items of `checkCascadeCalibrationOneSided`. The last column says
whether campaign 5's text for comparison M8 stated the kind in advance. This campaign's `PREDICTION.md` names
comparison M8 only "as campaign 6 names them", and states nothing about its items.

| Kind | X1 | X2 | F4 | F2 | F3 | Total | Stated in advance? |
|---|---|---|---|---|---|---|---|
| residual, on firing reads | 37 | 38 | 84 | 81 | 88 | 328 | **yes**: "the residual of every firing read" |
| residual, on silent reads | 20 | 32 | 77 | 110 | 97 | 336 | **no** (explained in (a)) |
| route | 19 | 20 | 46 | 44 | 50 | 179 | **yes**: "exact route equality is expected to fail on every routed read" |
| anchor (cell c's anchors) | 3 | 3 | 6 | 6 | 12 | 30 | **yes**: "`c`'s anchors" |
| submask comparison | 0 | 0 | 6 | 6 | 6 | 18 | **yes**: "the submask comparison of its pair" |
| decoder: FIRE bit is the threshold comparison | 0 | 0 | 3 | 0 | 0 | 3 | **no** (explained in (b)) |

- Campaign 5's text, as campaign 6's report quotes it: "Stated in advance, from campaign 4's smoke run on the nominal
  cell: the guard stops the charge at the FIRE, so the residual of every firing read, `c`'s anchors and the submask
  comparison of its pair are expected to fail."
- **The residual split.** Each failing residual item was located in its run's observation (`RUNS.json`, field
  `observation`), and its read was classed as firing when it has an emission.
  - Over the 15 runs there are 703 reads: 367 firing and 336 silent.
  - **All 336 silent reads fail their residual. Of the 367 firing reads, 328 fail.**
  - This split is this report's reading of `RUNS.json`; the frozen code does not compute it.

**(a) Residuals on nearly every read: a unit mismatch by design.** As in campaign 6 (its report, section 3(a)):
- the prediction scores Z on the stored-voltage axis;
- comparison M8 compares these scores with the run's `q_peak`, in integer units.

So a residual fails even where the predicted and measured outcomes agree. This follows from documents fixed before
the data, but neither this campaign's `PREDICTION.md` nor campaign 5's text said that the residuals of silent reads
would fail.

**(b) The three decoder items: a peak past the nominal THETA, below the cell's own firing level.**

| Read | Predicted | Measured | The cell's own firing reads in that run |
|---|---|---|---|
| 8507 (F4), firstTrain round 2, cell a | 97802, silent | silent, peak 100238 (THETA 100000) | 102398 |
| 8514 (F4), secondTrain read 4 (cell c, line 1) | 97246, silent | silent, peak 100571 | 101482 |
| 8514 (F4), secondTrain read 5 (cell c, line 2) | 98178, silent | silent, peak 100842 | 101484 |

Predicted silent, and silent. Sources: `RUNS.json`, `observation` and `observation_predicted` of `8507-F4-quiet` and
`8514-F4-quiet`.

**Scope, as the method was designed.** The Lean gate certifies the prediction. The experiment tests its outcome.
Comparison M8 was never meant to certify the run.

---

## 6. The noise values and amendment 2b's declared comparison

**The values** (amendment 2b section 1). They come from `NOISE_VALUES.json` (`65145fa3…`), on
`evidence/function-family-campaign-noise-values` at `cf58f9c3`. They were computed on machine M6 from the
rehearsal's 8 noisy F2 runs and its two F2 runs without noise, by campaign 3's definitions (`FREEZE_NOISE.txt`
section 2).

| | measured | decision 5 |
|---|---|---|
| `b`, between runs | 0.110 mV | 0.111 mV |
| `w`, within a run | 0.0818 mV | 0.094 mV |
| `d`, per dose | 0.00820 mV | 0.009 mV |

- They rest on 48 run offsets, 108 within-run counts and 108 doses. No run was left uncounted.
- All three are below decision 5's values.

**Where they are used.** Only in the declared comparison after comparison M8, which counts nothing. No run and no
verdict reads them. The noisy runs use the injected model with the record's noise seeds. The prediction record, the
verdicts and comparison M7 use decision 5's constants.

**The declared comparison** (amendment 2b section 4). Source: `NOISE_SENSITIVITY.json` (`4f6dff83…`), same branch as
`RESULTS.json`.
- The larger of each pair is decision 5's own value, so the 15 kernel gates were rerun with exactly the record's
  constants.
- **All 8 instances with room keep it**: `room_K3_with_larger` is true on each.
- The 7 without room read "no meaning: no room at K = 3 in the record".

---

## 7. The rehearsal, before the campaign

`PREDICTION.md` section 7 requires the rehearsal to pass before any campaign stage. Its verdicts are discarded; none
is a claim.

- **The record.** The rehearsal record is `PREDICTED.json` (`c02057d3…`) on `evidence/function-family-campaign-rehearsal`
  (`a82c3c65`), on the top-up's instances 8303 and 8306, which have room for all five members.
- **The runs.** They are on `-rehearsal-M1` to `-M6` at `6071b93b`, `8ab9a063`, `d800c720`, `dbe8928f`, `ac6b2542` and
  `0bdff841`. Per amendment 2 section 1, "all 22 network runs and all 6 R-M runs completed and reached their last
  date". The largest share of a judging limit was 0.66 (`8306-F4-quiet`), so no run triggered the 0.75 rule.
- **The extra run.** `8306-F2-quiet` was added by amendment 2 section 2 for the noise values only. It ran on machine M5
  and is in commit `e85e4aa5` (tip `8c9fa1e8`). It counts for nothing else.
- **The network limits.** Amendment 2 set them from the rehearsal's measured cost per slot:
  `10 × ceil(2 × r × n / 10)` s, with `n` the run's slots and `r` per member and kind.
- **Not re-derived here.** This report did not re-derive the rehearsal's other conditions. They are recorded in
  amendments 2a and 2:
  - the prediction records reproduced;
  - G on F2's partial teaching reads;
  - a unary cell trained in a network run;
  - the analysis run end to end.

---

## 8. Runs and timings

Sources: each machine's `STATE.json` per stage, on its evidence branch (section 12). Each limit is the run's
`limit_s`: for the network runs it is amendment 2's rule, and for the measure runs the implementation's plan. A run
cut at its limit would not have completed. None was.

| Stage | M1 | M2 | M3 | M4 | M5 | M6 | Highest share of the limit |
|---|---|---|---|---|---|---|---|
| D | 10 | 10 | 10 | 6 | 7 | 6 | 0.548 (`8510-cal-off`, M4) |
| S | 17 | 22 | 22 | 13 | 9 | 16 | 0.567 (`8505-scan-c-line2`, M2) |
| O | 2 | 2 | 2 | 3 | 1 | 2 | 0.448 (`8506-onesided-b`, M2) |
| Q | 6 | 5 | 3 | 2 | 2 | 2 | 0.553 (`8509-F3-quiet`, M3) |
| N1 | 2 | 1 | 2 | 1 | 2 | 0 | 0.588 (`8504-X1-n1`, M2) |
| N2 | 2 | 1 | 2 | 1 | 2 | 0 | 0.583 (`8504-X1-n2`, M2) |
| N3 | 2 | 1 | 2 | 1 | 2 | 0 | 0.592 (`8504-X1-n3`, M2) |

- **When each stage ran:**
  - stage D: 15:31 to 16:47;
  - stages S and O: until 17:48;
  - stage Q: 19:29 to 19:49;
  - stages N1 to N3: 20:03 to 21:18.
- **Machine M6** has no noisy run: 8514 and 8515 have no room.
- **The noisy runs' wall times:**
  - X1 and X2: 572 to 738 s;
  - F4 (8507): 1 226 to 1 386 s;
  - F3 (8509): 1 242 s;
  - F2 (8510): 1 490 to 1 504 s.

---

## 9. CI and the independent reruns

- **The frozen code** (amendment 1): rerun on machine M3 at the tips of `FREEZE.txt`, with no simulation. The result
  is on `evidence/function-family-campaign-ci`, commit `5aa1fcde`.
  - `test_family_predict`: 14 tests OK;
  - `test_family_net`: 33 OK;
  - `test_family_reads`: 23 OK;
  - `test_campaign`: 36 OK;
  - `test_integration`: 16 OK;
  - `gencheck.sh` on the five synthetic gates: passed.

  The rerun first checked the 17 files of `FREEZE.txt`, the Lean archive (`7289597a…`) and `bin/lean` (`bf8d54e4…`).
- **The noise code** (`FREEZE_NOISE.txt` section 1): rerun on machine M3, 10 tests OK. Commit `114e8d27`, same branch.
- **The prediction record**: reproduced byte for byte by machine M3 before stage Q (the coordinator's record; this
  report did not see that run). It was reproduced again by the analysis on machine M6 (`prediction_record_reproduced`
  true).

**The duplicate** (`PREDICTION.md` section 6). Machine M5 reran machine M1's guard-on unary deck of 8501.
- **Code:** `impl/dupcheck.py` (SHA-256 `181d99efa7a89cbe78a8a3fe60c53b555e2c27d02732605e97e51d56af8db769`, listed in
  `FREEZE.txt`), with `topup.py` (`1458569ca1af38d5651c324fafc31cbda51236b4353e2132548e5078daf67fc2`). Both come from
  `research/function-family-campaign-impl` at `920413ec`.
- **Inputs:** M1's `8501-cal-on-unary` at `801c251f`, and M5's `DUP/8501-cal-on-unary-dup` at `57b58f16`. Each was
  fetched by name, its parts joined, and its 8 files checked against its machine's `SHA256SUMS`.
- **Run:** by the coordinator, after the analysis, with `python3 -E -s -B dupcheck.py RUN DUP` (Python 3.13, standard
  library only), reading files only, with no simulation. It is not part of `RESULTS.json`.
- **Result:** `"identical": true`, exit 0. All five fields are equal:
  - `input_spice` `1bf1e858…`;
  - `record` `1d1eef8b…`;
  - `result` `a43e887d…`;
  - `noise_sha256` `f6e28ad1…`;
  - `trace_raw` without its `Date:` line, `72ec1c73…`.

  The full `trace.raw` files differ (`trace_raw_full_equal` false), and each has exactly one `Date:` line
  (`date_lines` [1, 1]). So the criterion fixed in `PREDICTION.md` section 6 is met. The only difference is the
  `Date:` line, as in the top-up.
- This report did not rerun the check. The figures above are the coordinator's.

---

## 10. Deviations and incidents

| # | What happened | Effect on results |
|---|---|---|
| 1 | **Amendment 2b, the values' command.** `FREEZE_NOISE.txt` section 2's literal command cannot import the frozen modules, since `noise_constants.py` never calls `family_net.paths`. `values_step.sh` called the same `noise_constants.main` with the same arguments through `python -B -c`, after `family_net.paths`. No frozen file changed. Stated in amendment 2b section 2 | None |
| 2 | **Amendment 2b, the comparison's command.** No frozen command line calls `campaign_predict.noise_sensitivity`, so amendment 2b section 4 gives its command. A plumbing test showed that without a first `family_net.paths` line it stops at `import c4`. The line was added before the push | None |
| 3 | **Machine M3's container restarted at 18:36 and at 20:02**, with nothing in flight (the coordinator's record) | None: no run was lost |
| 4 | **Machine M2's first driver launch failed** and created nothing (the coordinator's record). The driver was launched again | None |
| 5 | **Machine M4's `chain_SO.sh`**, the script that chained its stages S and O, was not in its measure push (`295b2351`, which holds only `machine/chain_SO.log`). It was added later, as a new file, in `drivers/` of its network push (`b30588b8`) | None: the measure files are unchanged |
| 6 | **Machine M1's worker process restarted** after its stage N3 had ended and before its evidence push, with nothing in flight | None |
| 7 | **The analysis ran once, on machine M6**, from 21:32:03 to 22:19:17 (`analysis_step.log`). The free space was 41.4 GB against 36.5 GB needed (2.2 × 16.6 GB of files). Lean was M6's existing, checked extraction. The files counted were 376, 386, 394, 262, 248 and 243 on M1 to M6 | None |
| 8 | **`PREDICTION.md` as pushed** (`5f9cdfe6…`) still opens with its draft line: "DRAFT for the owner's review. Not pushed, not frozen." Its text is otherwise the accepted preregistration | Wording only |

---

## 11. Scope and limits

**What this campaign cannot show** (`PREDICTION.md` section 11):

- **Simulation only:** one simulator (ngspice), one deck, the typical corner at 27 °C with mismatch. No PVT
  corners, no Monte Carlo of the mismatch beyond the instances drawn, no parasitics, no layout, no silicon.
- **One noise model:** the injected model with decision 5's constants. Nothing about any other noise.
- **No external reproduction:** every run and the analysis ran on the six machines of this campaign.
- **The five functions only:** nothing about functions outside them, about three-input functions that need more than
  two layers, or about more than three cells.
- **No prediction outside eligibility or room:** nothing about instances that are not eligible, or outputs without
  room.
- **The same simulator and deck** serve the per-cell measures and the network runs. The claim is that the network does
  what its cells, measured alone, were predicted in advance to make it do, as proved by the kernel.
- **Selection:** the instances and ports were selected by per-cell measures before any network run.

**Known limits of this report.**

- The residual split in section 5 is this report's reading of `RUNS.json`, not a field the frozen code computes.
- Incidents 3 and 4, and the duplicate's result (section 9), are from the coordinator's record. This report did not
  see those machines' sessions or that run.
- The rehearsal's conditions are cited from amendments 2a and 2, not re-derived here.

---

## 12. Every SHA a reader needs

**Preregistration and frozen code**

| Item | Commit | SHA-256 |
|---|---|---|
| PREDICTION.md | on `research/function-family-campaign` | `5f9cdfe6…` |
| AMENDMENT_1.md | `f8a8809d` | `eb19e291…` |
| AMENDMENT_2a.md | `c69e45e1` | `1508f531…` |
| AMENDMENT_2.md | `cdd410d9` | `02fc38f3…` |
| AMENDMENT_2c.md | `cb5c93c4` | `5d757467…` |
| AMENDMENT_2B.md | `2274f8f3f68755fce4de0ed683c0d18839c925a3` | `4698faaaf8ccd3c4daa00bde0894bdd1a817b6eeed7f29b256b9d9455a80c8e8` |
| FREEZE.txt | `df3851b241433d3608d2e895014ed678cba3f0c1` | `3ac80fb0…` |
| network code / implementation | `70d9d795` / `920413ec` | per FREEZE.txt (17 files) |
| FREEZE_NOISE.txt | `7ad98b14b66921c7a08648b7ed25fd062a3da8aa` | `d7cc5078ee5d77a343a1c6642a289e996ccb431f1d6142eaf9995b19d14f02f7` |
| noise code | `7bc064e8` | `noise_constants.py` `a704b890…` |

**Prediction record, values and analysis**

| Item | Branch and commit | SHA-256 |
|---|---|---|
| PREDICTED.json | `evidence/function-family-campaign-predicted`, `fd64602e` (stage files `d7e4fcc2`) | `2849a6149ab978dc7a68f3d7e2122e783245066b7b45b47e091be4289f246482` |
| NOISE_VALUES.json | `evidence/function-family-campaign-noise-values`, `cf58f9c3dbe7fd0f234dbe60ac67f265c0062ec9` | `65145fa3fbefa31cef34da82ccd24408a872bb582385151aa54d7973d2b4380b` |
| RESULTS.json | `evidence/function-family-campaign-analysis`, `d7ab44bb6d903fc2d3ef5c345663b239490fd3d4` | `4943dade8f7b8411220fc7d4113ff1eae1d5e0db703228e7171247b4d882594b` |
| RUNS.json | same | `5798a82c7f18c17f8ba3dcd8798eafa56f408686c8c125ad409ff6b42ee0edb9` |
| NOISE_SENSITIVITY.json | same | `4f6dff83061a2712e7c6fc7ffaa1bd28e89bd3230ebba8bd6fa4d0043b8a4811` |
| analysis_step.log | same | `da2d3c92…` |
| CI reruns | `evidence/function-family-campaign-ci`, `5aa1fcde` and `114e8d27` | per their sums files |

**Evidence branches** (`evidence/function-family-campaign-Mn`; each tip read by name, files checked by the analysis)

| Machine | Measure stages D, S, O | Network stages Q, N1–N3 (tip) |
|---|---|---|
| M1 | `801c251f` | `ca9baf56` |
| M2 | `dff5c14b` | `43e554fe` |
| M3 | `a1d1aaa0` | `7e7ab446` |
| M4 | `295b2351` | `b30588b8` |
| M5 | `57b58f16` | `edc095d5` |
| M6 | `59d9964c` | `ce29f9d7` |

**Rehearsal**

- the record: `evidence/function-family-campaign-rehearsal`, `a82c3c65`, `PREDICTED.json` `c02057d3…`;
- the rehearsal evidence: `-rehearsal-M1` to `-M6`, `6071b93b`, `8ab9a063`, `d800c720`, `dbe8928f`, `ac6b2542` and
  `0bdff841`;
- M5's extra run `8306-F2-quiet`: `e85e4aa5` (tip `8c9fa1e8`).
