# Campaign 6: report

Campaign 6, attempt c1: final report, 2026-11-20. Every number below names its source: a commit, or a file with its
SHA-256. Times are UTC, on 2026-11-19 unless a date is given.

**Names used throughout.** Several short names are reused in the campaign, so this report always qualifies them:

- **Stages and comparisons.** "Stage M1", "stage M2" and "stage M3" are the measure stages. "Comparison M1" to
  "comparison M8" are the declared comparisons of campaign 5. "Stage Q" and "stages N1, N2, N3" are the network stages.
- **Machines and cells.** "Machine a" and "machine b" are the two computers. "Cell a", "cell b" and "cell c" are the
  three simulated cells. Cell c has two input lines, "line 1" and "line 2".
- **Ports.** The ports `a1`, `a2`, `b1`, `b2`, `c1`, `c2` are the cells' learning ports.

---

## 1. Start here

**What was claimed.** The preregistration is `PREDICTION.md` (commit `df1a3cb`, SHA-256 `8e7392c5…2240`) with its
amendment 1 (`a0d4ad3`, `14a5379e…9554`).

- Three simulated SKY130 cells, each with its own mismatch, are joined as a network. They are trained only by their own
  pulses and should learn `(A and B) or (C and D)`.
- Before any network run, each cell's answers are predicted from measures of that cell alone. A Lean proof checks that
  the prediction implies the learned function. The network runs then test the prediction.
- The claims are:
  - the primary claim, without noise;
  - N-out, N-own and N-word, under the injected noise model;
  - the controls U and S;
  - G, read-only;
  - H, observed only.

**What ran.** Attempt `c1`. There were 62 runs, all complete with return code 0, none lost, none refused:

| Stage | Runs | What |
|---|---|---|
| stage M1 | 10 | calibration decks |
| stage M2 | 25 | threshold scans and both-lines checks |
| stage M3 | 10 | one-sided sets |
| stage Q | 5 | quiet runs (without noise), plus the untrained run |
| stages N1, N2, N3 | 4 each | noisy runs, rounds 1 to 3 |

- The source is `RESULTS.json` (`1b6e21f2…98e8e2`), section 2.
- The rehearsal that the preregistration requires before the campaign passed first (section 4).

**Eligibility.** Of the five instances 7801 to 7805, four are eligible: 7802, 7803, 7804 and 7805, so k = 4.

- The source is `stages/c1/PREDICTED.json` (`a8e1751e…aab8`, commit `b6e319f6`).
- 7801 is not eligible. The frozen prediction code raised on it (`TypeError: 'NoneType' object is not subscriptable`).
  This follows the rule stated from the start: `PREDICTION.md` lines 122–126, and stopping-rule amendment 1.

**The result, in the preregistration's words.**

- **Established** (counted runs from at least 2 eligible instances, no failure):
  - the **primary claim**, on all 4 eligible instances, 7802 to 7805, with no discrepancy;
  - **N-own**, with counted port-runs on all 4 instances, through the ports that have their own room (table in
    section 2);
  - **N-word**, on exactly 2 instances, 7804 and 7805. The ports of cell c had no room up to them and counted no run.
- **Held** (verdicts not judged by instance count): the controls **U** and **S**; **G**, its own verdict.
- **Not established:**
  - **N-out for cell a**: "held on one instance, not established" (7805);
  - **N-out for cell b**: "held on one instance, not established" (7804);
  - **N-out for cell c**: no counted run.
- **Refuted:** nothing.
- **Reproduction:** the analysis reproduced the prediction record byte for byte (`predicted6_is_reproduced: true`;
  `analyze6.py` line 186 compares the regenerated record's text with the pushed file's text). The missing list is
  empty.

**What was said before any data about cell c.** `PREDICTION.md` section 5 ("Cell `c` at `K = 3`, stated before any
data", line 242) says that N-out of cell c "will most likely have no counted output-run, and be 'not established'", and
that "N-own and N-word on `c`'s lines will most likely count few or no port-runs".

- The outcome: N-out for cell c had no counted run, as stated. N-word counted no port-run on cell c. N-own counted 9 on
  cell c (ports `c1` and `c2`, section 2).
- Section 11 gives the corresponding limit: "Nothing about outputs or ports without room".

**Comparison M8, in one line.** In the descriptive comparison M8, two of the three kernel checkers are true on all four
instances. The calibration checker is false on all four. Section 3 gives the reasons, and no verdict depends on it.

**Scope.** Simulation only, one simulator, one deck, one noise model. The claims are about instances selected by
per-cell measures before any network run (`PREDICTION.md` section 11).

**Blinding** (`PREDICTION.md` 9). No word, output or score of any network run was read before the last stage had
ended on both machines. Between stages, only statuses, return codes, wall times and fractions of the time limit were
read.

**How to check this report in a minute.**

1. Each of marker 3's 90 file hashes (`CAMPAIGN_MARKER_3.json`, field `files`) equals the SHA-256 of that path's blob
   at `7eaf94c`, and again at `ecfcd1c` (the last stage's manifest commit). This was checked here: 90 of 90, 0 bad.
2. `git diff --name-only 2e00835 ecfcd1c` lists 69 paths, and none of them is one of the 90 frozen paths.
3. `RESULTS.json`'s fields `claims`, `missing`, `predicted6_is_reproduced` and `runs` give section 2's table.

**Map: what to read, and what is superseded.**

1. This file, then `RESULTS.json` on `evidence/learned-dnf-circuit-campaign-6-c1-analysis` (`feb0927f`).
2. The preregistration: `PREDICTION.md` (`df1a3cb`), amendment 1 (`a0d4ad3`), `STOPPING_RULE.md` and its amendment 1.
3. The code: `campaign6/` on `research/learned-dnf-circuit-campaign-6-impl`, frozen at `7eaf94c` (marker 3).
4. The stages of attempt c1: `stages/c1/` (stage files, run lists, inputs, manifests, the prediction record).
5. The evidence: one branch per stage and machine, `evidence/learned-dnf-circuit-campaign-6-c1-<stage>-<machine>`
   (section 13).
6. The rehearsal that counts: attempt r3, in `stages/r3/` with its evidence branches (sections 4 and 13).
7. **Superseded markers.** Marker 1 (`b88144f`) and marker 2 (`7eda858`) were replaced by marker 3 (`2e00835`): first
   because of the shared claim key (incident 2), then because of the audit's fixes (freeze 3).
8. **Superseded attempts.**
   - Attempt 1's stage RM1 ran under superseded manifest code and counts for nothing (incident 2).
   - Attempt 2's files (`stages/STAGE_RM1.md`, `stages/RUNS_RM1.json`) belong to superseded code; CI failed on its
     stage-RM1 source commit `46e757c` (run 44489455167).
9. **Superseded files.** The old top-level stage files (`STAGE_RM1.md`, `STAGE_RM2.md`, `CAMPAIGN_RM1.json`,
   `CAMPAIGN_RM2.json`, `INPUTS_RM2.json`, `RUN_ATTEMPT_RM*.json`) belong to attempt 1. They are kept unchanged and are
   not read.
10. The batch (`BATCH_REPORT.md`, `57464435`) is a separate development study. It is pooled with nothing here.

---

## 2. Result

Source: `RESULTS.json`, SHA-256 `1b6e21f2c6bbf699aa2b0b72bbf816dcd1eb9c8991861bb8024a8c892f98e8e2`, on
`evidence/learned-dnf-circuit-campaign-6-c1-analysis` at `feb0927f` (verified file by file from the pushed branch).

- `runs`: 62. `missing`: []. `predicted6_is_reproduced`: true. `predicted_is_reproduced`: true.
- The minimum rule: "PREDICTION.md 5: held needs counted runs from at least 2 eligible instances".

| Claim | Verdict | Counted instances | Counts |
|---|---|---|---|
| primary | held, so **established** | 7802, 7803, 7804, 7805 | discrepancies: none |
| G | held | (own verdict) | failures: none |
| N-out, cell a | held on one instance, **not established** | 7805 | 3 output runs, 0 failures |
| N-out, cell b | held on one instance, **not established** | 7804 | 3 output runs, 0 failures |
| N-out, cell c | **not established** | none | 0 output runs |
| N-own | held, so **established** | 7802–7805 | 21 port-runs: `a1` 3, `a2` 3, `b1` 3, `b2` 3, `c1` 6, `c2` 3; 0 not counted; 0 failures |
| N-word | held, so **established** | 7804, 7805 | 12 port-runs: `a1` 3, `a2` 3, `b1` 3, `b2` 3, `c1` 0, `c2` 0; 0 failures |
| U | held | | fires: none |
| S | held | | fires: none |

**Three kinds of room**, each from the prediction record (`PREDICTED.json`):

- **A cell's room at K = 3** (`room_at_K3`) is what N-out needs. An output of cell a or cell b counts when that cell
  has it. An output of cell c counts only when cells a, b and c all have it.
- **A port's own room** (`learning_ports.<port>.own_room`) is what N-own needs.
- **Room up to a port** (`learning_ports.<port>.room_up_to`) is what N-word needs.

A port can have its own room while its cell has no room at K = 3. That is why cell c's ports count N-own port-runs
although cell c counts no N-out run.

**Which instance gives which port-runs.** Each counted port gives 3 port-runs, one per noisy round.

| Instance | Cell room at K = 3 | Ports with own room (N-own) | Ports with room up to them (N-word) |
|---|---|---|---|
| 7802 | none | `c1` | none |
| 7803 | none | `c2` | none |
| 7804 | cell b | `b1`, `b2`, `c1` | `b1`, `b2` |
| 7805 | cell a | `a1`, `a2` | `a1`, `a2` |
| Port-runs | | 7 ports × 3 = 21 | 4 ports × 3 = 12 |

This is why N-out for cell a counts 7805 only, N-out for cell b counts 7804 only, and N-out for cell c counts nothing.

**H (observed, never refuting).** On the four quiet runs:

- minimum separation was 22.0 units on cells a and b, and 21.92 to 21.96 on cell c;
- late fires, arrivals not routed, skews above bound, cell-c fires outside, undelivered and queued were all 0.

**Noise fingerprints.** `launch.py check-noise` over stages N1 to N3, both machines: all_distinct true, 12 fingerprints
for 12 runs. Source: `check_noise.json`, `a7aef502…b3d1`, same branch.

**Beside the result.**

- **7801 is not eligible.** The frozen prediction code raised. This rule was stated from the start (`PREDICTION.md`
  lines 122–126; stopping-rule amendment 1, which describes this `TypeError` path of the frozen geometric fit). It is
  the same mechanism as the batch's 7709.
- **Selection.** The instances were selected by per-cell measures (`PREDICTION.md` section 11).
- **One simulator, one deck.** The per-cell measures and the network runs use the same simulator and deck.

---

## 3. Comparison M8, the descriptive kernel check

Comparison M8 runs campaign 5's kernel checkers on the quiet runs of the eligible instances. It refutes nothing
(campaign 5's `PREDICTION.md`, SHA-256 `36249501…0b10`, section 8). On each of 7802 to 7805:

- `checkCascadeValid`: true;
- `checkTrainingSeparation`: true;
- `checkCascadeCalibrationOneSided`: false.

Source: `RESULTS.json` comparisons.M8, and `M8.lean` (`11daa418…4c5971`), same branch.

**Failing items, by kind.** The last column says whether campaign 5's text for comparison M8 stated the kind in advance.

| Kind | 7802 | 7803 | 7804 | 7805 | Total | Stated in advance? |
|---|---|---|---|---|---|---|
| residual, on firing reads | 32 | 35 | 37 | 38 | 142 | **yes**: "the residual of every firing read" |
| residual, on silent reads | 58 | 62 | 64 | 63 | 247 | **no** (explained in (a)) |
| route | 20 | 22 | 24 | 24 | 90 | **yes**: "exact route equality is expected to fail on every routed read" |
| anchor (cell c's anchors) | 6 | 6 | 6 | 6 | 24 | **yes**: "`c`'s anchors" |
| submask comparison | 2 | 2 | 2 | 2 | 8 | **yes**: "the submask comparison of its pair" |
| decoder: FIRE bit is the threshold comparison | 1 | 0 | 0 | 1 | 2 | **no** (explained in (b)) |

- Campaign 5's text says: "Stated in advance, from campaign 4's smoke run on the nominal cell: the guard stops the
  charge at the FIRE, so the residual of every firing read, `c`'s anchors and the submask comparison of its pair are
  expected to fail."
- The residual split: 142 failures on firing reads, stated in advance; 247 on silent reads, not stated. Each failing
  read was located in `M8.lean`'s traces and checked for an emission. Of the 248 silent reads, 247 fail their residual.

**(a) Residuals on nearly every read: a unit mismatch by design.**

- `MAPPING_U.md` v3 (introduced at `9c7a96e`; byte-identical copy on `-impl` at `b825d6a`; SHA-256 `fd7afedf…414f`, as
  in `PREDICTION.md`'s reference table) scores Z on the stored-voltage axis, `w_p(k) = (u_p(0) − u_p(k)) / D_p`.
- Comparison M8 compares these scores with the run's `q_peak`, the measured charge peak, in integer units.
- **Example: 7802, cell a, firstTrain.**
  - Predicted scores: 38103, 58339, 78573, 98805, 119035.
  - Measured `q_peak`: 86790, 90197, 93715, 97360, then FIRE.
  - The training-error budget is 541.
  - Both agree on the outcome: silent through round 3, FIRE at round 4.
  - Sources: `PREDICTED.json` observation, and `M8.lean` `trace_run_7802_ft` and `cascade_run_7802`.
- **Both halves must be said.**
  - This follows from documents fixed before the data: MAPPING_U v3 and campaign 5's definition of comparison M8.
  - But campaign 6's `PREDICTION.md` did not say that comparison M8's residuals would fail on all reads.

**(b) The two decoder items: a peak past the nominal THETA, below the cell's own firing level.**

| Read | Predicted | Measured | The cell's own firing reads |
|---|---|---|---|
| 7802, firstTrain round 3, cell b | 94221, silent | silent, peak 100635 (THETA 100000) | 101740 |
| 7805, secondTrain read 9 (cell c, line 2) | 98006, silent | silent, peak 100329 | 100876 and 100895 |

Predicted silent, and silent.

**Scope, as the method was designed.** The Lean gate certifies the prediction. The experiment tests its outcome.
Comparison M8 was never meant to certify the run.

---

## 4. The rehearsal (attempt r3), before the campaign

`PREDICTION.md` 7 and 10 require the rehearsal to pass before any campaign stage. It ran stages RM1, RM2 and RM3 on the
nominal cell (`none-a` on machine a, `none-b` on machine b), then stage RN on 7701 (machine a) and 7706 (machine b). Its
pass conditions are REHEARSAL_RULES in `campaign6/README.md`. **Its verdicts are discarded; none is a claim.**

| Condition | Figure | Source |
|---|---|---|
| 1. Every run completes | 23 of 23 (stage RM1 4, stage RM2 10, stage RM3 4, stage RN 5), all with return code 0 | each machine's `STATE.json` on the r3 evidence branches (section 13) |
| 2. The 0.75 rule | highest fraction 0.563 (`7706-quiet`, machine b) | the same, against `stages/r3/CAMPAIGN_<stage>.json` |
| 3. Section 7's other checks | the seed guard refused a campaign seed outside the kit and two development seeds in campaign stages; the noise-model guard refused `extracted` | `guards_demo.txt` ("RESULT all refused") |
| 4. check-noise under R1 | 3 distinct fingerprints for 5 runs. The two noisy runs are distinct from each other and from every run without noise. The 3 runs without noise share one, as R1 allows | stage RN's `check_noise.json` |
| 5. The analysis reproduces RN's record | `predicted6_is_reproduced` true | stage RN's `RESULTS.json` |
| 6. Each stage's marker check | VERDICT: PASSED at stages RM1, RM2, RM3 and RN | each stage's `MARKER_CHECK_<stage>.txt`, on machine a's evidence branch |

The rehearsal's measure doses `D_V` are identical on machine a and machine b, string for string, for `none-a` and
`none-b`. Source: `stages/r3/INPUTS_RM2.json` (`a031edd`, `daea47a9…65a5`).

---

## 5. Machines, and which ran what

**Machine assignment.**

- **Stage M1.** A run keeps its instance's machine: 7801 to 7803 on machine a, 7804 and 7805 on machine b (marker 3,
  `seeds.machine_of`).
- **Stages M2 and M3** follow amendment 1's two-shard alternation, so a run can be on the other machine. For example,
  `7801-scan-b-pair` in stage M2 ran on machine b.
- **Network runs** alternate machine a, machine b in seed order (`PREDICTION.md` 4; `stages6.py`). So 7803's network
  runs ran on machine b, and 7804's on machine a, though stage M1 measured them on machine a and machine b
  respectively.

**Machine a changed during the day.**

- At 17:40 a new session and container became machine a.
- The kit accepted the pushed `INVENTORY_a.json` (`e047e9d`, written at 05:50 on the earlier machine a). The kit
  compares the published inventory with the local one, and its machine, environment and executor.
- The inventory records a CPU at 2.30 GHz booted at 05:31:42. Machine a's envchecks in attempt c1 record 2.10 GHz and
  later boots.
- The earlier machine a ran attempts 1 and 2 and the audit. The machine a that ran the rehearsal r3 and attempt c1 is
  the later one, with its own restarts (section 7).

---

## 6. Runs and timings

Sources: each machine's `STATE.json` in the stage's evidence branch (section 13). Each limit is the run's `timeout_s`
in `stages/c1/CAMPAIGN_<stage>.json`, which is 10 × ceil(2 × estimate / 10). The 0.75 rule held on every run.

| Stage | Runs on machine a / machine b | Wall times, machine a (s) | Wall times, machine b (s) | Highest fraction of the limit |
|---|---|---|---|---|
| stage M1 | 6 / 4 | 554.4–714.4 | 633.6–810.7 | 0.507 on machine b (machine a: 0.43–0.45) |
| stage M2 | 13 / 12 | 33.9–450.8 | 35.9–612.4 | 0.619 on machine b, run `7801-scan-b-pair` |
| stage M3 | 5 / 5 | 200.2–204.4 | 213.2–237.2 | 0.539 on machine b |
| stage Q | 3 / 2 | 129.9–689.6 | 747.4–772.1 | 0.525 on machine b |
| stage N1 | 2 / 2 | 940.4, 1010.3 | 1118.3, 1134.7 | 0.399 on machine b |
| stage N2 | 2 / 2 | 884.0, 951.9 | 1104.3, 1117.9 | 0.394 on machine b |
| stage N3 | 2 / 2 | 1078.6, 1154.6 | 1090.2, 1100.4 | 0.407 on machine a |

**The first noisy runs against section 4's 1 400 s estimate, scaled to needs.** The scaled estimate is each run's
`estimate_s` in its manifest.

| Run | Machine | Wall (s) | Estimate (s) | Ratio |
|---|---|---|---|---|
| `7802-n1` | a | 940.4 | 1330 | 0.71 |
| `7803-n1` | b | 1118.3 | 1400 | 0.80 |
| `7804-n1` | a | 1010.3 | 1430 | 0.71 |
| `7805-n1` | b | 1134.7 | 1430 | 0.79 |
| rehearsal `7701-n1` | a | 1067.0 | 1480 | 0.72 |
| rehearsal `7706-n1` | b | 1231.8 | 1480 | 0.83 |

The rehearsal estimates come from `stages/r3/CAMPAIGN_RN.json`.

---

## 7. Restarts and the kernel

**Restarts consistent with idle sessions.** These restarts are consistent with a container restarting when its session
sits idle. That is an inference from the timing, not a documented rule.

- Pairs on the earlier machines, from the supervising session's record:
  - 08:32:54, against a message at 08:32:52;
  - 08:38:50, against messages at 08:38:50;
  - 15:06:21, in the minute of a request.
- On the machines of attempt c1:
  - machine a at 17:40:10 and machine b at 17:40:41, together;
  - machine b at 17:47:16;
  - machine a at 20:42:17;
  - machine a at 2026-11-20 04:10:01, after the campaign, on standby.

After each restart, envcheck passed again before any further launch. None of these fell inside a running shard, and no
run was lost.

**One host-update restart.**

- Machine a restarted at 2026-11-20 00:12:40, while `publish_evidence.py` was publishing stage N2's shard.
- The shard had already ended and been collected (24 files, 0 bad against `COLLECTED.json`).
- The kernel moved from 6.18.44-fc-v653 to v726.
- The interrupted publish left only an unpushed local commit (`20f59eb`). The re-run published `6c401e7f`, verified.

**Before stage N3, a deliberate idle cycle on machine b.**

- At 00:23:40 machine b was still on v653. With nothing in flight and nothing unpublished, it ended its turn on purpose.
- It came back at 00:24:47 on v726, and only then ran envcheck and launched stage N3.

**The kernel record.** Stage N3 ran on v726 on both machines. Every earlier stage ran on v653: all 12 earlier envchecks
on machine a show v653. The kernel line is recorded, not a stop condition; the kit's environment fields (Python, numpy,
ngspice, PDK, machine) did not change.

---

## 8. CI

Every stage source commit took the **short path**. The log line was "CI path short; the skipped steps (if short) read
only frozen files, which equal marker 3". Steps 9 to 14 were skipped: Lean install, smoke waveform, comparison M8's two
paths, the kernel gate on the 7.4 cases, the structural comparison, and the audit's negative cases.

| Stage | Source commit | CI run | Path |
|---|---|---|---|
| stage M1 | `d3480bec` | 44612538070 | short |
| stage M2 | `27438283` | 44617381148 | short |
| stage M3 | `cc0c39a8` | 44623031407 | short |
| stage Q | `f26e64bd` | 44634547176 | short |
| stage N1 | `3bfbf8bc` | 44637915797 | short |
| stage N2 | `c748e81d` | 44641491345 | short |
| stage N3 | `4962555f` | 44644998929 | short |

The full path ran on the frozen commit `7eaf94c2`: CI run 44570260200, 16:48:32 to 17:31:57, success. That run covered
the full Lean, audit and structural steps. The short path skips only steps that read frozen files equal to marker 3's.
The workflow was first tested on `-wip` (runs 44541675989 full, 44541744254 short, 44541813625 fallback).

---

## 9. Incidents

From `campaign6/README.md`, "Implementation incidents" (1 to 15), then those of attempts r3 and c1 (16 to 23).

| # | What happened | Fixing commit | Effect on results |
|---|---|---|---|
| 1 | Campaign 6's CI never passed before `55e5560`: campaign 5's smoke files were missing | `55e5560` | None |
| 2 | The claim key was the protocol's SHA-256 and the machine alone, so attempt 1's stage-RM1 claims refused stage RM2 | `1758644` (one stage file per stage) | Attempt 1 stopped after stage RM1, which counts for nothing |
| 3 | An ancestry check could not run in CI's shallow checkout (run 44481345779) | `6f29fe6` | None |
| 4 | `marker_check.py` named the old layout | `0c061cc` | None |
| 5 | README said the MARKER_CHECK file is pushed with the manifest, which the kit would refuse | `1758644` | None |
| 6 | Machine b's attempt-1 stage-RM1 evidence branch had a different layout | none (pushed files are never changed) | None |
| 7 | Wording of `marker_check`'s report ("91 frozen paths") | `0c061cc` | None |
| 8 | The working copy of the pushed `CAMPAIGN_RM2.json` was deleted by mistake | none needed (restored byte-identical) | None |
| 9 | Stage-Q and stage-N manifests bound the prediction record only through the run list | the `marker_check` commit after marker 3 | None |
| 10 | The pre-start audit of 2026-11-19: 14 numbered findings, one withdrawn (13 defects) (appendix A). README incident 10's "14" counts the withdrawn one | freeze 3 and the `marker_check` commit after marker 3 | None on any result |
| 11 | `marker_check` required a gate file for every measured instance, which would have refused stage Q | the `marker_check` commit after marker 3 | None |
| 12 | analyze6's mapping 5 created absent fields of comparison M8 (`start`, `emissions`), turning a KeyError into a silent `None` | freeze 3 (`222cfaf`) | None |
| 13 | The first CI short-path version never audited the gate file (runs 44536895037, 44536954202, on `-wip` only) | freeze 3 (`7eaf94c`); then tested green: 44541675989, 44541744254, 44541813625 | None |
| 14 | The local candidate chain (seven commits, throwaway author) was rebuilt as two commits with the owner's identity: FZ (`222cfaf`, tree equal to candidate F) and W (`7eaf94c`, the workflow) | `222cfaf`, `7eaf94c` | None |
| 15 | 11 finished worktrees were removed with `git worktree remove --force` without a status check | none | None known; anything uncommitted in them can no longer be checked |
| 16 | Stage RN, machine a: a guard chained with `&&` under `set -e` did not stop the script, so `runs/a` was cleared before publication; the push was then refused for a 133.6 MB file | published in parts per campaign 4's `PARTS.json` (`d9195141`); `publish_evidence.py` (`886ff40`) prevents this class | Nothing lost: the collected copy was intact |
| 17 | One read through `gh api`, while in this environment gh is for search only | none | None; declared at the time |
| 18 | Lean was not on PATH in the first proof run of `predicted6` | re-run with Lean on PATH | None: the pushed record is from the re-run |
| 19 | `stages6.py stage-file` fails when `stages/<attempt>/` does not exist | `mkdir -p` first (known limit) | None |
| 20 | `diskcheck.py` writes its report next to the manifest, which was once inside the checkout | the file was moved out; from then on diskcheck ran on a copy outside the checkout | None |
| 21 | Machine b's stage-Q evidence commit (`9dc06b78`) says "files above 100 MiB in parts of PARTS.json", but no file was split | none (the pushed commit is unchanged) | Wording only |
| 22 | The killed stage-N2 publish (section 7) left a local commit `20f59eb` in `ev_N2_a` | none (never pushed; the folder is kept untouched) | None |
| 23 | The analysis evidence commit `feb0927f` does not carry `RESULTS.json`'s SHA-256 in its message | the SHA-256 is given in this report and was verified from the pushed branch | None |

---

## 10. Rule changes of the audit (2026-11-19)

These were made before any stage-RN result and before any rehearsal result that counts. Source: `campaign6/README.md`,
"Rule changes of the audit"; the audit report (appendix A) lists the same R1 to R5.

- **R1. REHEARSAL_RULES condition 4.**
  - Old: "check-noise on RN's evidence from both machines reports every fingerprint distinct."
  - New: the two noisy runs must be distinct from each other and from every run without noise; the runs without noise
    may share theirs.
  - The network stages N1 to N3 keep "all distinct", over all their evidence together. That held: 12 of 12.
- **R2. RN's record.**
  - Old: "predicted6 for 7701 and 7706 on the batch's merged evidence, then analyze6". It crashed, and it compared with
    `PREDICTIONS_BATCH.json`, a record of another structure.
  - New: `PREDICTED_RN.json`, written by `predicted6.py --rehearsal` (round 1 only), pushed alone with its gate files
    before stage RN's stage file, its needs equal to the batch's.
- **R3. RN's analysis.**
  - Old: no restriction was written; the README gives only the new rule.
  - New: it covers stage RN's runs only (the quiet runs, `n1`, the untrained run); no `n2` or `n3` exist in its record.
- **R4. The procedure.**
  - Each attempt has its own `stages/<attempt>/`.
  - Manifests and marker-check reports stay outside the checkout.
  - Nothing is pushed to `-impl` from a source commit until both shards have ended.
  - The analysis takes explicit lists of collected stage folders.
- **R5.** There is no `PREDICTION.md` amendment. No rule, claim, instance or limit of the preregistration changed.

---

## 11. Known limits

- `analyze6.py`'s docstring says the adapter "maps exactly four things", but it lists five (mapping 5 is comparison M8's
  second-test fields).
- **The manifest's data path** (review point N1, observed, not fixed): `stages6.py manifest` checks that a data path is
  given exactly when the stage takes one, but not that it resolves to `stages/<attempt>/`. This is contained by the run
  list check and the manifest's SHA-256 of the committed data file.
- The test of mapping 5 asserts that a KeyError is raised, but not which key.
- Coverage: in the dry run's coverage table (26 variants), one cell was not covered: "N-out for cell c, held on one
  instance". No variant had exactly one instance counting cell c. The code path is the same mapping-4 minimum as for
  cells a and b, which was covered.
- `publish_evidence.py`:
  - it tests the push limit with `>` at line 84 but `>=` at lines 106 and 131, so a file of exactly 100 MiB is treated
    inconsistently;
  - its tests (9 of 9 passed on machine a and on machine b) are not run in CI.
- `stages6.py stage-file` needs `stages/<attempt>/` to exist.
- `diskcheck.py` writes its report next to the manifest it reads.

---

## 12. Glossary and timeline

**The campaign's structure.**

- **Marker**: a pushed JSON file listing the SHA-256 of each of the 90 frozen files at a frozen commit. Every manifest
  must match it.
- **Freeze**: the commit at which the code is fixed and its marker taken. Nothing frozen changes afterwards.
- **Stage**: one step of the campaign (stages M1, M2, M3, Q, N1, N2, N3). Each has its own protocol file, run list and
  manifest.
- **Protocol, source and manifest commits**: each stage's three commits. The protocol commit adds only its stage file.
  The source commit adds its run list and inputs. The manifest commit adds the kit's manifest and attempt marker.
- **The kit**: the launch kit (`launch.py`), which claims a stage for a machine, runs the shard and records its state.
- **Shard**: one machine's part of a stage.
- **Attempt**: one complete try of the stages, with its own folder `stages/<attempt>/` and its own claim refs.
- **Envcheck**: the environment check run on a machine before each launch and after each restart.
- **Roles**: the campaign director is the session that ran machine a and directed the stages; the coordinator is the
  session that coordinated and reviewed; the supervising session reviewed from outside; the owner is the repository's
  owner, who gave every go.

**The model.**

- **K**: `PREDICTION.md` gives no definition in words. It uses `K = 0` for the eligibility gate (line 132) and
  `K = 3` as "the noise budget" (line 63).
- **Need**: "the number of training pulses after which it fires", of a cell (`PREDICTION.md` line 32).
- **Port and line**: a port is a learning input of a cell (`a1`, `a2`, `b1`, `b2`, `c1`, `c2`). Cell c's two inputs are
  also called its lines.
- **Room**: whether the prediction still holds under the noise budget. A cell's room at K = 3, a port's own room and
  room up to a port are defined in section 2.
- **Quiet run**: a network run without noise. **Untrained run**: a network run with no training, for control U.

**Judging the claims.**

- **Claim**: a preregistered statement with its own verdict. Also, the kit's claim ref, which reserves a stage for a
  machine.
- **Eligible**: an instance that is measured, and whose prediction passes campaign 5's kernel gate at K = 0 in Lean
  and in the Python mirror.
- **Gate**: the Lean check, through campaign 5's `check.sh`, that an instance's prediction implies the learned function.
- **Verdicts**:
  - **held**: no failure in the counted runs.
  - **established**: held, with counted runs from at least 2 eligible instances.
  - **held on one instance, not established**: held, with counted runs from exactly one instance.

**Timeline of the freezes.**

1. Freeze 1: frozen commit `55e5560`, marker 1 `b88144f` (2026-11-19 05:38).
2. Freeze 2: frozen commit `6f29fe6`, marker 2 `7eda858` (08:33), after the claim-key fix.
3. Freeze 3: frozen commit `7eaf94c` (with `222cfaf`), marker 3 `2e00835` (17:33), after the pre-start audit.

---

## 13. Every SHA a reader needs

**Preregistration and markers**

| Item | Commit | SHA-256 |
|---|---|---|
| PREDICTION.md | `df1a3cbcf73ed0ad71e04ded987f756a466e3902` | `8e7392c5654975049de3d25adf8a511105fba425fdb07b4d841a12fdc6342240` |
| PREDICTION_AMENDMENT_1.md | `a0d4ad3cfd4ab5b669070c499385c2f5fdd06110` | `14a5379e8ec78fea5d137cecfbb3614b439fa227e5939c7653d6be518ddc9554` |
| CAMPAIGN_MARKER.json (1) | `b88144f5999bda8fe5672d20af791608fa3d7693` | `deb8e78c4425e9b97fe559f95f1da6a0b99775f557832cdbaa58003dab472c9f` |
| CAMPAIGN_MARKER_2.json | `7eda858a2ad0c999c37efd198161f4ab8df50e3a` | `2084a1c14f6679d6b3dd79564c13044870e152a56713ecc2b549f8e9ab154c68` |
| CAMPAIGN_MARKER_3.json | `2e00835dec24edd8cb9abc41dbdc0a993463854d` | `5a92a6498e7c605c2a537a97c7be454434f0d4eff7990f4d2a10d338643ee65b` |
| Frozen commit 3 | `7eaf94c21639c76bb165c5dc96e5f37e3bd82283` (with `222cfaf915b588389b9abb9e589c1adb8d80217a`) | |
| MAPPING_U.md v3 | `9c7a96e` (copy on `-impl` at `b825d6a`) | `fd7afedf4df72ea302af178c1f9b4feb42aaccfe9f20014d34323998aa49414f` |
| publish_evidence.py | `886ff402cedb1d5e5a2f9d27d7200b8739ac7b7c` | |

**Attempt c1 stage commits** (all on `-impl`)

| Stage | Protocol | Source | Manifest + marker |
|---|---|---|---|
| stage M1 | `fc34fa1d` | `d3480bec` | `533da74a` |
| stage M2 | `354d8dbe` | `27438283` | `f8015540` |
| stage M3 | `491000d9` | `cc0c39a8` | `4bcdb284` |
| stage Q | `25c44dc4` | `f26e64bd` | `1977ad89` |
| stage N1 | `8f94421a` | `3bfbf8bc` | `7ca5d88c` |
| stage N2 | `e711cdc8` | `c748e81d` | `b127a565` |
| stage N3 | `4ac990e1` | `4962555f` | `ecfcd1c1` |

The prediction record is `b6e319f6`. Its `PREDICTED.json` is
`a8e1751e72a27d0b5c3ee722ec47f5ab12ea661b5554a7356e3b89b859daaab8`.

**Attempt c1 evidence branches** (`evidence/learned-dnf-circuit-campaign-6-c1-<stage>-<machine>`, every file verified
against `COLLECTED.json`)

| Stage | Machine a | Machine b |
|---|---|---|
| stage M1 | `90ce4b9bb5ce5803c8b29435475da31937be1364` | `f0b3b4ea94e2b323a53bc4feae225efd320dc782` |
| stage M2 | `220fd6c8fb81b0c4825d964df2c5f1be33098a00` | `5b01e46ffa3d95c3c9fb829486aa9a8b2be60185` |
| stage M3 | `c0b26dbf7b220530a41054f624909d70bd8945c2` | `8798d4c274c6fb84162d9bf7f2a3baf0eaaee98a` |
| stage Q | `7361a44487342a7aa2e0ea100869309ca76d74e4` | `9dc06b78a12552fb92ae329dd35fb64321909435` |
| stage N1 | `38ee6bbba2756ddbca8046c263f445f468ea8101` | `56cc33c8ce9652ac8ad98d8c1817f917f0daf8b3` |
| stage N2 | `6c401e7fcbd313ee49a329805e8c95dbbebd5fc6` | `eec037c8ebce0644a9c9265a3dd3130c643e5a7a` |
| stage N3 | `788d993448bb8813f086a6dd52b913230f78eaf5` | `3b68a15a5afd3f3a3ef25685737dbd244d7aafff` |

**Analysis** (`evidence/learned-dnf-circuit-campaign-6-c1-analysis`, commit `feb0927fd62eed08918bc612bf5e10f1ab637c70`)

| File | SHA-256 |
|---|---|
| RESULTS.json | `1b6e21f2c6bbf699aa2b0b72bbf816dcd1eb9c8991861bb8024a8c892f98e8e2` |
| M8.lean | `11daa418a26b0244cb7958494132d5e7f050c376cf04a00c81489f4b974c5971` |
| check_noise.json | `a7aef502e04200aa66159a3f359fda783c44d2548bbf45327772cbc50a96b3d1` |
| analyze6_stdout.txt | `d90cc5729a54d6448b75b37d9b73b5014b262847276dd6eed4762cb4fac047bc` |
| analyze6_stderr.txt | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (empty) |
| COMMAND.txt | `b8229c9f3b575fff23dfdcfdcf3bb01580a4dcccb8aa01cfd28050a4b90d6075` |

**Rehearsal r3 evidence** (machine a / machine b)

- stage RM1: `cdb7d030` / `3e4a7872`
- stage RM2: `2fe244f6` / `dae1db40`
- stage RM3: `8a5a92d3` / `1d213416`
- stage RN: `d9195141` / `7b660b7c`

RN's record `stages/r3/PREDICTED_RN.json`, at `ce9880c0`, has SHA-256
`69d386e5b939b111dfda5271d5033a9d7ef8df2660dbc1605e05de3d2952265b`.

---

## Appendix A. The pre-start audit of 2026-11-19 (incident 10)

**Source.** The audit report was sent by the campaign director to the coordinator on 2026-11-19 at 10:08 UTC. It is an
unpublished message, 11 841 bytes, text SHA-256
`29e7eaa9ce3ec9db51bc17ba06b59098b715b5e487c4b212608f6cd2216e3e83`.

- It holds findings 1 to 12 and the rule changes R1 to R5. Finding 13 (withdrawn) and finding 14 came after it.
- That makes 14 numbered findings, one withdrawn: 13 defects.
- Its text is condensed here without changing any finding.
- The file `AUDIT_REPORT.md` in the dry-run archive (`a711a6e4…`) is an unfinished draft (SHA-256 `ed1a14d6…`, findings
  section empty). It is not the report.

**How the audit tested.**

- The real `launch.py` was run in-process, with four patches only. Throwaway clones were used, and claim refs went to a
  local bare repository.
- A fake simulator replayed real results and traces.
- A CI simulation put dummy files at every future `-impl` path, in deep and depth-1 clones.
- Cases covered: stage RM1 to stage RN end to end, stage M1 to the analysis, one eligible instance, zero eligible, and
  the cases F1, F2 and F3 on their own.

The report does not state, finding by finding, which test found each. The fix-commit column below is the author's
reading of the commit messages, not the report's.

| # | What | Fix | Fix in (read from the commit messages) |
|---|---|---|---|
| 1 | `test_c` commits a fixture that collides with real stage files, so CI fails on every commit after the first stage file | the test builds on a parentless base without `stages/` | `222cfaf` |
| 2 | (F3 + claim key) The layout cannot host a new attempt, and the claim key is reused across attempts. A claimed-then-aborted attempt would block its stage forever (the dry run's stage-RM1 claim ref equalled rehearsal 2's real `STAGE_RM1`) | an attempt id in the stage file; each attempt's files under `stages/<attempt>/`; stages6, `c6.stage_check` and `marker_check` take the attempt | `222cfaf`, `e9d7e17` |
| 3 | The STATE.json race: `c6` read the kit's STATE.json while the kit rewrote it non-atomically, so a registered run could be lost (the dry run lost `none-b-scan-b-pair`) | a tolerant reader in `c6` (retry, then refuse); `launch.py` untouched | `222cfaf` |
| 4 | (C1) RN's record could not be produced: predicted6 built rounds 1 to 3 while `c6.noise_seed` allows only round 1 for rehearsal seeds. Its reproduction was unreachable: the comparison was against `PREDICTIONS_BATCH.json`, a record of another structure | `network_runs` takes the rounds; `PREDICTED_RN.json` pushed alone before stage RN's source commit; stages6 builds stage RN's runs from it, with its needs asserted equal to the batch's | `222cfaf` |
| 5 | (C2) `analyze6.main` had no command line for RN | a `--rehearsal` mode | `222cfaf` |
| 6 | (C3) `predicted6.layout` labelled a kit-complete run whose record did not reach its last date as "complete" | an explicit label that `predict_batch` never counts | `222cfaf` |
| 7 | (C4) The analysis walked folders recursively, and the last duplicate run id won | explicit lists of collected stage folders; any run id outside the record, and any duplicate, refused | `222cfaf` |
| 8 | (F1) A manifest inside the checkout gave "not clean", and MARKER_CHECK was then written inside it | `marker_check` refuses a manifest inside the repository; the report goes outside | `222cfaf`, `e9d7e17` |
| 9 | (F2) An unrelated commit after prepare made run-machine refuse | the rule that nothing goes on `-impl` from a source commit until both shards end; `marker_check` checks the head's diff stays within the kit's allowed files | README R4; `e9d7e17` |
| 10 | `marker_check` (`0c061cc`) allowed `stages/PREDICTIONS.json` for stages Q and N, but predicted6 writes `PREDICTED.json` (a naming error) | the right names under `stages/<attempt>/` | `e9d7e17` |
| 11 | (incident 9, confirmed) Stage-Q and stage-N manifests did not bind the prediction record | stages6 binds `PREDICTED.json` / `PREDICTED_RN.json`; `marker_check` requires each byte-identical to the record's own earlier commit | `222cfaf`, `e9d7e17` |
| 12 | The analysis input layout was undocumented | the README procedure names the collected stage folders | `222cfaf` (README) |
| 13 | WITHDRAWN by the director: "python.log not frozen". `check.sh` was thought to read a file outside the frozen set; it compares `expected/python.log`, and the drafts path appears only in a comment | none | none |
| 14 | Found after the report, by the regression proof: comparison M8's `assumption_on_c` called `predicted.exact` on `secondTest[AB]` and `secondTest[CD]` (`.start`, `.emissions`), which `PREDICTED.json` holds as strings (exact fractions), so it raised on every eligible instance with c1 ≠ c2. Campaign 5 never ran that branch | analyze6 mapping 5 converts exactly those fields, only where present | `222cfaf` |

**The reviews of the candidate** (README incidents 11 and 12). Each fix is in one of the pushed commits `222cfaf`,
`7eaf94c`, `e9d7e17`, `1b84c40` and `8f20185`.

- `marker_check` requires a gate file exactly for each measured instance with an observation.
- Gate files are checked unchanged at the source commit.
- The refusal tests were restored.
- README step 4 checks that the pushed manifest is the checked one.
- The manifest's data path is observed and contained, not fixed (section 11).
- Diskcheck's explicit kinds and its "extrapolated" wording.
- From the supervising session's review: mapping 5's absent fields.
