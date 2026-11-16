# Campaign 4, amendment 7: the noise model of campaign 4

Pushed alone on `research/learned-dnf-circuit-campaign-4`, after `PREDICTION.md` (commit `1596b36`) and amendments
1 to 6 (commits `c14124f`, `d6a75a9`, `41cf88b`, `a167f3c`, `6c5630f`, `424f6f9`), **before `BEFORE_M.md` and before
stage M**. It is the owner's decision. It is the file by which the owner chooses the noise model when the device
model is not validated (`PREDICTION.md`, Noise model, second item). Nothing else in `PREDICTION.md` or amendments 1
to 6 changes.

**No campaign seed (7501 and up) has been simulated, and nothing here depends on campaign-4 data.**

## 1. The verdict

The noise study's validation report is `research/network-noise-study/validation/REPORT_A2.md` at commit `fd25955`
(SHA-256 `ef136da5d31501ca06dc2183665612072ee21fa5326830b3a3f2ba59928a7c96`). Its results are `RESULTS_A2.json` at
commit `ca4c21f` (SHA-256 `77a8e3023d965a0b09ebda858d09c4e488e147eccacfda25164cd31a6c60fa45`).

- **Under the criteria with amendments 1 to 4, the governing reading** (campaign-4 amendment 4), the device model is
  **not validated**. V1, V2, V2b and V2c pass. V3, V4, V6, V7 and V8 fail.
- The reading under `SPLIT_A2.md` as first written gives the same verdict, so the two verdicts do not differ
  (amendment 4, section 3).
- The report's section 9 declares one change to the analysis made after the results existed. It is a fix to the
  computation of V7 that touches no tolerance and no other criterion. It cannot change the verdict: V3, V4, V6 and V8
  fail without it, under both readings.

## 2. The model of campaign 4

Campaign 4 runs under **the injected default**, the second item of `PREDICTION.md` (Noise model). This is the
injected model of campaigns 1 to 3 (`research/circuit/noise.py`, `trnoise` sources at the input of each block),
already implemented, frozen at commit `3156ee4` and being rehearsed. In this case `PREDICTION.md` already fixes the
following:

1. The noise constants are those of decision 5: `b = 0.111` mV between runs, `w = 0.094` mV within a run,
   `d = 0.009` mV per dose (`PREDICTION.md`, Noisy budget).
2. There is no noise-model extraction, so there is no E stage, and the rules of V2, V2b and the isolation check do not
   apply. The trip-value question does not arise. The noise seed is the imposed process number, and `xtrtol` is not
   set (`PREDICTION.md`, Noise model, the injected default).
3. The frozen code (`plan.py before-m`) recomputes `I`, the expected compute and the stage caps under the existing
   rules (`PREDICTION.md`, Execution, and amendment 5, sections 2 and 3), from the costs of the injected default:
   the noisy run at 1 316 s and no extraction (`PREDICTION.md`, The record before stage M, item 3). The rehearsal can
   then only lower `I`, never raise it. `BEFORE_M.md` records the result. This `I` may differ from the `I = 9` of
   `PREDICTION.md`, which was computed with the device model's costs and its E stages: under the injected default the
   frozen code may give more instances within the same 8 h (`plan.size`, up to 15), or fewer. It is the value of the
   rule of Execution, not a choice. After the rehearsal, `I` can only go down (`PREDICTION.md`, The record before
   stage M).

## 3. Why

A corrected model would need an independent justification, and then a new validation against five failing criteria,
two of them unexplained. V5 shows that the injected model is above the device model's reference at every frequency:
its spectrum is 2 to 20 times the reference, its drift 1.7 to 1.9 times, and its between-run rms 2.4 to 4.9 times
(the report, sections 4 and 6). So the noisy claims are tested under the stronger noise. This choice depends on no
campaign-4 data: no seed of 7501 or above has been simulated.

## 4. What was known when this file was written (2026-11-16)

- **The report.** The noise study pushed `RESULTS_A2.json` (`ca4c21f`) and `REPORT_A2.md` (`fd25955`) at 18:18:11
  UTC, on `research/network-noise-study-phase0`.
- **What the campaign director read.** The director had read no part of the report before the owner relayed its
  verdict, at about 18:31 UTC. The director then read `REPORT_A2.md` at `fd25955`, read-only: sections 1, 4, 5 and 7,
  the V5 table of section 6, and sections 9 and 10. The director computed the SHA-256 of `RESULTS_A2.json`, but did
  not read the file.
- **What the coordinator read.** Before the report was pushed, the coordinator had read the validation's criteria
  and amendments, machine 5's system records (`SYSTEM.txt`, `MEMORY.txt`, `SYSTEM_RESTART.txt`), the commit messages
  and run counts of the machines' branches, the queue's claims, and the noise study session's messages on the state
  and durations of its runs; no result of any run. After the push, at about 18:20 UTC, it read, read-only:
  `REPORT_A2.md` at `fd25955` in full, the messages of commits `d393262`, `ca4c21f` and `fd25955`, and the diff of
  `vanalyze.py` in `ca4c21f`. It computed the SHA-256 of `REPORT_A2.md` and `RESULTS_A2.json`. It did not open
  `RESULTS_A2.json`, `RESULTS_A2_SPLIT_AS_WRITTEN.json` or the `SHOT_*.json` files, and did not recompute the results.
- **The rehearsal.** The rehearsal of the frozen implementation had started at 18:11:16 UTC on commit `3156ee4`, on
  the nominal cell only. Its rehearsal stage M on machine `a` was launched through the kit at 18:11:24 UTC: two
  calibration decks, the run without noise, and the untrained check. At 18:18 UTC those runs were in progress. No
  noisy run had started, and no result of the rehearsal had been looked at. The rehearsal continues unchanged. It
  covers both noise models, as `PREDICTION.md` requires.
