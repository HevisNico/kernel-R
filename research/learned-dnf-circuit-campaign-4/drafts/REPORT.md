# Campaign 4: report

## In plain language

**What campaign 4 set out to show.** Three SKY130 cells, wired as a small network, learn the Boolean function
`(A and B) or (C and D)`, and each cell's outputs can be predicted in advance from measures of that cell alone. The
plan, fixed before any run in [`PREDICTION.md`][prediction], was: measure each of 12 instances (seeds 7501 to 7512)
cell by cell (stage M), predict their outputs with frozen code, check the prediction with a Lean kernel gate, then run
the networks without noise (Q) and with noise (N1, N2, N3) and compare.

**What happened, in order.**

1. The noise study did not validate its device noise model, so campaign 4 took the injected default noise model
   ([amendment 7][a7]).
2. The rehearsal of the frozen code on the nominal cell was run, its first attempt interrupted by an operator error
   and its second completed after a defect in a final audit ([amendments 8][a8] and [9][a9]). Its record set the
   time limits of every stage.
3. Stage M ran the 24 calibration decks of the 12 instances, two per instance (guard on, guard off), on two
   machines. Every guard-on deck, and one guard-off deck (seed 7511), reached its time limit of 660 s; the other 11
   decks completed ([amendment 11][a11]).

**The result.** An instance is measured only when both its calibration decks count ([`PREDICTION.md`][prediction],
"Measures, each cell alone in its slot"). No instance was measured. So there is no prediction, no kernel gate on a
prediction, and no network stage: **no claim of campaign 4 was tested, refuted or confirmed.** Nothing was rerun;
seeds 7501 to 7512 are spent.

**The time limit** of 660 s came from [amendment 10][a10]'s rule: 1.3 times the calibration deck's expected cost
(925 s) times the ratio measured in the rehearsal (0.549), under the cap of 1.3 times the expected cost. This report
states no cause.

**Every departure from the plan**, one line each (details in section 1):

- Amendments 1 to 6, before the freeze or the rehearsal: the kernel gate's inputs, its cases, exact arithmetic,
  which noise verdict decides, the stages' protocols and time limits, and what two runs of one seed may differ in. No
  effect on any measure.
- Amendment 7: the injected noise model, since the device model was not validated. No noisy run took place.
- The rehearsal: attempt 1 interrupted, attempt 2 completed rather than redone, its memory stages rerun, the floats'
  kernel pinned (amendment 8). It set the 660 s limit.
- The rehearsal's zero-amplitude check failed (amendment 9). It concerns only the device model, which was not used.
- Amendment 10: how the stage caps and time limits are recorded. It states the 660 s limit; it changes no value.
- Restarts of both machines while nothing ran, one of them on machine `b` before its launch. No run was cut.
- Stage M's evidence collected by a reviewed script, since the kit refused the links left by the stopped decks
  (amendment 11). Every file kept byte for byte.

---

## 1. The departures

| What | Why | When | Effect on the results |
|---|---|---|---|
| [Amendment 1][a1]: what the kernel gate needs that `PREDICTION.md` does not fix | the Lean premise and its checkers need rules `PREDICTION.md` leaves open, so that the kernel and the Python agree | before the freeze | none: no gate ran on a prediction |
| [Amendment 2][a2]: the gate's case P4 redefined, a control P4′ added, a target per case | to fix, for every case, the condition it must fail and nothing else | before the freeze | none |
| [Amendment 3][a3]: exact arithmetic for every integer, the pinned interpreter, a correction | a fitted value exactly halfway between two units, rounded by floating-point error; the interpreter not pinned | before the freeze | none |
| [Amendment 4][a4]: which verdict of the noise validation decides | the validation reports two verdicts and does not say which governs | before the verdict was known | it fixed which verdict decided the noise model |
| [Amendment 5][a5]: a protocol file per stage, the time limits as a computation, the extraction costs | the kit claims a machine once per protocol file; the time limits and the extraction costs were not fixed | before the freeze | its rule, with the rehearsal's ratio, gave the 660 s limit |
| [Amendment 6][a6]: what two runs of one noise seed may differ in | records and evidence hold fields with the time of day or the simulator's timing | before the rehearsal | none |
| [Amendment 7][a7]: the injected default noise model | the device model was not validated ([the noise study's report][noise-report]) | after the verdict, before `BEFORE_M.md` | the noise model of campaign 4; no noisy run took place |
| Rehearsal attempt 1, [interrupted][run1] | the 2 h limit of the director's session tasks, not checked, stopped it (operator error) | 2026-11-16, before any check | none: no check evaluated; redone as attempt 2 |
| Rehearsal attempt 2, [stopped][run2] at the audit of `M8.lean`, then [completed][run2c] | `check.sh` refused the analysis's `theorem no_eligible_instance : True := trivial`, which depends on no axiom; every run had ended | 2026-11-17, before any check of the record | none on the runs; `check.sh` fixed, refrozen ([amendment 8][a8]) |
| The completion's memory stages, rerun as MEMD2 and MEMI2 | the machine's memory peaks were kept only in the record attempt 2 never wrote | before the record was written | the memory check (passed) |
| The floats' kernel pinned (OpenBLAS SkylakeX) | byte comparisons of reported floats depend on the CPU | before the completion ([amendment 8][a8]) | none on stage M: ngspice does not use numpy, and no `PREDICTED.json` was computed |
| The rehearsal's zero-amplitude check failed ([amendment 9][a9]): FIRE dates up to 0.358 µs apart (tolerance 0.1 µs) | the check tests `xtrtol=7`, the solver setting of the device model's runs | after the record, before `BEFORE_M.md` | none under the injected model, which has no XSPICE source; it blocks any run under the device model; `all_checks_passed` stays false |
| [Amendment 10][a10]: `BEFORE_M.md`'s caps are upper bounds; limits computed at each stage | amendment 5 has the caps use the rehearsal's limits; the frozen code uses 1.3 times the expected cost | before `BEFORE_M.md` | none: it records the 660 s limit |
| Machine `b`'s numpy reinstalled, and its remote URL set | its RECORD differed (script shebang); its remote's letter case | before its inventory; before its launch | none |
| Machine `b` restarted before its launch (boot 14:36:37, inventory 14:11:18) | not known | before any run on `b` | none: only the boot differed from the inventory; launched by the owner's decision, the boot recorded at launch |
| Machine `b` launched (14:54:45) before the coordinator's hold on it arrived | the hold arrived after the launch | at its launch | none: the owner lifted the hold; nothing was relaunched |
| Restarts after the stage: `a` at 16:03:27, `b` at 15:42:22 and 16:09:36 | not known | after every run had ended | none |
| Stage M collected by [`collect_with_links.py`][collector] ([amendment 11][a11]) | the kit's `collect` refused the links left by the stopped decks | after stage M | none: every file copied byte for byte, the links recorded as text; the kit's partial copy of 17 files of `a` kept, not used |

## 2. Stage M as recorded

Protocol [`STAGE_M.md`][stage] (governing protocol `PREDICTION.md`), runs [`STAGE_M_RUNS.json`][runs], manifest
[`CAMPAIGN_M.json`][manifest], attempt marker [`RUN_ATTEMPT_M.json`][marker], record before stage M
[`BEFORE_M.md`][before]. Each deck limited to 660 s.

| Seed | Machine | `cal-on` | `cal-off` |
|---|---|---|---|
| 7501 | a | limit, 660 s | complete, 578 s |
| 7502 | a | limit, 660 s | complete, 576 s |
| 7503 | a | limit, 660 s | complete, 568 s |
| 7504 | a | limit, 660 s | complete, 574 s |
| 7505 | a | limit, 660 s | complete, 568 s |
| 7506 | a | limit, 660 s | complete, 595 s |
| 7507 | b | limit, 660 s | complete, 590 s |
| 7508 | b | limit, 660 s | complete, 577 s |
| 7509 | b | limit, 660 s | complete, 551 s |
| 7510 | b | limit, 660 s | complete, 563 s |
| 7511 | b | limit, 660 s | limit, 660 s |
| 7512 | b | limit, 660 s | complete, 572 s |

"limit" is the kit's `time-limit-never-rerun`: missing, never rerun. Both machines' `STATE.json` read
`ended-with-failed-or-lost-runs`.

| Machine | Launch (UTC) | Claim | `uptime -s` at start and end (UTC) |
|---|---|---|---|
| a | 2026-11-17 14:41:50 | `owner-launch/protocol-05c84161…/a` at `d44ba21` | 12:25:44, 12:25:44 |
| b | 2026-11-17 14:54:45 | `owner-launch/protocol-05c84161…/b` at `43265ef` | 14:36:37, 14:36:37 |

**Evidence.** Each machine's evidence folder was collected once by [`collect_with_links.py`][collector] (SHA-256
`e3b13277ff04bb0d0eb42321efb143e38d6e874de3eb99c0b81b7a2d1cbdcab2`, reviewed as a draft at [`d073110`][collector-draft]); the
links left by the stopped decks (`evidence/pdk -> /home/user/campaign/pdk`) are recorded as text.

| Machine | Files collected | Links recorded | On the campaign branch | On an evidence branch | `COLLECTED.json` SHA-256 |
|---|---|---|---|---|---|
| a | 90 | 6 | [`evidence/M-a`][ev-a] (commit `d7f390d`), without the waveforms of 10 MB and more | those 6 waveforms, [`evidence/…-stage-M-a`][evb-a] (`3b26d62`) | `3ab4d690c192be659ca2017d7293185803dee531e901cb454c6c393ef8c4e8c0` |
| b | 86 | 7 | [`evidence/M-b`][ev-b] (commit `639d504`), without the waveforms of 10 MB and more | the whole collection, its 5 such waveforms included, [`evidence/…-stage-M-b`][evb-b] (`158439e`) | `37cc962674827ac91b56e4b259c942672bf4abbd9afacf4695020009717ea752` |

Each folder's `ON_EVIDENCE_BRANCH.json` names that branch, its commit and the files that are only there. Both `COLLECTED.json` read the
kit status `ended-with-failed-or-lost-runs` and the collector's SHA-256 above.

## 3. What was not run

`PREDICTED.json`, the kernel gate on a prediction (`gate4.py`), and the stages Q, N1, N2 and N3. By
[`PREDICTION.md`][prediction] ("Measures, each cell alone in its slot"), an instance is measured when both its
calibration runs count; otherwise it is not measured, has no prediction, gets no network run and enters no claim.
No instance was measured.

## 4. References

The campaign's files are pinned to the campaign branch at `639d504`; the rehearsal's to the work branch.

- The frozen implementation: commit [`093995b`][frozen] (tree `0b2a3a7`); the rehearsal's runs used [`3156ee4`][runs-commit].
- The rehearsal's record: [`REHEARSAL.json`][rehearsal] (SHA-256 `b5486033e64d00e30b6279edd3f0c902a5c08cbe6f0e778990a9cfea4fd1032c`).
- The inventories: [`INVENTORY_a.json`][inv-a], [`INVENTORY_b.json`][inv-b].

[prediction]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/PREDICTION.md
[a1]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/AMENDMENT_1.md
[a2]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/AMENDMENT_2.md
[a3]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/AMENDMENT_3.md
[a4]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/AMENDMENT_4.md
[a5]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/AMENDMENT_5.md
[a6]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/AMENDMENT_6.md
[a7]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/AMENDMENT_7.md
[a8]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/AMENDMENT_8.md
[a9]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/AMENDMENT_9.md
[a10]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/AMENDMENT_10.md
[a11]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/AMENDMENT_11.md
[noise-report]: https://github.com/HevisNico/kernel-R/blob/fd25955adcdcb85b874c1ba38c3891a7411410af/research/network-noise-study/validation/REPORT_A2.md
[run1]: https://github.com/HevisNico/kernel-R/blob/05bfd2824afd35a9070d971223a78b505afea3da/research/learned-dnf-circuit-campaign-4/rehearsal/run-1-interrupted/NOTE.md
[run2]: https://github.com/HevisNico/kernel-R/blob/6ef8cb55d8d22b2bb492952b73d68df5ae9459dd/research/learned-dnf-circuit-campaign-4/rehearsal/run-2/NOTE.md
[run2c]: https://github.com/HevisNico/kernel-R/blob/1e74a71a82a842c60b0418e30c7fc970c9270155/research/learned-dnf-circuit-campaign-4/rehearsal/run-2-completion/NOTE.md
[rehearsal]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/REHEARSAL.json
[collector]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/evidence/collect_with_links.py
[collector-draft]: https://github.com/HevisNico/kernel-R/blob/d073110a500236dae43513af816f2a031b8a5be9/research/learned-dnf-circuit-campaign-4/drafts/collect_with_links.py
[stage]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/STAGE_M.md
[runs]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/STAGE_M_RUNS.json
[manifest]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/CAMPAIGN_M.json
[marker]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/RUN_ATTEMPT_M.json
[before]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/BEFORE_M.md
[inv-a]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/INVENTORY_a.json
[inv-b]: https://github.com/HevisNico/kernel-R/blob/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/INVENTORY_b.json
[ev-a]: https://github.com/HevisNico/kernel-R/tree/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/evidence/M-a
[ev-b]: https://github.com/HevisNico/kernel-R/tree/639d504a173d037a16d7407548c84c1ce6c6fadf/research/learned-dnf-circuit-campaign-4/evidence/M-b
[evb-a]: https://github.com/HevisNico/kernel-R/tree/3b26d624f0860e81694df657e6135fc8d732646a/research/learned-dnf-circuit-campaign-4/evidence/M-a
[evb-b]: https://github.com/HevisNico/kernel-R/tree/158439ee3ac4c7639e607ea7d09655c58a8ffa38/research/learned-dnf-circuit-campaign-4/evidence/M-b
[frozen]: https://github.com/HevisNico/kernel-R/tree/093995b6f8568889dc53d0650be7a7c9d28092e4
[runs-commit]: https://github.com/HevisNico/kernel-R/tree/3156ee40ab35dea396b6fa8785177b84b7667c76
