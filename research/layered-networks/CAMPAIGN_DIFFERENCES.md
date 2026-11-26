# campaign.py and analysis.py against the chain they replace (campaign_run17 and analyze10), and against PREDICTION §8

The places where campaign.py knowingly differs from campaign_run17 (audit point 3), and where analysis.py differs from
analyze10. Each item says whether it changes a step, a record, or only a driver file.

## campaign.py vs campaign_run17

**The template and the plan** (driver files only; no step changes, test (a)):
1. **One template, campaign_template.json** (sha 02af33e0…). The chain's defaults are explicit keys: time_limits_s,
   which are PREDICTION §8's values (deck 120, inverters 3600, D 7200, seal 120, N 7200, C 300, U 3600, dup 7200);
   cores 4 (the chain's `jobs=4`); seal_push_delay_s 2. The template keys described in words (kernel, trace_extract,
   driver, disk_guard_exempt) are dropped: campaign.py does those things, and there are no others.
2. **The template is an argument, with a mode.** `campaign` requires the frozen sha, and `test` refuses it. ENV.json
   and RESULT.json get a `campaign` key (driver sha256, template sha256, mode). status.json gets `mode`, and DONE
   carries the mode after the time. The chain had no mode.
3. **Stricter plan checks.**
   - groups[g] must have exactly spec, seeds and d4_audit (no timeout_s).
   - controls must be {"duplicate": {}}: no same-machine duplicate (DUP_). The chain supported one, and campaign plans
     never used it.
   - remote_duplicates entries must have exactly plan_split3's keys.
   - U_groups must name groups of the plan.
4. **Not supported, refused:** save_ref_round, steps_until, stagen other than controls4, stage_d_script other than
   stage_d6, dry seals (allow_dry_seal must be false and seal_push.dry false).
5. **A refusal is a `Refused` message.** The chain raised AssertionError on a tree at the wrong commit or a dirty tree.

**The run** (same steps, argv, cwd, environment, outputs and time limits: test (a)):

6. **A step that is not done is checked before the guard.** A failed, timed-out, interrupted or refused step below
   the guard is not listed as held. The chain's guard ran first and listed it as held although it would never run.
7. **The end of the run is written once.**
   - RESULT.json has the chain's final keys plus `campaign`.
   - The top-level SHA256SUMS is written once, with the chain's final list.
   - There is no SHA256SUMS.pre_post_writes (an artifact of the chain's layering).
8. **A resume also refuses a change of mode or template** (ENV.json `campaign`), besides a changed static
   environment.
9. **`steps`, the no-run mode,** is a new command. It runs nothing (the equivalence test (a) needs it).
10. **Timeout reasons** print the limit with `:g` ("more than 7200 s", as before for integer limits).

**Unchanged, and noted because the audit asked:**
- **On SIGTERM**, neither driver kills its running children: each step runs in its own session. In test (c) the
  interruption therefore kills the child's process group as well, as a machine stop would.
- **U takes no core of the budget** in either driver, while the remote duplicate's N0 takes one.

## analysis.py vs analyze10
1. **Format and hashes:** format layered-campaign-analysis/1; analysis_sha256 in place of analyze3…10_sha256.
2. **New keys:** `mode`, `root_drivers` (each root's driver and template sha256 and mode, from ENV.json) and
   `roots_sha256sums` (before and after).
3. **Refusals:**
   - campaign mode refuses a root not run by this campaign.py on the frozen template in campaign mode;
   - an OUTDIR inside a root is refused;
   - a changed root is refused;
   - a lean binary that is not the pinned one is refused.
4. **The rest is byte-identical to analyze10.** Equivalence (b) shows it on the final dry run's 8 roots and e2e17's
   3 roots.

## Where the chain or the analysis and PREDICTION §8 differ (the text wins)
- **Time limits, the not-completed rule, "interrupted" and no relaunch:** the same in the text and in campaign.py.
- **"Premise flagged" for the stage-N premises (§8 failure rule).** The text says an instance whose letters, bits and
  outputs all agree is premise-flagged at that level, not counted towards established, when a premise observed in
  stage N is false: the leak along the trajectory, the latch delay, the routed walk, D4. analyze10, and so
  analysis.py, flags D4 only. The other three are not computed by any analysis: the data for them is in the trace
  extracts (POSTCHECK_DATA.md). **This is a gap between the text and the analysis.** Closing it is new analysis code,
  which the feature freeze forbids without the owner's decision. It is listed here for that decision and not done.
- **The secondary Lean control (§2, and in §7's list of RESULTS.json contents).** The text says the kernel's
  recognition theorem (`layered_recognition_at`, and `layered_inverters_chained` for G1 and G3) is applied to the
  stage-N traces and reported per instance. No driver and no analysis does it: not analyze10, not analysis.py. Only
  the dev tool leancal2.py touches that theorem. **This is a second gap between the text and the code.** It is
  listed for the owner's decision and not done: either new analysis code (forbidden by the freeze without that
  decision), or an amendment that drops the promise.
- **§7's "One analysis … analyze8.py"** names the analysis of the review candidate; it is analysis.py now. This needs
  an amendment of the text, not of the code.
