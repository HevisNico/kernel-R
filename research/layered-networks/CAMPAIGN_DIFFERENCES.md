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

**The audit's defect fixes** (on c99c1f70 and 4ec49104; none changes a step's argv, cwd, environment, outputs or
limit: test (a) is rerun on them, identical):

11. **D1, campaign mode and the pins.**
    - Campaign mode refuses unless every file of FREEZE_PINS.json matches its sha256 in the driver's own tree, the
      tree is clean, and campaign.py, analysis.py and campaign_template.json are among the pins.
    - The check is recorded as `pins` in TEMPLATE_CHECK.json, in both modes.
    - A tree is clean only with no changed tracked file and no untracked .py or .json. This applies to the kit and
      noise trees too, in both modes. The chain used --untracked-files=no.
    - Until the next freeze pins campaign.py and analysis.py, campaign mode refuses on this branch, as it should.
12. **D2, the children.**
    - On SIGTERM or SIGINT the driver kills its running children's process groups, logs them in SIGNALS.json and
      exits. The chain left them running.
    - The child registry's lock is re-entrant (RLock): the handler runs in the main thread, which may hold it while
      starting a child (remote_duplicate).
    - `run` and the new `resume` refuse while ngspice runs, while the OUTROOT's driver is alive, or while another
      process names the OUTROOT.
   - A zombie ngspice (state Z: killed, not yet reaped) is not counted as running. Test (c) first failed on it: a
     killed ngspice stays a zombie for a few seconds, and the refusal counted it (fixed in 3e90a3de; (c) all pass).
13. **D2, a detached resume.** `resume` is `run` started detached, as launch does. It writes DRIVER_PID and
    DRIVER_PIDS.log, and moves an earlier DONE aside to DONE.before_resume_<k>. This follows the rule of detached jobs
    and waits of at most 590 s.
14. **D3, no silent stop.** When inverters is done but inv/K3_BUDGET.json is not ok, D is recorded "refused" with the
    reason: in status.json the entry is under the step name `D` (status `refused`, why "inv/K3_BUDGET.json is not ok
    (the inverters' K3 budget)"), although D itself never ran. The chain returned without an entry. With today's indeck_noise4, which exits 1 when not ok, inverters is
    "failed" first; the refused entry covers a K3_BUDGET that says not ok after an exit 0. Test (c) makes one with a
    stub tree.
15. **D4, the instances' result before the duplicates.**
    - Once every chain, round and U has ended, and before any remote duplicate waits, the driver writes
      RESULT_INSTANCES.json (RESULT.json's instance part), SHA256SUMS.instances and INSTANCES_DONE. `wait` prints
      INSTANCES_DONE.
    - RESULT.json, the top-level SHA256SUMS (which now also lists those two files) and DONE follow the duplicates, as
      before.
    - Both cases are covered. While a duplicate waits up to 6 h for another machine's seal, the instance results are
      already final and hashed. A machine with no duplicate, or whose duplicates are done, writes DONE right after,
      and RESULT.json repeats the same instance part.
16. **D7, the kernel build** records the Lean binary resolved by envcheck's resolver (E3.lean_resolution, which
    envcheck_layered4 uses): its path, its sha256 and how it was resolved. It also compiles with that binary. The
    chain hashed realpath(which("lean")), which is elan's proxy on most machines.
17. **D5, D6 (no change of code, stated):** U takes no core of the budget (kept for equivalence). Nothing is killed
    when the window ends: only time_limits_s stops a step. The start order is the plan's submission order as the
    cores free, not the draw order.

**A known cosmetic limit (no code change, by the coordinator's decision):** `campaign.py status OUTROOT` lists the
instances' status.json files only, so it prints nothing for a root that holds only a remote duplicate (K06 in the
test phase). The facts are recorded all the same: DUPX_<inst>/duplicate_here.json (the duplicate's run, exit and
cost), DUPX_<inst>/seal_wait.json (the seal found, its commit and line), DONE, and RESULT.json.

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
4. **The audit's defect fixes (A1–A6):**
   - **A1:** at K3, refuted if ANY completed sealed comparison of a noisy round refutes; held only if all three
     completed and agree; otherwise not completed. analyze10 counted K3 only when all three rounds had completed, so
     it would have lost a refutation next to a timed-out round. The seal-log layers check only the completed rounds of
     a counted level.
   - **A2:** eligibility and room are read from the sealed prediction (seal/<inst>.json). A D/prediction.json that
     differs from its seal is a seal defect: the instance is not sealed and not counted.
   - **A3:** campaign mode reads only the pinned thresholds.json, times github or lsremote:LOG only, and controls only
     from the clean noise worktree at the frozen template's noise_commit. The THRESHOLD constant is removed; the
     thresholds are read once, before the first layer.
   - **A4:** the not_sealed rows list each instance with its comparison verdicts (analyze10: names only).
   - **A5:** campaign mode checks FREEZE_PINS.json over its own tree and that the tree is clean (campaign.pins_check).
     It also refuses a root whose driver checked another FREEZE_PINS.json (TEMPLATE_CHECK.json pins.pins_sha256): the
     same campaign.py at another commit, with another pinned list, is not accepted.
   - **A6:** first_failing uses the one step order ORDER, with sealpush in it.
   - **The seal log's push times (sealpush.times, source github; fixed in 2011058e, found by equivalence (b)):**
     GitHub records the first push of a log branch as a branch creation, and that event counts as its push. Only
     the activity types push and branch_creation give a push time; a force push or a branch deletion never does.
     Whether such an event on a log branch should itself make a seal defect is left to the complementary analysis
     (text only, no code).
   - A new top-level key, `pins`.
5. **The rest is byte-identical to analyze10.** Equivalence (b) shows it on the final dry run's 8 roots and e2e17's
   3 roots, where none of A1, A2 and A4 applies.

## Where the chain or the analysis and PREDICTION §8 differ (the text wins)
- **Time limits, the not-completed rule, "interrupted" and no relaunch:** the same in the text and in campaign.py.
- **"Premise flagged" for the stage-N premises (§8 failure rule). DECIDED by the owner, no code.** The frozen analysis
  checks only the D4 premise; the leak along the trajectory, the latch delay and the routed walk are assumed. A
  complementary analysis after the campaign checks them on the trace extracts (POSTCHECK_DATA.md). It can only lower
  counts, never remove a refutation, and both versions of every count are reported. The coordinator's text now says
  this.
- **The secondary Lean control (§2, and §7's list of RESULTS.json contents). DECIDED by the owner, no code.** The
  Lean recognition control on the stage-N traces (`layered_recognition_at`, `layered_inverters_chained`) is not part
  of the frozen analysis. It belongs to the complementary analysis after the campaign. The coordinator's text now
  says this; the review copy 0a025464 is outdated on this point.
- **§7's "One analysis … analyze8.py"** names the analysis of the review candidate; it is analysis.py now. This needs
  an amendment of the text, not of the code.

- analysis.py, refuted_stopped_by_own_check: the C<n> label names round n's comparison slot; the run that stopped is
  N<n> (the driver never runs C<n> after a failed N<n>).
- analysis.py, check_rehearsal_seeds: its refusal "(the second scan must read the rehearsal)" refers to the campaign
  list's three-step construction in FREEZE.txt (the second scan's output PLUS the rehearsal's seeds and noise seeds,
  added by step 1, then checked by step 3), not to rerunning the scan.
