# PREDICTION_CANDIDATE.md's promises against the code (audit point 9)

One line per promise the text makes about what the campaign's code does: the function that keeps it, and the test
that exercises it. **(a)** is tests/equiv_campaign.py (dev/equiv/EQUIV_A.json, the chain's steps against
`campaign.py steps`). **(b)** is tests/equiv_b.py (dev/equiv/EQUIV_B.json: campaign.py's roots against the chain's,
and analysis.py against analyze10). **(c)** is tests/test_campaign.py (dev/equiv/TEST_C.json), named by its case.
A function is campaign.py's unless it says `analysis.` or names another file. "Measuring code" is the code that was
left alone (stage_d6, fit3, indeck_noise4, controls4, compare_d2, sealpush2, check_duplicate): its own older tests
are named where they exist.

**Two promises of the review copy have no code in the frozen analysis, by the owner's decision.** They are marked
**DECIDED**. The frozen analysis checks only D4. The other stage-N premises and the Lean recognition control on the
traces belong to the complementary analysis after the campaign, which can only lower counts and reports both
versions. The coordinator's text now says so (CAMPAIGN_DIFFERENCES.md, last section).

| § | Promise | Code | Test |
|---|---|---|---|
| 1 | Each instance is one mismatch draw (setseed S on the whole deck), 27 °C, typical, at the design point | Instance.steps_chain → stage_d6 deck with the template's overlay | (a); (b) input.spice identical |
| 2 | Every R cell is measured alone, fitted and gated at K0 and K3 by fit3, with the one-port rule for the either cell | steps_chain D (stage_d6 run `rule=one-port`, the template's testError_rule) | (a); (b) D records identical; test_fit3 |
| 2 | Every inverter is gated in the network deck itself (indeck, K0, K3, StateBound) | steps_chain inverters (indeck_noise4) and the chain's stop when K3_BUDGET is not ok (Instance.chain) | (a); (b) |
| 2 | The kernel is the last word on Cell.Valid | build_kernel; LAYERED_KERNEL_BUILD in every step's environment; analysis.kernel_library | (c) kernel_mirror_disagreement |
| 2 | The prediction (words, outputs on 2^m patterns, cell bits, skew silence, eligibility, room) is written and sealed with the ENV hash included | steps_chain D and seal (stage_d6 seal); set_env, which sets LAYERED_ENV_SHA256 | (a); (b) seal contents identical |
| 2a | Each prediction is sealed before its own stage N | Instance.chain: the order deck → … → seal → sealpush → N0 | (a); (c) no_pushed_seal |
| 2b | The seal is pushed in one append-only commit on evidence/combined-seals-K<nn> (SEALS.txt line and seals/<inst>/) before stage N, and stage N starts only after the push | steps_chain sealpush (sealpush2 push, under Machine.seal_lock); Instance.round refuses N without a pushed seal | (c) no_pushed_seal, home_run; test_sealpush |
| 2b | A second seal of the same instance is refused | sealpush2 (measuring code) | (c) second_seal |
| 2b | Stage N refuses to start without the seal-log commit and records it in every stage-N record | Instance.round (SEAL_LOG.json, `refused` with no pushed seal); steps_round passes seal_log= and seal_branch= to controls4 | (c) no_pushed_seal; (b) the seal_log key of noisy_record.json |
| 2b | A duplicate fetches the log branch by name, checks the commit is on it, the SEALS.txt line equals the seal's sha256, the seal verifies, then writes its own comparison | wait_for_seal, probe, seal_log_line, fetch_seal, remote_duplicate | (c) home_run, differing_duplicate; (b) duplicates |
| 2b | The push time is GitHub's; the coordinator checks every log against the stage-N start times | analysis.seal_log, analysis.layer_stage_n_seal_log (times=github) | (b) analysis on the roots |
| 2c | The analysis regenerates every prediction from the stage-D records alone, byte-identical to its seal; a mismatch is a defect with no counted prediction | analysis.regenerate, analysis.layer_seals (seal_defects) | (b) analysis on the roots; test_analyze10 |
| 2 | K0: one noiseless run on every eligible instance, compared directly | Instance.round(0) (controls4 stagen 0, compare_d2 noiseless) | (a); (b) comparisons identical |
| 2 | K3: three noisy rounds on every instance with room, noise seed 10·S + n | Instance.chain returns room_K3; cmd_run starts rounds 1–3 as jobs; steps_round | (a); (b) |
| 2 | One difference refutes; no prediction, no claim (observed only, never "predicted to fail") | compare_d2 (measuring code); analysis.analyze_root (observed_only), analysis.layer_counts | (b) analysis; test_analyze10 |
| 2 | K3: one completed refuting round refutes, even beside a round that did not complete (audit A1) | analysis.analyze_root (K3), analysis.completed_rounds | (c) analysis_tampered (A1) |
| 2c | The counted set and the gates are read from the sealed prediction; a D/prediction.json differing from its seal is a defect (audit A2) | analysis.analyze_root (seal/<inst>.json), analysis.layer_seals | (c) analysis_tampered (A2) |
| 2 | Secondary control: layered_recognition_at (layered_inverters_chained for G1, G3) on the stage-N traces, per instance | **DECIDED: not in the frozen analysis**; the complementary analysis after the campaign | none |
| 3 | Sizes of the yield-lot rule (60/32/37, final by the owner's decision; the rehearsal 6/6/6) | pinned in the analysis: analysis.DRAW_SIZES and DRAW_SIZES_REHEARSAL; analysis.check_draw refuses a DRAW_ANNOUNCE.txt whose sizes are not the mode's and recomputes the draw at those sizes; plan_split3.py and draw_seeds.py write the plans; the driver's check_plan refuses a plan that differs from the template | (c) draw_plans_command (both sizes), draw_canonical; independent plans_command_6_6_6, plans_command_60_32_37; no dedicated test of an announce with other sizes |
| 4 | The verdict words and thresholds count held instances (counted, completed, agreeing, no premise flagged) | analysis.word, analysis.layer_thresholds, analysis.layer_counts | (b) analysis; test_analyze10 |
| 4 | All three groups together are established only if each group is | analysis.layer_counts (family_of) | (b) analysis |
| 5 | Noisy rounds run in parallel after N0, within 4 cores | Budget(cores 4), cmd_run's job scheduler; inverters take m cores | (a) cores column; (c) partial_guard_and_resume |
| 5 | A job not started is "not run", listed with its seed, never replaced | Instance.step marks running before start; analysis.never_run | (c) interrupt_and_resume, partial_guard_and_resume |
| 5a | Noise off in D and N0; rounds 1–3 with noise seeds 10·S + n | steps_round (round number passed to controls4) | (a); (b) |
| 6 | U: one untrained run per group on its first eligible instance, no R-cell output fires | untrained (after all the group's chains, guarded, no core budget) | (a); (c) partial_guard_and_resume (U held, then ok); (b) |
| 6 | S: one skew slot per both cell in every stage-N run, the cell silent | controls4 (measuring code); analysis.analyze_root controls S | (b) analysis |
| 6 | Duplicate on a second machine, judged by check_duplicate.py: input.spice identical, records identical except cost and wall, trace.raw identical except Date: (digests when deleted), session.log except wall lines | remote_duplicate; after_comparison (keep trace.raw when a comparison does not agree, and for the duplicates' originals); analysis.layer_duplicates | (c) differing_duplicate, home_run; (b) duplicates |
| 6 | A duplicate failure is an environment defect; no instance is dropped | analysis.layer_duplicates (reported, the instance kept) | (c) differing_duplicate |
| 7 | One analysis, run once and checked byte-identical on a second run | analysis.main; two runs compared | (b) two analysis runs byte-identical |
| 7 | RESULTS.json: counted, verdicts, refuting differences, observed-only, failed and not-run, controls U, S, duplicate, max-rule counts, seal regeneration, ENV per machine, costs | analysis.layer_counts, analyze_root, env_section, layer_seals, max_rule | (b) analysis |
| 7 | RESULTS.json: the secondary Lean control per instance | **DECIDED**, as in §2 above | none |
| 7 | Frozen tools: Lean 4.35.0 by its real binary, ngspice 42, Python 3.13.18, numpy 2.3.5, SKY130 | set_env (envcheck_layered4 checks at launch and every run); analysis.kernel_library (pinned Lean) | (c) refusals; test_envcheck4 |
| 7 | Machine discipline: jobs detached, foreground waits of ≤ 590 s, uptime -s at start and end, no counted run relaunched | cmd_launch and cmd_resume (detached), cmd_wait (≤ 590 s), inventory (INVENTORY_START/END), Instance.step (interrupted, never relaunched) | (c) interrupt_and_resume, sigterm_driver_only, crash |
| 7 | No child outlives its driver unnoticed (audit D2) | on_signal (kills the children's groups), cmd_run and cmd_resume refuse while ngspice or a process on OUTROOT runs (processes_on) | (c) sigterm_driver_only, sigkill_driver_only |
| 8 | No silent stop: a chain that stops leaves a status entry with its reason (audit D3) | Instance.chain (D refused when K3_BUDGET is not ok), Instance.round (N refused without a seal) | (c) k3_budget_stop, no_pushed_seal |
| 5 | A machine's instance results never depend on another machine (audit D4) | cmd_run: RESULT_INSTANCES.json, SHA256SUMS.instances, INSTANCES_DONE before remote_duplicate | (c) home_run, differing_duplicate (the files present) |
| 7 | The kernel build records the real Lean binary (audit D7) | build_kernel (E3.lean_resolution) | (c) every run (kernel_build/KERNEL_BUILD.json) |
| 7 | Any fix after the freeze is a new freeze commit | campaign mode requires FROZEN_TEMPLATE_SHA256 and every FREEZE_PINS file matching, the tree clean (pins_check, pins_refusal); ENV/RESULT record the driver's and template's sha; analysis campaign mode does the same pins check, refuses other roots and refuses a root whose driver checked another FREEZE_PINS.json (TEMPLATE_CHECK.json pins.pins_sha256) | (c) refusals, pins, analysis_refuses |
| 7 | One analysis with no free argument in campaign and rehearsal modes: the pinned thresholds, times from GitHub only (lsremote removed, B7), the frozen noise tree's checker (audit A3) | analysis.main (strict = mode != test) | (c) analysis_refuses (times=bare refused), pins (analysis refusals) |
| 8 | Not completed: a crash or a time limit ends the instance's run at that level; never re-run, never replaced. There is no cut: by the owner's decision a cost overrun lengthens the window | Instance.step (failed, timeout kills the process group, interrupted on resume); cmd_run; analysis.layer_counts (not completed, not_run) | (c) crash, timeout, interrupt_and_resume |
| 8 | Time limits deck 120, inverters 3600, D 7200, seal 120, N 7200, C 300, U 3600, dup 7200 | campaign_template.json time_limits_s, read by load_template; Instance.step | (a) timeouts column; (c) timeout |
| 8 | The counted set is fixed by stage D, nothing after stage N removes an instance | analysis.analyze_root (eligibility and room from the sealed prediction, seal/<inst>.json, audit A2) | (b) analysis |
| 8 | Premise flagged for D4: audited instance (every 6th) runs solo scans; D4* > 0.005 regates the unaudited from their sealed records | steps_chain (solo=1 for d4_audit seeds); analysis.layer_d4 (d4_regate) | (a); (b) NOT1 6220 audited; test_d4_regate |
| 8 | Premise flagged for the leak along the trajectory, the latch delay, the routed walk | **DECIDED: assumed in the frozen analysis**; the complementary analysis checks them on the trace extracts | none |
| 8 | Counts side by side: counted, held, refuted (with refuted_stopped_by_own_check), premise flagged, not completed, not_run, at the pinned sizes | analysis.layer_counts(res, sizes), analysis.ROWS | (b) analysis (RECORDS_0b33340d.md); (c) analysis_d8_not_run, analysis_own_check |
| 8 | Zero-noise identity (check_noise_identity2) | an environment check, run apart from the driver (tests/check_noise_identity2.py) | its own run before the freeze |
| — | Disk: refuse a launch below 40 GB; hold a step below the 20 GB guard, except the comparisons | cmd_launch; Machine.guard (C exempt, GUARD_EXEMPT.json; held steps in stopped_for_disk) | (c) guard, partial_guard_and_resume |
| — | A resume refuses a changed static environment, mode or template | set_env | (c) refusals |

## Promises made on 2026-11-27 (analysis.py format layered-campaign-analysis/2)

The independent tests are tests/test_analysis_defects.py (dev/equiv/DEFECTS_R_AFTER.json, 51 of 51 at 8bac22cc),
named by case. (c) is test_campaign.py's run4 (dev/equiv/TEST_C_run4.json, 27 of 27). "No offline test" marks a
check that reads GitHub only in campaign and rehearsal modes; the test mode skips it, so it is exercised first by the
rehearsal.

| Promise | Code | Test |
|---|---|---|
| Every planned instance has a state; a planned instance that never started is a not_run row, with sealed_in_log; a machine with no root or an unfinished root is in NOTICE (D8) | analysis.expected_plans, analysis.match_plan, analysis.layer_seals, analysis.layer_counts (not_run) | (c) analysis_d8_not_run; independent planned_seed_not_started, planned_machine_no_root, draw_machine_without_root |
| Repeated roots: a root path given twice, two roots on one machine, a home instance in two roots are refused (D9) | analysis.main (D9 checks) | (c) analysis_d9_copies; independent same_root_30_times, draw_same_machine_twice, same_machine_two_paths, home_instance_twice, draw_duplicate_machine_only |
| Manifests verified: every SHA256SUMS* line of every root is checked before anything is read; a read under no verified line refuses (D10, B8) | analysis.Root (walk, covered, file), analysis.UNMANIFESTED | (c) analysis_d10_manifest, analysis_hardening (B8); independent listed_file_missing, k05_alone, k05_with_dupx |
| A refutation is kept with a defective seal (owner rule A1(ii)) | analysis.seal_defect, analysis.layer_counts | (c) analysis_tampered, analysis_hardening (B1/B2) |
| A run stopped by its own check (status "failed: " not a simulator end) is refuted, refuted_stopped_by_own_check with its round and status; read from N<n>/noisy_record.json when there is no comparison (A2, the audit's defect 1) | analysis.own_check, analysis.analyze_root, analysis.SIMULATOR_END | (c) analysis_own_check (a real driver run); independent round_own_check_failed, round_simulator_ended |
| A stopped machine: a refutation that compare_d2 reproduces, with files matching their status outputs and a verifying seal, counts though the manifest is not final (option ii) | analysis.partial_instance | (c) analysis_hardening (the partial machine); independent stopped_mid_instance |
| The draw recomputed in full from public inputs: the round from the announce's push time, the BLS signature against the pinned key, one canonical value (64 lowercase hex = sha256 of the exactly 48-byte signature), integer rounds, the seeds at the pinned group order, byte for byte (B16, X1, X2, N6) | analysis.check_draw; draw_seeds.canonical_beacon, draw, GROUP_ORDER; beacon_verify.verify, round_after; plan_split.ordered_groups | (c) analysis_hardening (B16, X1, N6), draw_canonical, draw_plans_command; independent standin_* (draw, seed, round, signature, beacon writings, pads, flip, other round), beacon_*, verify_*, sizes_permutations, plans_command_* |
| The announce cannot be redone: no force push or deletion of the announce branch, its oldest activity item the branch_creation of the announce commit (the audit's defect 2) | analysis.announce_time, analysis.announce_on_github, analysis.parse_announce | (c) analysis_announce (recorded items); independent standin_activity_clean, standin_activity_redone, standin_activity_force_push |
| The freeze before the announce: the announce later than GitHub's push of the frozen commit on FREEZE_BRANCH (N1) | analysis.freeze_time, analysis.check_draw | no offline test |
| No instance sealed before the draw: no drawn instance has a SEALS.txt line pushed before its round's time (N3) | analysis.main (N3, strict modes) | no offline test |
| The rehearsal's seeds: the campaign's list holds the rehearsal's 18 seeds and their noise seeds 10 S + 0..3, the rehearsal draw checked in full, its announce earlier; the list a superset of the freeze's, at most 20 % of the range (N5) | analysis.check_rehearsal_seeds, analysis.check_draw; draw_seeds.excluded_fraction, MAX_EXCLUDED_FRACTION | (c) analysis_hardening (seed missing, noise seed missing, full list, N5 wide list); independent rehearsal_full_list, rehearsal_seed_missing, rehearsal_noise_missing, rehearsal_announce_later, standin_excluded_not_superset, standin_excluded_sha_differs; dev/freeze/final (option A, step 3) |
| The sizes pinned: 60/32/37 (campaign), 6/6/6 (rehearsal) | analysis.DRAW_SIZES, DRAW_SIZES_REHEARSAL, check_draw | (c) draw_plans_command; no dedicated test of an announce with other sizes |
| Comparisons recomputed: compare_d2 rerun on every comparison, byte-identical (B4) | analysis.verify_comparison | (c) analysis_hardening (B4); independent one_byte_in_comparison |
| Exactly one seal line per instance in its machine's log, with the seal's sha256 (B3) | analysis.seal_log | (b) analysis on the roots (one line each); no test of two lines |
| Times from GitHub only in campaign and rehearsal modes; the activity saved in OUTDIR/activity/ (B7) | analysis.main, analysis.push_times, analysis.activity_items | (c) analysis_refuses (times=bare refused), github_times; RECORDS_0b33340d.md (times=github on the four run2 roots) |
| The expected controls: U per group and S per both cell present and passed, listed against the plans (A7) | analysis.layer_duplicates (expected_controls, home_instances_without_root) | (c) analysis_hardening (A7) |
