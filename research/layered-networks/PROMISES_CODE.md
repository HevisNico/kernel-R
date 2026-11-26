# PREDICTION_CANDIDATE.md's promises against the code (audit point 9)

One line per promise the text makes about what the campaign's code does: the function that keeps it, and the test
that exercises it. **(a)** is tests/equiv_campaign.py (dev/equiv/EQUIV_A.json, the chain's steps against
`campaign.py steps`). **(b)** is tests/equiv_b.py (dev/equiv/EQUIV_B.json: campaign.py's roots against the chain's,
and analysis.py against analyze10). **(c)** is tests/test_campaign.py (dev/equiv/TEST_C.json), named by its case.
A function is campaign.py's unless it says `analysis.` or names another file. "Measuring code" is the code that was
left alone (stage_d6, fit3, indeck_noise4, controls4, compare_d2, sealpush2, check_duplicate): its own older tests
are named where they exist.

**Two promises have no code.** They are marked **GAP**, and listed for the owner's decision in CAMPAIGN_DIFFERENCES.md.
The feature freeze forbids writing that code without that decision.

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
| 2 | Secondary control: layered_recognition_at (layered_inverters_chained for G1, G3) on the stage-N traces, per instance | **GAP: no code.** Neither analyze10 nor analysis.py runs it; leancal2.py is a dev tool, not called by any driver | none |
| 3 | Sizes of the yield-lot rule | not in the driver: plan_split3.py and draw_seeds.py write the plans; check_plan refuses a plan that differs from the template | test_draw_split; (c) refusals |
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
| 7 | RESULTS.json: the secondary Lean control per instance | **GAP**, as in §2 above | none |
| 7 | Frozen tools: Lean 4.35.0 by its real binary, ngspice 42, Python 3.13.18, numpy 2.3.5, SKY130 | set_env (envcheck_layered4 checks at launch and every run); analysis.kernel_library (pinned Lean) | (c) refusals; test_envcheck4 |
| 7 | Machine discipline: jobs detached, foreground waits of ≤ 590 s, uptime -s at start and end, no counted run relaunched | cmd_launch (detached), cmd_wait (≤ 590 s), inventory (INVENTORY_START/END), Instance.step (interrupted, never relaunched) | (c) interrupt_and_resume, crash |
| 7 | Any fix after the freeze is a new freeze commit | campaign mode requires FROZEN_TEMPLATE_SHA256; ENV/RESULT record the driver's and template's sha; analysis campaign mode refuses other roots | (c) refusals, analysis_refuses |
| 8 | Not completed: crash, time limit or cut ends the instance's run at that level; never re-run, never replaced | Instance.step (failed, timeout kills the process group, interrupted on resume); cmd_run | (c) crash, timeout, interrupt_and_resume |
| 8 | Time limits deck 120, inverters 3600, D 7200, seal 120, N 7200, C 300, U 3600, dup 7200 | campaign_template.json time_limits_s, read by load_template; Instance.step | (a) timeouts column; (c) timeout |
| 8 | The counted set is fixed by stage D, nothing after stage N removes an instance | analysis.analyze_root (eligibility and room from D/prediction.json) | (b) analysis |
| 8 | Premise flagged for D4: audited instance (every 6th) runs solo scans; D4* > 0.005 regates the unaudited from their sealed records | steps_chain (solo=1 for d4_audit seeds); analysis.layer_d4 (d4_regate) | (a); (b) NOT1 6220 audited; test_d4_regate |
| 8 | Premise flagged for the leak along the trajectory, the latch delay, the routed walk | **GAP: not computed.** Listed in CAMPAIGN_DIFFERENCES.md | none |
| 8 | Counts side by side: counted, held, refuted, premise flagged, not completed | analysis.layer_counts | (b) analysis |
| 8 | Zero-noise identity (check_noise_identity2) | an environment check, run apart from the driver (tests/check_noise_identity2.py) | its own run before the freeze |
| — | Disk: refuse a launch below 40 GB; hold a step below the 20 GB guard, except the comparisons | cmd_launch; Machine.guard (C exempt, GUARD_EXEMPT.json; held steps in stopped_for_disk) | (c) guard, partial_guard_and_resume |
| — | A resume refuses a changed static environment, mode or template | set_env | (c) refusals |
