# Rehearsal of campaign_run13 from the pinned template (item 4, 2026-11-26). Development only; nothing pushed

## Setup
- **Trees.**
  - stage-D tree: a fresh worktree at a2ea377f, the local integration commit that holds TEMPLATE_CAMPAIGN.json and
    campaign_run13.
  - kit tree: d599300d; noise tree: 458bc7a6. Both are clean worktrees, found by campaign_run13 from the commits
    alone. Neither plan names a path.
- **Plans.** plan_split2.py, m = 8, on the D4-check draw (NOT1 6212, 6213, 6217, 6218, 6219, 6220: yield-lot seeds,
  excluded from the campaign).
  - The template was TEMPLATE_REHEARSAL.json, sha c12e7151…. It is the pinned template (c812cc28…) with seal_push.remote
    set to a local bare repository carrying the pre-receive and post-receive hooks of the earlier checks.
  - campaign_run13 accepted it as a rehearsal (TEMPLATE_CHECK.json: rehearsal true, the difference recorded).
  - The same plan against the pinned template is refused, on seal_push.
- **Instances.**
  - **K01** = NOT1_6220, audited (d4_audit: stage D with its own solo scans).
  - **K02** = NOT1_6212. It carries the group's U control and has keep_raw NOT1_6212: the original of the group's remote
    duplicate, which is on K07 and was not run here.

## Results
- **K01** took 759 s and **K02** 536 s, run one after the other on 4 cores. Every step was done:
  - deck, inverters (the noise4 K3 budget), D, seal and sealpush;
  - N0, then N1–N3 (room_K3 on both), and C0–C3, all agreeing.
- **The D4 source.** K01's fit_d.json says "this run's solo scans"; K02's says "calibration.json d4_stage".
- **The seals.** Both were pushed to the local bare repository through its hooks:
  - evidence/combined-seals-K01 is at 414d304 and holds seals/NOT1_6220/;
  - evidence/combined-seals-K02 is at 83ab4a2.
  - K02's U control read its record's seal log from that branch.
- **The trees.** trees.json gives kit d599300d…, noise 458bc7a6… and stage_d_tree a2ea377f….
  - PLAN.json is the resolved plan: the input plus kit_tree and noise_tree. PLAN_INPUT.json is the input, byte for
    byte.
- **analyze8 / analyze9** on out_K01 + out_K02: rc 0, and two analyze9 runs are byte-identical (RESULTS.json
  ede82e96…). The rest of RESULTS.json equals analyze8's. The counts:
  - **K0:** counted 2, held 2 (6220 and 6212); every other row 0.
  - **K3:** counted 2, held 2; every other row 0.
  - **D4\*** = 0.003966, from 6220 (cell c1_0). That is ≤ 0.005, so there is no regate and no flag.
  - The verdict is "held on 2 instances, not established", since 2 is below the thresholds.

## Noted, not changed
- **keep_raw keeps every round's raw, not only N0's.** keep_raw works per instance (campaign_run5: the raws of the
  instance are kept). On K02 it kept N0 (19 MB) and N1–N3 (33 + 32 + 32 MB), although plan_split2's docstring says
  "their N0 trace.raw is kept".
  - For NOT1 this is ~0.1 GB.
  - For the XOR3 original with room it would be ~9 GB (1.2 GB for N0, plus 3 × 2.7 GB). An ANDOR3 original would be
    ~7 GB.
  - Both can sit on one machine. The disk guard (20 GB free) stops new steps before the disk fills; it deletes
    nothing.
  - Only N0 is compared by the remote duplicate.
- **Not exercised here:** the remote duplicate (K07). It ran in the earlier dry runs on campaign_run10 and later.
