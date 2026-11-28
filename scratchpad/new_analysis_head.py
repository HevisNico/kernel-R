"""The campaign analysis: one file, in place of analyze.py … analyze10.py (the owner's decision, relayed 2026-11-26).
It is analyze10 flattened, with the defect fixes listed below. Each former layer is a function, applied in order, with a
JSON round trip between them as before.

  analysis.py MODE OUTDIR ROOT [ROOT ...] [draw=DRAW.json] [rehearsal=1] [times=github|bare|lsremote:LOG]
                                          [thresholds=FILE] [controls=DIR] [tips=FILE]

MODE:
- **campaign:** every ROOT must come from campaign.py in campaign mode: its ENV.json names this tree's campaign.py by
  sha256, the frozen template (campaign.FROZEN_TEMPLATE_SHA256), and mode CAMPAIGN. Any other root is refused, and so
  is a mix. draw= is required, times must be github, thresholds the pinned file, controls the noise tree at the
  template's noise_commit.
- **test:** any root of this driver. RESULTS.json then says "mode": "TEST". draw= is optional: given, every check of
  the draw and of the expected plans runs as in campaign mode.
- **rehearsal=1:** the draw's sizes are DRAW_SIZES_REHEARSAL instead of DRAW_SIZES. RESULTS.json then carries
  "REHEARSAL" in its first field (NOTICE), in `mode` and in every verdict line: it can never be read as the campaign.

THE DRAW AND THE EXPECTED PLANS (D8, B5, B16):
- DRAW.json must be, byte for byte, draw_seeds.canon of draw_seeds.draw(beacon, round, the pinned EXCLUDED.json,
  DRAW_SIZES) with one key added, `beacon_round`: drand's /public/<round> (round, signature, randomness). The beacon
  value must be the round's randomness, and the round's BLS signature must verify (beacon_verify.verify) against the
  pinned quicknet chain (beacon_chain.QUICKNET). Any failure refuses.
- The expected plans are plan_split3.split(draw, the frozen template, MACHINES). Each root's PLAN_INPUT.json must be
  byte-identical to plan_split.canon of one of them, which names the root's machine K<nn>; its PLAN.json and
  PLAN_RESOLVED.json must be that plan plus PLAN_LOCAL_KEYS only, equal to TEMPLATE_CHECK.json's trees. Two roots on
  one machine refuse. Everything the analysis reads from a plan is then read from the expected plan.
- Every expected home instance is a row. One with no folder, and every instance of a machine with no root, is "not
  run" (counted for nothing); the rows of each group and level sum to the drawn size.

THE ROOTS (D9, D10, A3, A4, B2, B8, B9, B10):
- A repeated root path, two roots of one machine, and a (group, seed) home instance in more than one folder refuse.
- A folder with a status.json is a home instance (U_, DUP_ and DUPX_ never are). Its name must be <TAG>_<seed> of its
  status.json's group and seed, and its plan must name it; anything else refuses.
- Every line of every SHA256SUMS file of a root (each instance's, seal/, inv/, N<n>/extract/, each DUPX_'s,
  SHA256SUMS.instances and the root's; lean_build/ and kernel_build/ are not read and not walked) is verified against
  the file it names. A missing or differing file REFUSES the analysis and names the files. No manifest the driver
  writes lists a deleted raw trace: an instance's SHA256SUMS is written after the raws are dropped, and lists its
  *.json files only.
- Every file this script reads from a root is under a verified manifest line or on the named list UNMANIFESTED.
- A root without DONE or without its final SHA256SUMS is "not finished": it is named at the top of RESULTS.json, its
  instances with a verified instance manifest are analysed as usual, the others are "not completed". A machine of
  the expected plans with no root is named at the top too, and its instances are "not run". Neither refuses.
- OUTDIR must be new or empty, and outside every root. Every root's SHA256SUMS files are hashed before and after the
  analysis; a change refuses.

THE SEALS (A1, B1, B2, B3, B6, B7, B11):
- A seal is exactly seal/<TAG>_<seed>.json beside MANIFEST.json and SHA256SUMS, and seal.verify must hold. The seal
  log must hold exactly one line for the instance, with this seal's sha256, pushed (GitHub's recorded push time)
  before stage N started. In campaign mode an unreadable seal log or unreadable push times REFUSE the analysis (it is
  rerun later, never reinterpreted); times=lsremote is not accepted there. The activity items read for each seal
  branch are saved in OUTDIR/activity/.
- A seal defect makes an agreement count for nothing (not_sealed). A completed comparison that differs, or a run
  stopped by its own check, stays "refuted" with a defective seal, flagged seal_defect (the owner's rule A1(ii)).
- The regeneration child gets a minimal environment (REGEN_ENV).
- Campaign mode requires every sealed prediction to name stage_d6.py and the template's testError_rule.

THE COMPARISONS (A2, A6, B4):
- Each comparison.json is recomputed with the pinned compare_d2 from its sealed prediction and its round's
  noisy_record.json, and must be byte-identical; its tag, seed, run_kind, noise_round, noise_seed and stage_n_status
  are checked, and a completed comparison must compare letters. Any mismatch refuses. A verdict outside VERDICTS
  refuses.
- A run stopped by its own check (own_check below) counts as refuted, in its own row (the owner's rule A2).

THE LAYERS, in order (each as its file's docstring states):
1. per root (analyze, analyze2): the instances, K0/K3 counting, the observed-only list, run_failed, the controls, the
   max-rule comparison, and ENV (mixed environments refused);
2. over the roots (analyze3): the seal regeneration and the seal-log check (push before stage N), and the
   cross-machine duplicates' records;
3. analyze4: N<n>/SEAL_LOG.json against the log;
4. analyze5: the thresholds of thresholds.json;
5. analyze6: the records' own seal_log;
6. analyze7: the duplicates judged by the controls' tests/check_duplicate.py; the expected controls (A7);
7. analyze8: the proportional D4 rule (d4_regate.py), the planned audits against the present ones (A8);
8. analyze9: the counts side by side;
9. analyze10: the stage-D script named by the prediction, stage_d6 with its kernel field.

RESULTS.json is analyze10's, with these changes, all listed: the format (layered-campaign-analysis/2), analysis_sha256
in place of analyze*_sha256, `mode`, `NOTICE`, `draw`, `machines_detail`, `expected_controls`, `roots_sha256sums`,
`root_drivers` and `pins`; and the fixes above, together with the audit's A1–A6 of 2026-11-26:
- K3: an instance is refuted if ANY completed sealed comparison of a noisy round is "refuted"; held only if every
  round completed and agrees; not completed when no completed round refutes and a round is missing. The seal-log
  checks of a counted level read only its completed rounds.
- Eligibility and room are read from the SEALED prediction (seal/<inst>.json); an instance whose D/prediction.json
  differs from its seal is a seal defect.
- The thresholds are read once, before the first layer (there is no constant default).
- The not_sealed row lists each instance with its comparison verdicts.
- first_failing uses the one step order (ORDER, sealpush included).
- Campaign mode: FREEZE_PINS.json checked over this tree (campaign.pins_check) and the tree clean.
- It refuses to run with Python's -O (sys.flags.optimize): no check of this file is an assert.
"""
