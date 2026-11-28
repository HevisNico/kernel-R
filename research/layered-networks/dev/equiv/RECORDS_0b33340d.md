# Record at the freeze candidate 0b33340d (the audit's W3)

Made on the stage-D worker's machine with the pinned Python 3.13.18 (numpy 2.3.5, py_ecc 8.0.0) and Lean 4.35.0. The
tree was the clean clone of the final proof (dev/freeze/final), research/layered-campaign-dev at
0b33340d16cbac3edc00ffae7b6416dddfbdb013. `git status --porcelain --untracked-files=all` printed 0 before and after.

**The four run2 roots of (b)** were analysed twice (out_K02, out_K03, out_K05, out_K06 of evidence/devtest-run2-K02, K03,
K05 and K06). The command, run from the clone's research/layered-networks:

    python -B analysis.py test <OUT> <K02>/out_K02 <K03>/out_K03 <K05>/out_K05 <K06>/out_K06 times=github

- Both runs exited 0. RESULTS.json, SHA256SUMS and the activity items are byte-identical between the two runs.
- RESULTS.json sha256: 48de95e0e264f7186dd6980d54a4229d2afc25ba19aefed1ee6221296c09f47c.
- Kept files: dev/equiv/b/run2/RESULTS_times_github_0b33340d.json, SHA256SUMS_times_github_0b33340d, and the
  activity items read (activity_0b33340d/).
- Compared with the record at e14c3200 (RESULTS_times_github_e14c3200.json), only two keys differ:
  - analysis_sha256 (analysis.py as frozen);
  - pins (pins_sha256 6baf8a51…, the regenerated FREEZE_PINS.json).
- Everything else is the same: the counts, every group's verdicts, the family line and seal_defects (empty).
- The run is in test mode with no draw, because these roots' plans are hand-written devtest plans, not plan_split3's.
  The verdicts are therefore the same as at e14c3200 and at ef374ccd:
  - XOR3 and ANDOR3 held on one instance (no D4 audit in the group);
  - NOT1 held on 2 instances, not established;
  - no run stopped by its own check.
