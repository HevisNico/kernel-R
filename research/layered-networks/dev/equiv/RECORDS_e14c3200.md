# Records at e14c3200 (analysis.py after D8-D10, the audit's selection and its two defects)

Made on the stage-D worker's machine, the pinned Python 3.13.18 (numpy 2.3.5, py_ecc 8.0.0), Lean 4.35.0, at
e14c32004b212ae8fd840d0ef2f728bf6e582314 (code; 582e5dfc adds only dev/equiv files).

- **(a)** tests/equiv_campaign.py: 24 of 24 identical; EQUIV_A.json byte-identical to the record (dev/equiv/EQUIV_A.json).
  The negative control differs in 24 of 24 cases; its output equals dev/equiv/EQUIV_A_NEGATIVE.json except the
  temporary paths. campaign.py has not changed since 86a00ac2's equivalence runs except sealpush.py (ef374ccd).
- **The four run2 roots**, analysis.py test, times=github, twice: RESULTS.json and SHA256SUMS byte-identical between
  the two runs (RESULTS.json sha256 3ce024d598d849b25d3c5cede10cc034f92a159ff1ea548f18122acc0d634d98). Kept: dev/equiv/b/run2/RESULTS_times_github_e14c3200.json, and the
  activity items read (activity_e14c3200/).
  - Test mode with no draw (their plans are hand-written devtest plans, not plan_split3's).
  - The same seals and verdicts as at ef374ccd: seal_defects empty; margins XOR3_9803 3.493 s, ANDOR3_6104 2.832 s,
    NOT1_6212 2.909 s, NOT1_6220 3.368 s; XOR3 and ANDOR3 held on one instance (no D4 audit in the group), NOT1
    held on 2 instances, not established; no run stopped by its own check.
- **(c)** at 0b603d54 (before the audit's two defects): 23 of 23 on K07-K12 (evidence/devtest-K07 ... K12, merged by
  dev/equiv/merge_test_c.py). The (c) run at the fixed tip waits for the audit's go (RUNBOOK_C.md, evidence/devtest-run2-K<nn>).
- **The independent suite** (tests/test_analysis_defects.py, not written by the implementer): 24 of 24 at this tip.
