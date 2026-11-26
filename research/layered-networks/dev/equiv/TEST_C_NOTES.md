# Notes on the test records (dev/equiv)

**The code commit these records were made on: 86a00ac2479101f116f600626f05a13cddedb799.** Equivalence test (b) on the
test machines runs at exactly this commit (RUNBOOK_B.md's `<COMMIT>`). The commits after it change no code file: only
these records, the runbook's notes and the documents.

| Record | Run at 86a00ac2 | Result |
|---|---|---|
| EQUIV_A.json | tests/equiv_campaign.py | 24 of 24 cases identical to the chain's steps (the file is byte-identical to the one committed before) |
| EQUIV_A_NEGATIVE.json | tests/equiv_campaign.py negative | differs in all 24 cases, as it must |
| TEST_C.json | tests/test_campaign.py, all 18 cases | all pass; every check has its expected message matched and its target existing before the call (the `checks` list of each case) |
| EQUIV_B_ANALYSIS.json | analysis.py test, twice, on the final dry run's 8 roots and e2e17's 3; tests/equiv_b.py analysis | two runs byte-identical; identical to analyze10 except the listed keys; `pins.tree_commit` 86a00ac2 |

TEST_C.json is kept exactly as test (c) wrote it.

**analysis_forged_pins, the control.** The control is not a full pass. It is the same forged root with
TEMPLATE_CHECK.json's pins sha set to the analysis tree's: it clears the pins gate and the other-driver gate, and is
then refused for a named, different reason ("mixed environments in one OUTROOT", the ENV.json the forgery changed). In
campaign mode a TEST root can never pass all the way, so this shows that the forged root's refusal comes from its pins,
not from the setup.

**Earlier records.** TEST_C_FOLLOWUP.json (two cases at ee2a0d95) is superseded by TEST_C.json. The earlier full run
at a6fcccf5 stopped at case `pins`, a defect of that test (it copied root_home before home_run had written it); the
fix is in 86a00ac2, which also made every check assert its own message. Checks that had passed vacuously before:
- refusals: the six refusals were checked for the word "refused" only;
- pins: four analysis.py checks pointed at root_home before it existed (now in analysis_forged_pins, on the real root);
- analysis_refuses_test_root: in the unpinned dev tree the first refusal is the tree's own pins, not the TEST root
  (now asserted as such; the TEST-root refusal is shown in analysis_forged_pins);
- sigkill_driver_only, no_pushed_seal, second_seal: the reason was not checked (now "ngspice process(es) running",
  "pre-receive hook declined", "a second seal is refused").

**The first (b) run at a8303e8e was stopped and discarded** (the audit's follow-ups changed campaign.py and
analysis.py). Its branches count for nothing and are left as they are: evidence/devtest-K05 7b13a91b,
evidence/devtest-K06 90e87115, evidence/devtest-seals-K02 c3c36431, evidence/devtest-seals-K03 24818934,
evidence/devtest-seals-K05 86377a55. The rerun writes only evidence/devtest-seals2-K<nn> and evidence/devtest-run2-K<nn>.
