# Notes on the test records (dev/equiv)

**The code commit these records were made on: ef374ccd389cf026491d56213cfd064b42ef29df** (the tip after the
github_times fix). From 86a00ac2, the commit equivalence (b) ran on, it differs in sealpush.py and the tests only
(dev/equiv/b/FIX_SHA_TABLE.json); EQUIV_B_NOTES.md says why the (b) roots still stand.

| Record | Run at ef374ccd | Result |
|---|---|---|
| EQUIV_A.json | tests/equiv_campaign.py | 24 of 24 cases identical to the chain's steps (byte-identical to the record at 86a00ac2) |
| EQUIV_A_NEGATIVE.json | tests/equiv_campaign.py negative | differs in all 24 cases, as it must (only the temporary paths changed from the record at 86a00ac2) |
| TEST_C.json | tests/test_campaign.py, all 19 cases | all pass; every check has its expected message matched and its target existing before the call (the `checks` list of each case) |
| b/run2/RESULTS_times_github_ef374ccd.json | analysis.py test, twice, on the four run2 roots, times=github | see EQUIV_B_NOTES.md |
| EQUIV_B_ANALYSIS.json | at 86a00ac2 (not rerun): analysis.py test, twice, on the final dry run's 8 roots and e2e17's 3; tests/equiv_b.py analysis | two runs byte-identical; identical to analyze10 except the listed keys; `pins.tree_commit` 86a00ac2 |

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

**Since 86a00ac2.**
- 2011058e fixed sealpush.times(github) (EQUIV_B_NOTES.md) and added the case `github_times`: sealpush.github_times
  on the activity items recorded for evidence/devtest-seals2-K05 (a branch_creation and a push), plus a synthetic
  force_push and branch_deletion. It asserts that the two real commits have their times and the other two none.
- (c) at 2011058e failed at `pins`: tamper_pins kept FREEZE_PINS.json's old pin of sealpush.py. d234834e makes it
  recompute every pin over the clone, as a freeze does; the one-byte change to fit3.py is still refused.
- (c) at d234834e failed at `analysis_refuses` (18 of 19 pass): the check, not the behaviour. Campaign mode was still
  refused, but in the dev tree sealpush.py now differs from its pin in FREEZE_PINS.json (left untouched), so the
  refusal begins "pinned files differ from FREEZE_PINS.json: ['research/layered-networks/sealpush.py']", and the
  needle "campaign mode: not in FREEZE_PINS.json" was no longer contiguous. ef374ccd (test only, the coordinator's
  option 1) asserts both parts with their exact lists. The other cases on the dev tree's own pins were reviewed:
  refusals is refused by the template before the pins; pins and analysis_forged_pins run in the tamper_pins tree;
  every test-mode launch records the pins check and refuses nothing for it. None is affected.

**analysis_refuses is a dev-tree test.** On the frozen tree (FREEZE_PINS.json at 34bd7513) its precondition, analysis.py
not pinned, no longer holds, so its two pin checks do not apply there. The record of (c) stays at ef374ccd.

**The first (b) run at a8303e8e was stopped and discarded** (the audit's follow-ups changed campaign.py and
analysis.py). Its branches count for nothing and are left as they are: evidence/devtest-K05 7b13a91b,
evidence/devtest-K06 90e87115, evidence/devtest-seals-K02 c3c36431, evidence/devtest-seals-K03 24818934,
evidence/devtest-seals-K05 86377a55. The rerun writes only evidence/devtest-seals2-K<nn> and evidence/devtest-run2-K<nn>.

## (c) after the analysis fixes (D8-D10, the audit's selection, its two defects), split over K07-K12

- **Run 1 at 0b603d54** (before the audit's two defects): 23 of 23 pass, one machine per case
  (dev/equiv/TEST_C_run1_0b603d54.json, merged by dev/equiv/merge_test_c.py from evidence/devtest-K07 ... K12). Kept
  as a record only: its analysis.py was changed after it.
- **Run 2 at 582e5dfc** (code e14c3200, the frozen analysis.py): **25 of 25 pass** (dev/equiv/TEST_C_run2.json, from
  evidence/devtest-run2-K07 ... K12; every case once, the machine of each recorded, the same envcheck values on all
  six). The two new cases: analysis_announce (the announce cannot be redone, on recorded activity items) and
  analysis_own_check (a real driver run on a stub noise tree: a round stopped by its own check is refuted, a
  simulator end is not completed).
- In refuted_stopped_by_own_check, the C<n> label names round n's comparison slot; the run that stopped is N<n>
  (its record N<n>/noisy_record.json; C<n> never ran).
