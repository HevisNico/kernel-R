# The freeze record's proof (dev/freeze)

**Superseded.** Everything below is the old proof at 34bd7513 (pins 7323d3dd), kept as a record. The final proof, at
the freeze candidate after the last exclusion scan and the regenerated pins (340e1c6c), is in dev/freeze/final/
(FINAL_PROOF.md), made on a clean clone.

**Made on a clean clone of research/layered-campaign-dev at 34bd7513bc846f54b5bad87f875437675328c471** (the commit
that regenerated FREEZE_PINS.json; FREEZE_PINS.json sha256 7323d3ddc76204f704db0b12572c22c0135b5b5b96171b0d6c623220d263cd8f,
114 files). The clone was fetched by branch name from origin, with two clean worktrees added at the template's
kit_commit d599300d and noise_commit 458bc7a6. Nothing was launched. The commit that adds these files changes no
pinned file: only FREEZE.txt (not pinned) and this folder.

1. **The plans.** `plan_split3.py DRAW_dummy.json campaign_template.json plans` (plan_split3.out). DRAW_dummy.json
   is the dummy draw test (c) writes (its note: "tests (c)"); it is not the campaign's draw.
2. **campaign.py check campaign campaign_template.json plans/PLAN_K01.json** → check_campaign.json: ok true, pins
   tree_clean true, mismatched [], not_pinned [], pinned_files 114, pins_sha256 7323d3dd…, tree_commit 34bd7513. The
   same check on all 12 plans: check_all_plans.txt, every one ok, [] and [], clean.
3. **analysis.py campaign** on a TEST root (evidence/devtest-run2-K02's out_K02), times=github → analysis_campaign.txt:
   - with controls set to the noise worktree's top folder: refused, "controls must be the noise tree at 458bc7a6d763
     (…/research/layered-networks)";
   - with controls set to that folder: refused, "roots not run by this campaign.py on the frozen template in campaign
     mode: ['machine_1']", the root being TEST.
   Both refusals come after the pins gate, the pinned-thresholds gate, the times gate and the noise-worktree gate,
   all passed (analysis.py main, in that order).

## What depends on the dev FREEZE_PINS.json as it was before this record (not changed; the records stay at ef374ccd)

- **tests/test_campaign.py, case analysis_refuses (analysis_refuses_test_root):** its checks c1 ("not in
  FREEZE_PINS.json: [analysis.py, campaign.py, campaign_template.json]") and c1b ("pinned files differ from
  FREEZE_PINS.json: ['research/layered-networks/sealpush.py']") assert the old pins' two refusals. At the new pins the
  dev tree passes the pins gate, so both would fail; campaign mode would be refused later (the TEST root).
- **tests/test_campaign.py, tamper_pins (cases pins and analysis_forged_pins):** it recomputes every pin and adds a
  test group of the three MUST_BE_PINNED files. At the new pins they are already pinned: the group repeats them with
  the same sha256, which pins_check accepts. analysis_forged_pins' "the dev tree's FREEZE_PINS.json" still differs
  from the tampered tree's (the added group), so its refusal holds. Not expected to change; not rerun.
- **tests/equiv_b.py:** only the label of the analysis's `pins` key; no value.
- **CI:** no workflow reads FREEZE_PINS.json or runs these tests (.github/workflows: layered-checks.yml runs the Lean
  checks of research/learned-coincidence only).
- Every test-mode run records the pins check in TEMPLATE_CHECK.json and the analysis's `pins` key as data; none
  refuses for it.
