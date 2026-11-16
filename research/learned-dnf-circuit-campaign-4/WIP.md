# Campaign 4: the work branch (research/learned-dnf-circuit-campaign-4-wip)

**The frozen implementation is the tree of the commit that wrote this text** (the second refreeze, 2026-11-16),
before its rehearsal. Its frozen files are `plan.FROZEN` (`plan.py`), byte for byte; after the freeze, a stage's
source commit may differ from it only as amendment 5 (section 1, item 3) and amendment 6 (section 5) allow, which
`plan.check_after_freeze` checks. It supersedes two freezes under which no rehearsal run was started: `c69e21d` (the
device model's deck named its samples by an absolute path, fixed in `3e63391`) and `52e2cc2` (`REHEARSAL.json` did
not record the frozen tree, and safeguard ii had no entry for amendments pushed after the freeze; amendment 6).

The campaign branch (`research/learned-dnf-circuit-campaign-4`) holds `PREDICTION.md` (commit `1596b36`) and
amendments 1 to 5 (commits `c14124f`, `d6a75a9`, `41cf88b`, `a167f3c`, `6c5630f`), merged into this branch.
Amendment 6 (commit `424f6f9`) is on the campaign branch only: it is not merged here, as a later amendment it
is allowed in a stage's source commit by safeguard ii.

- Not yet run on the frozen commit: the rehearsal (`rehearsal.py`), which is run on this commit next.
- Rehearsed before the freeze, as smoke runs on the nominal cell only (amendment 5, section 7): the calibration decks,
  the runs without noise, the 21 extraction runs without the trip value reused and their merge, one noisy run under
  each model, two real launches of the kit (the seed guard and the stage files), and one pass of the analysis.
- `rehearsal/gate-cases-4` and `rehearsal/mirror-mutations-3`: the kernel gate on P0 to P6 and P4' and the mirror
  mutations, under the pinned interpreter; `check.sh` regenerates and compares them.
- `drafts/AMENDMENT_1.md`: the outgoing director's draft, superseded by the pushed `AMENDMENT_1.md`.
