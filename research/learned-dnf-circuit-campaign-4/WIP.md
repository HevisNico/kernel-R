# Campaign 4: unfrozen work in progress (branch research/learned-dnf-circuit-campaign-4-wip)

**Not the frozen implementation.** Nothing here has been reviewed, frozen or rehearsed through the kit. The
campaign branch (`research/learned-dnf-circuit-campaign-4`) holds only `PREDICTION.md` (commit `1596b36`).

- `drafts/AMENDMENT_1.md`: **draft** of amendment 1, final for the owner's review (SHA-256
  `47c9743b97bdef4aa1e39eb7f18cd62b95332a05ff35889dcaf55ff7090d77fd`), not pushed to the campaign branch. Its top
  line says "Pushed alone": that becomes true only when the owner's review is done and it is pushed there, alone,
  as `AMENDMENT_1.md`, before any prediction code is committed to the campaign branch.
- The code follows PREDICTION.md and the seven points of the draft amendment, as named constants in `predicted.py`
  (`DURATION_C`, `RAIL`, `EMPTY_IN_EPSILON`, `GUARDED_READS_1`, `GUARDED_READS_2`) and `plan.py` (`MISSING_NEED`).
- Tested: `test_campaign.py` (11 checks, no simulation). Run by hand on the nominal cell only (no mismatch seed):
  one untrained run without noise, two calibration decks (guard on, off), the Python prediction on them and on
  phase 0's CALIBRATION.json (P0). Not yet run: any extraction, any noisy run (device or injected), the Lean gate,
  the analysis, the manifests, the kit.
