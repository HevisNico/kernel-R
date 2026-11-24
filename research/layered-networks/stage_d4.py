"""stage_d3.py with the full set of mask reads in stage D (a defect found by the dry run, 2026-11-24). Development only.

  stage_d4.py run | predict | deck | seal | verify ...     as stage_d3.py (rule=one-port by default)

The defect: stage_d.mask_reads reads the masks of fit.MASKS without its empty mask. For an either cell that is (1,), (2,)
only: fit.MASKS["either"] has no (1, 2) (it lists the masks fitted, and an either cell's two-port state is not a
training state). So stage D never read the either cell's two-input mask, and its observed table had no entry for it.
- An instance whose patterns present both inputs to an either cell (ANDOR3 at x = 111) then had an unknown composed
  output. Its eligible prediction stopped at stage_d.predict's assertion (dry run, ANDOR3 9805).
- NOT1 and XOR3 never present both inputs to an either cell, so their predictions were complete and are unaffected.
- That read is the one PLAN_NOTES_3.md (b) names as the first suspect under the one-port rule. It must be observed.

The fix: the mask reads are every non-empty mask of the gate's two ports: both and either (1,), (2,), (1, 2); copy (1,).
The read of (1, 2) enters fit.cell_fit's read calibration as a firing read (FiringSlot: the monotonicity
scoreAt y <= scoreAt (1, 2) and the single-port anchors), as a test read does. stage_d.py and stage_d3.py are pushed
and kept as they are; this file replaces stage_d.read_masks at import and records `mask_reads` = "all" in the prediction.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import stage_d  # noqa: E402
import stage_d3  # noqa: E402

ALL_MASKS = dict(both=[(1,), (2,), (1, 2)], either=[(1,), (2,), (1, 2)], copy=[(1,)])


def read_masks(gate):
    return list(ALL_MASKS[gate])


stage_d.read_masks = read_masks
_stamp = stage_d3.stamp


def stamp(out, rule):
    _stamp(out, rule)
    p = json.loads((Path(out) / "prediction.json").read_bytes())
    p["mask_reads"] = "all"
    p["code"]["stage_d4.py"] = stage_d.sha256_file(HERE / "stage_d4.py")
    (Path(out) / "prediction.json").write_bytes(stage_d.canon(p))
    return p


stage_d3.stamp = stamp

if __name__ == "__main__":
    sys.exit(0 if stage_d3.main(sys.argv[1:]) else 1)
