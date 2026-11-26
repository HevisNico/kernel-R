"""compare_d.py with one rule added (compare_d.py is pushed and kept as it is). Development only.

  compare_d2.py SEALDIR SPEC STAGE_N [noiseless|noisy|auto] [OUT.json]

Added rule: a stage-N record that lists shift slots (top-level `skews`, the controls' controls2.py stagen) must have
one shift slot per predicted both cell; a predicted both cell without one is a difference ("no shift slot").
Everything else is compare_d.py's.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import compare_d as C  # noqa: E402

FORMAT = "layered-stage-d-comparison/2"
_observed, _differences = C.observed, C.differences


def observed(s, rec):
    o = _observed(s, rec)
    o["has_skews"] = "skews" in rec
    return o


def differences(pred, obs):
    d = _differences(pred, obs)
    if obs.get("has_skews"):
        for c in pred.get("skew_silent", []):
            if not any(x["cell"] == c for x in obs["skew"]):
                d.append(dict(what="skew", cell=c, predicted=False, observed=None, why="no shift slot"))
    return d


def compare(sealdir, spec_path, outdir, kind="auto"):
    C.observed, C.differences, C.FORMAT = observed, differences, FORMAT
    try:
        return C.compare(sealdir, spec_path, outdir, kind)
    finally:
        C.observed, C.differences, C.FORMAT = _observed, _differences, "layered-stage-d-comparison/1"


if __name__ == "__main__":
    a = sys.argv[1:]
    if len(a) < 3:
        sys.exit(__doc__)
    r = compare(a[0], a[1], a[2], a[3] if len(a) > 3 else "auto")
    text = json.dumps(r, indent=1, sort_keys=True) + "\n"
    if len(a) > 4:
        Path(a[4]).write_text(text)
    print(json.dumps({k: r[k] for k in r if k not in ("observed",)}, indent=1, sort_keys=True))
