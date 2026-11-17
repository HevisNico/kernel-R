"""Campaign 5: the CI case of M8's eligible path (PREDICTION.md, M8: both paths in CI from the start), code path only.

M8 (analyze.py) on P0's prediction (cases.py, from CALIBRATION.json of #172) with the smoke run without noise of
smoke/nominal-quiet (the nominal cell, need 4, the skew control; its waveform on the branch
evidence/learned-dnf-circuit-campaign-5-smoke). The verdicts are not a claim of anything: the run is not P0's. The
case checks that the eligible path runs and writes a Lean file that `check.sh` compiles and audits.

    m8_case.py RUN_FOLDER OUT.lean

RUN_FOLDER's `evidence/trace.raw` and `evidence/result.json` must have the SHA-256 that its own record.json gives.
"""
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "network-circuit"))

import analyze  # noqa: E402
import c4  # noqa: E402
import cases  # noqa: E402
import reads4  # noqa: E402


def main():
    print(c4.require_pinned())
    folder, out = Path(sys.argv[1]).resolve(), Path(sys.argv[2])
    rec = json.loads((folder / "record.json").read_text())
    for name in ("trace.raw", "result.json"):
        assert hashlib.sha256((folder / "evidence" / name).read_bytes()).hexdigest() == rec["files"][name], name
    x = cases.build()[0]
    assert x["tag"] == "P0" and x["eligible"], "P0 must be eligible"
    rows, _ = analyze.rows_of(folder, [x["needs"][k] for k in ("a", "b", "c1", "c2")], "skew")
    m8, lean = analyze.M8({None: x}, {None: (rows, reads4.words(rows), dict(folder=str(folder)))}, None)
    assert list(m8) == ["None"] and "theorem no_eligible_instance" not in lean
    out.write_text(lean)
    print(json.dumps(dict(case="M8, eligible path: P0 with the nominal smoke run without noise", per_checker=m8["None"]["per_checker"])))


if __name__ == "__main__":
    main()
