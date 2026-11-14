"""Does the pinned Python 3.12.3 give the outputs that PR 123 published under Python 3.12.14? No simulator is run here.

  python_identity.py REPLAY          -> PYTHON_IDENTITY.json
  python_identity.py REPLAY --check  compares with the committed file instead of writing it

REPLAY holds the diagnostics of ../sky130-supervisor-qualification replayed with `calibrate.py` under
the interpreter that runs this script (the commands are in ../sky130-supervisor-qualification/REPRODUCE.md).
For each of the 23 diagnostics without noise: the deck rebuilt here, the replayed waveform and the
analysis of that waveform are compared with ../sky130-supervisor-qualification/RESULTS.json. The three
noisy diagnostics cannot be replayed (their noise is not reproducible) and are not compared.
"""
import gzip
import hashlib
import importlib.metadata
import io
import json
import os
from pathlib import Path
import platform
import sys

import numpy as np

HERE = Path(__file__).resolve().parent
OLD = HERE.parent / "sky130-supervisor-qualification"
sys.path.insert(0, str(OLD))
import calibrate


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    root = Path(sys.argv[1]).resolve()
    saved = json.loads((OLD / "RESULTS.json").read_text())
    rows = []
    for record in saved["records"]:
        case = record["case"]
        if case.get("noise"):
            continue
        folder = root / case["name"]
        text, starts, stop = calibrate.make_deck(case)
        raw = (folder / "trace.txt.gz").read_bytes()
        result = calibrate.analyze(np.loadtxt(io.BytesIO(gzip.decompress(raw))), case, starts, stop)
        replayed = json.loads((folder / "metadata.json").read_text())
        rows.append(dict(name=case["name"], deck_identical=sha(text.encode()) == record["deck_sha256"] == sha((folder / "input.spice").read_bytes()),
                         waveform_identical=sha(raw) == record["trace_sha256"], waveform_sha256=sha(raw),
                         analysis_identical=result == record["result"] == replayed["result"]))
    joint = {c["name"]: c for c in saved["capacity"]}
    result = dict(python_version=platform.python_version(), python_sha256=sha(Path(os.path.realpath(sys.executable)).read_bytes()),
                  numpy_version=np.__version__, numpy_record_sha256=sha(importlib.metadata.distribution("numpy").read_text("RECORD").encode()),
                  published_with="Python 3.12.14 and numpy 2.3.5 (PR 123)", compared=len(rows), joint_reads_compared=sum(r["name"] in joint for r in rows),
                  all_identical=all(r["deck_identical"] and r["waveform_identical"] and r["analysis_identical"] for r in rows),
                  not_compared=[r["case"]["name"] for r in saved["records"] if r["case"].get("noise")], diagnostics=rows)
    target = HERE / "PYTHON_IDENTITY.json"
    if "--check" in sys.argv:
        assert json.loads(target.read_text()) == result, "this interpreter does not give the committed comparison"
        print("PASS: the committed comparison recomputed")
    else:
        target.write_text(json.dumps(result, indent=1) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "diagnostics"}, indent=1))
    assert result["all_identical"] and result["compared"] == 23


if __name__ == "__main__":
    main()
