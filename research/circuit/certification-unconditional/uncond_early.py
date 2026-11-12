"""Early charge of each mirror, by the rule of AMENDMENT_1.md. No simulation is run.

  uncond_early.py STAGE [FIRST LAST]

For each run of the slice that has a result, reads its compact trace traces/STAGE/NAME.npz, checks
its SHA-256 against the metadata of the run, and writes results/STAGE/NAME.early.csv: one row per
pulse, the charge WE that each mirror delivers from the start of the pulse to 0.75 unit later,
weighted by the leak of the main capacitor. Ends with a status that is not zero when a run of the
slice has no early charge.
"""
import hashlib
import json
import math
from pathlib import Path
import sys

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import uncond_run as U

C = U.C
TE = 0.75                                           # the date of the early gain of the certification campaign


def early_charge(d, col, edge):
    """WE of AMENDMENT_1.md: trapezoid sum over the solver points, the two ends interpolated."""
    lo, hi = edge, edge + TE * C.TU
    i0, i1 = np.searchsorted(d[:, 0], [lo, hi], side="right")
    t = np.concatenate(([lo], d[i0:i1, 0], [hi]))
    v = np.concatenate(([C.at(d, col, lo)], d[i0:i1, col], [C.at(d, col, hi)]))
    f = v * np.exp(-(hi - t) / (2 * C.TU))
    return float(np.sum(np.diff(t) * (f[:-1] + f[1:]) / 2) / (U.CQ * U.VUNIT))


def main():
    stage = sys.argv[1]
    runs = U.MANIFEST["stages"][stage]
    if len(sys.argv) > 2:
        runs = runs[int(sys.argv[2]):int(sys.argv[3])]
    missing = 0
    for run in runs:
        name = run["name"]
        out = HERE / "results" / stage
        if (out / f"{name}.early.csv").exists():
            continue
        if not (out / f"{name}.json").exists() or (out / f"{name}.failed").exists():
            missing += 1
            print(name, "no result")
            continue
        trace = HERE / "traces" / stage / f"{name}.npz"
        meta = json.loads((out / f"{name}.json").read_text())
        if not trace.exists() or hashlib.sha256(trace.read_bytes()).hexdigest() != meta["trace_sha256"]:
            missing += 1
            print(name, "trace missing or not the trace of the metadata")
            continue
        z = np.load(trace)
        d, signals = z["data"], [str(s) for s in z["signals"]]
        cols = [signals.index(s) for s in U.CURRENTS]
        ports = C.MODES[run["mode"]]["ports"]
        rows = [(k - 1, ports[k - 1]) + tuple(early_charge(d, c, k * C.PERIOD + C.OFFSET) for c in cols) for k in range(1, len(ports) + 1)]
        if not all(math.isfinite(w) and w > 0 for r in rows for w in r[2:]):
            missing += 1
            print(name, "a value is not finite or not positive")
            continue
        with (out / f"{name}.early.csv").open("w") as fh:
            fh.write("pulse,port,e1,e2\n")
            for r in rows:
                fh.write("%d,%d,%.12g,%.12g\n" % r)
    print(len(runs), "runs,", missing, "without an early charge")
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
