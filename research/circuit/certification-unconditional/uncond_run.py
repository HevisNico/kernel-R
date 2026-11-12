"""One run of this campaign, by the rules of PREDICTION.md.

  uncond_run.py STAGE NAME

The run is looked up in manifest.json. The deck, the rows and the compact trace are made by the
function main of ../certification/cert_run.py, which is not modified: this script sets the folder
of the results and adds two saved signals, the drain currents of the output transistor of the gain
mirror of each port. It then measures, on the compact trace, the charge that each mirror delivers
during each pulse, weighted by the leak of the main capacitor. Writes, under results/STAGE/:
  NAME.csv         the rows of cert_run.py
  NAME.json        the metadata of cert_run.py
  NAME.charge.csv  one row per pulse: the weighted charge W of each mirror
  NAME.failed      when the run, a check or the charge measure fails
and the compact trace traces/STAGE/NAME.npz, which goes to the private repository.
"""
import hashlib
import json
import math
from pathlib import Path
import sys

import numpy as np

HERE = Path(__file__).resolve().parent
CERT = HERE.parent / "certification"
sys.path.insert(0, str(CERT))
import cert_run as C

CQ, VUNIT = 5e-12, 0.5              # main capacitor and voltage of one unit of q, from the netlist
MANIFEST = json.loads((HERE / "manifest.json").read_text())
CURRENTS = MANIFEST["added_signals"]


def weighted_charge(d, col, edge):
    """W of PREDICTION.md: trapezoid sum over the solver points of the pulse, the two ends interpolated."""
    lo, hi = edge, edge + C.TU
    i0, i1 = np.searchsorted(d[:, 0], [lo, hi], side="right")
    t = np.concatenate(([lo], d[i0:i1, 0], [hi]))
    v = np.concatenate(([C.at(d, col, lo)], d[i0:i1, col], [C.at(d, col, hi)]))
    f = v * np.exp(-(hi - t) / (2 * C.TU))
    return float(np.sum(np.diff(t) * (f[:-1] + f[1:]) / 2) / (CQ * VUNIT))


def main():
    stage, name = sys.argv[1], sys.argv[2]
    run = next(r for r in MANIFEST["stages"][stage] if r["name"] == name)
    assert hashlib.sha256((CERT / "cert_run.py").read_bytes()).hexdigest() == MANIFEST["cert_run_sha256"], "cert_run.py changed"
    assert not run["noise"] and run["mode"] in ("train", "leak")
    out = HERE / "results" / stage
    if (out / f"{name}.failed").exists():
        print(name, "already there")
        return 0
    C.HERE = HERE                                   # results, traces, work folder and manifest of this campaign
    C.SIGNALS = C.SIGNALS[:17] + CURRENTS           # the 17 signals of the certification campaign, then the two currents
    status = C.main()
    if status != 0 or (out / f"{name}.charge.csv").exists():
        return status
    ports = C.MODES[run["mode"]]["ports"]
    z = np.load(HERE / "traces" / stage / f"{name}.npz")
    d, signals = z["data"], [str(s) for s in z["signals"]]
    cols = [signals.index(s) for s in CURRENTS]
    rows = [(k - 1, ports[k - 1]) + tuple(weighted_charge(d, c, k * C.PERIOD + C.OFFSET) for c in cols) for k in range(1, len(ports) + 1)]
    if not all(math.isfinite(w) and w > 0 for r in rows for w in r[2:]):
        (out / f"{name}.failed").write_text("charge measure: a value is not finite or not positive\n")
        print(name, "FAILED charge measure")
        return 1
    with (out / f"{name}.charge.csv").open("w") as fh:
        fh.write("pulse,port,w1,w2\n")
        for r in rows:
            fh.write("%d,%d,%.12g,%.12g\n" % r)
    return 0


if __name__ == "__main__":
    sys.exit(main())
