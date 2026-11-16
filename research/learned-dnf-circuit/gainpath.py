"""Phase 0 addendum: the gain-path model of the calibration, linear against geometric, on the nominal cell.

  gainpath.py phase0 GAINPATH.json

Score Z(S) = h + sum over active ports j of g_j(k), fitted on every stage 0 to 7 of the guard-disabled probe
(singles and pairs). Linear: g_j(k) = g_j0 + d_j k. Geometric: g_j(k) = g_j0 r_j^k. The help h is a free constant in
both. Reported: the largest residual |Z - G| over every single and pair read, and over a split (fitted on stages 0
to 3 and 6, 7, checked on 4 and 5). No simulation."""
import json
from pathlib import Path
import sys

import numpy as np

READS = {"port 1": (1,), "port 2": (2,), "both": (1, 2)}


def load(folder, tag):
    off = {(r["stage"], r["read"]): r["q_peak"] for r in json.loads((folder / f"cal-{tag}-off.json").read_text())["reads"]}
    return off


def predict(kind, x, k, ports):
    h, a1, b1, a2, b2 = x
    g = {1: (a1, b1), 2: (a2, b2)}
    return h + sum((g[p][0] + g[p][1] * k) if kind == "linear" else g[p][0] * g[p][1] ** k for p in ports)


def fit(kind, off, stages):
    best = None
    for h in np.linspace(0.05, 0.2, 301):                       # h on a grid; the gains by least squares at each h
        x = [h]
        for p in (1, 2):
            ks = np.array(list(stages), float)
            y = np.array([off[(k, f"port {p}")] - h for k in stages])
            if kind == "linear":
                b, a = np.polyfit(ks, y, 1)
                x += [a, b]
            else:
                if (y <= 0).any():
                    break
                lb, la = np.polyfit(ks, np.log(y), 1)
                x += [np.exp(la), np.exp(lb)]
        if len(x) < 5:
            continue
        err = max(abs(off[(k, n)] - predict(kind, x, k, ports)) for k in stages for n, ports in READS.items())
        if best is None or err < best[0]:
            best = (err, x)
    return best


def main():
    folder, out = Path(sys.argv[1]), Path(sys.argv[2])
    result = {}
    for tag in ("049", "05", "10"):
        off = load(folder, tag)
        row = {}
        for kind in ("linear", "geometric"):
            err, x = fit(kind, off, range(8))
            cal = [0, 1, 2, 3, 6, 7]
            err_c, xc = fit(kind, off, cal)
            held = max(abs(off[(k, n)] - predict(kind, xc, k, ports)) for k in (4, 5) for n, ports in READS.items())
            row[kind] = dict(all_stages=dict(largest_residual=err, h=x[0], port1=x[1:3], port2=x[3:5]),
                             split=dict(calibration_stages=cal, largest_residual_on_calibration=err_c, largest_residual_on_stages_4_5=held))
        result[tag] = row
        print(tag, {k: (round(v["all_stages"]["largest_residual"], 4), round(v["split"]["largest_residual_on_stages_4_5"], 4)) for k, v in row.items()})
    out.write_text(json.dumps(dict(what="linear against geometric gain path on the nominal cell; see gainpath.py", amplitudes=result), indent=1) + "\n")


if __name__ == "__main__":
    main()
