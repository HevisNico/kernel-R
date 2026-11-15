"""The phase 0 records of the nominal cell, summarized into CALIBRATION.json: the read-only gate, and per pulse
amplitude the fit of CalibratedAdditiveRead with its calibration and validation split.

  summarize.py phase0 CALIBRATION.json

Score observable: the peak of the main charge q over a read, from the matched guard-disabled probe (q = 0.1 at rest,
FIRE level 1). The additive model of a cell is Z(S) = h + sum over active ports j of g_j(k), with a constant help h
and a linear gain path g_j(k) = g_j0 + d_j k in the dose stage k. Split: the model is fitted on stages 0 to 5 of the
probe (the calibration); stages 6 and 7 of the probe and every FIRE bit of the guard-on pass are held out (the
validation). The threshold is the FIRE level, theta = 1. No noise: phase 0, nominal cell.
"""
import json
from pathlib import Path
import sys

import numpy as np

CAL, HOLD = range(0, 6), range(6, 8)
READS = {"empty": (), "port 1": (1,), "port 2": (2,), "both": (1, 2)}


def fit(off):
    """Least squares for (h, g10, d1, g20, d2) on the singles and the pair of the calibration stages."""
    rows, rhs = [], []
    for k in CAL:
        for name, ports in READS.items():
            if not ports:
                continue
            row = [1, 0, 0, 0, 0]
            for p in ports:
                row[1 + 2 * (p - 1)] = 1
                row[2 + 2 * (p - 1)] = k
            rows.append(row)
            rhs.append(off[(k, name)]["q_peak"])
    x, *_ = np.linalg.lstsq(np.array(rows, float), np.array(rhs), rcond=None)
    return dict(h=x[0], g0={1: x[1], 2: x[3]}, d={1: x[2], 2: x[4]})


def model(m, k, ports):
    return m["h"] + sum(m["g0"][p] + m["d"][p] * k for p in ports)


def amplitude(folder, tag):
    on = {(r["stage"], r["read"]): r for r in json.loads((folder / f"cal-{tag}-on.json").read_text())["reads"]}
    off = {(r["stage"], r["read"]): r for r in json.loads((folder / f"cal-{tag}-off.json").read_text())["reads"]}
    m = fit(off)
    res = {"calibration": [], "held out": []}
    table = []
    for k in range(8):
        row = dict(stage=k, u_mV=round(off[(k, "empty")]["u_before_mV"]["1"], 3))
        for name, ports in READS.items():
            z = off[(k, name)]["q_peak"]
            g = model(m, k, ports) if ports else None
            if ports:
                res["calibration" if k in CAL else "held out"].append(z - g)
            row[name] = dict(Z=round(z, 4), G=None if g is None else round(g, 4), fire=on[(k, name)]["fire"],
                             latency=None if on[(k, name)]["latency"] is None else round(on[(k, name)]["latency"], 3))
        table.append(row)
    first = {name: next((k for k in range(8) if on[(k, name)]["fire"]), None) for name in ("port 1", "port 2", "both")}
    bits = [(off[(k, n)]["q_peak"] >= 1.0) == on[(k, n)]["fire"] for k in range(8) for n in READS]
    kb = first["both"]
    margins = None
    if kb:
        margins = dict(last_silence_q=1.0 - off[(kb - 1, "both")]["q_peak"], first_fire_q=off[(kb, "both")]["q_peak"] - 1.0,
                       pair_dose_q=off[(kb, "both")]["q_peak"] - off[(kb - 1, "both")]["q_peak"],
                       singles_at_the_stop_q=[off[(kb, "port 1")]["q_peak"], off[(kb, "port 2")]["q_peak"]])
    return dict(fit=dict(h=m["h"], g0=m["g0"], d=m["d"]), table=table, first_fire_stage=first,
                residual=dict(calibration=[min(res["calibration"]), max(res["calibration"])], held_out=[min(res["held out"]), max(res["held out"])]),
                fire_bit_is_the_threshold_comparison=all(bits), pair_margins=margins)


def main():
    folder, out = Path(sys.argv[1]), Path(sys.argv[2])
    gate = json.loads((folder / "gate.json").read_text())["summary"]
    moves = []
    for tag in ("049", "05", "10"):
        for g in ("on", "off"):
            moves += [abs(v) for r in json.loads((folder / f"cal-{tag}-{g}.json").read_text())["reads"] if r["gated"] for v in r["move_mV"].values()]
    doses = [v for tag in ("049", "05", "10") for r in json.loads((folder / f"cal-{tag}-on.json").read_text())["reads"] if r["read"] == "joint dose" for v in r["move_mV"].values()]
    result = dict(what="phase 0 of the learned monotone DNF on the nominal cell (tt, no mismatch, no seed): the read-only gate and the calibration; see summarize.py",
                  gate=dict(gate, largest_move_of_any_gated_read_in_the_calibration_mV=max(moves), clock_only_joint_dose_mV=[min(doses), max(doses)], gated_reads=len(moves) // 2),
                  amplitudes={tag: amplitude(folder, tag) for tag in ("049", "05", "10")})
    out.write_text(json.dumps(result, indent=1) + "\n")
    for tag, a in result["amplitudes"].items():
        print(tag, a["first_fire_stage"], a["residual"], a["fire_bit_is_the_threshold_comparison"], a["pair_margins"])


if __name__ == "__main__":
    main()
