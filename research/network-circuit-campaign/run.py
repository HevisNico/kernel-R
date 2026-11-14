"""One run of the campaign, as the launch kit starts it: a scan of one port, a train on each port alone, or a
network run. The simulation itself is that of `../network-circuit` and `../network-circuit/phase1`, unchanged.

  run.py --out DIR --ngspice BIN --pdk DIR --id ID --kind scan --section tt_mm --seed 7201 --noise 0 --port a1
  run.py ... --kind train --seed 7201 --noise 1 --reads 10
  run.py ... --kind network --seed 7201 --noise 0 --spacing 18 --guard 16

Written in DIR: the deck (`input.spice`), the log of the simulator session, the waveform (`trace.raw`), what the
simulation recorded of itself (`result.json`), and from this file `record.json` (what was asked, that the run
reached its last date, the SHA-256 of the files) and `noise.sha256`, the fingerprint of the noise that the run drew.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

import numpy as np

HERE = Path(__file__).resolve().parent
NET = HERE.parent / "network-circuit"
sys.path.insert(0, str(NET))
sys.path.insert(0, str(NET / "phase1"))
import calendars
import cellscan
import measure
import net
import noisechar
import router

NOISE_SAMPLES = 64


def fingerprint(tr, cells):
    """SHA-256 of the first 64 values drawn by the ten voltage noise sources of the two cells, in nanovolts, at the
    sources' own sample dates. Without noise every value is zero and the fingerprint is that of zeros."""
    names = [v for c in cells for v in [f"v(x{c}.nzm)"] + [f"v(x{c}.x{p}.{n})" for p in net.PORTS for n in ("nzo", "nzc")]]
    grid = net.NOISE_STEP * np.arange(1, NOISE_SAMPLES + 1)
    assert tr.t[-1] >= grid[-1], "the waveform ends before the last sample date of the fingerprint"
    values = np.rint(np.column_stack([np.interp(grid, tr.t, tr.v[v]) for v in names]) * 1e9).astype("<i8")
    return hashlib.sha256(np.ascontiguousarray(values).tobytes()).hexdigest()


def run(a):
    began = time.time()
    seed = None if a.seed == "none" else int(a.seed)
    cells = cellscan.CELLS
    if a.kind == "scan":
        assert a.port in ("a1", "a2", "b1", "b2") and not a.noise
        result = cellscan.scan(a.out, a.section, seed, a.port[0], int(a.port[1]), a.ngspice, a.pdk)
        result["wall_s"] = time.time() - began
        (a.out / "result.json").write_text(json.dumps(result, indent=1) + "\n")
        last = max(p["date_s"] for p in result["pulses"])
    else:
        if a.kind == "train":
            calendar, guard = noisechar.calendar(a.reads), None
        else:
            calendar, guard = calendars.reciprocal(a.spacing), (a.guard or None)
        result = router.run(a.out, calendar, a.ngspice, a.pdk, cells=cells, seed=seed, guard=guard, section=a.section, noise=bool(a.noise))
        last = router.ORIGIN + calendar["horizon"] * net.TU
    (a.out / "pdk").unlink()                                # the link that the session made to the PDK: evidence holds no link
    tr = measure.Trace(a.out / "trace.raw")
    reached = bool(tr.t[-1] >= last - 1e-9)
    mark = fingerprint(tr, cells)
    (a.out / "noise.sha256").write_text(mark + "\n")
    record = dict(id=a.id, kind=a.kind, section=a.section, seed=seed, noise=bool(a.noise), port=a.port, reads=a.reads if a.kind == "train" else None,
                  spacing=a.spacing if a.kind == "network" else None, guard_units=(a.guard or None) if a.kind == "network" else None,
                  last_date_s=last, waveform_ends_s=float(tr.t[-1]), reached_its_last_date=reached, noise_fingerprint=mark, points=int(len(tr.t)),
                  wall_s=time.time() - began, files={x: net.sim.digest(a.out / x) for x in ("input.spice", "session.log", "trace.raw", "result.json")})
    (a.out / "record.json").write_text(json.dumps(record, indent=1) + "\n")
    assert reached, "the waveform ends before the last date of the run"
    return record


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("out", "ngspice", "pdk"):
        p.add_argument("--" + name, type=Path, required=True)
    p.add_argument("--id", required=True)
    p.add_argument("--kind", choices=("scan", "train", "network"), required=True)
    p.add_argument("--section", required=True)
    p.add_argument("--seed", required=True)
    p.add_argument("--noise", type=int, choices=(0, 1), required=True)
    p.add_argument("--port")
    p.add_argument("--reads", type=int, default=10)
    p.add_argument("--spacing", type=int, choices=(18, 8))
    p.add_argument("--guard", type=int, default=0)
    r = run(p.parse_args())
    print(json.dumps(dict(id=r["id"], kind=r["kind"], reached_its_last_date=r["reached_its_last_date"], wall_s=round(r["wall_s"]))))


if __name__ == "__main__":
    main()
