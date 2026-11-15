"""One run of campaign 3, as the launch kit starts it: a robust scan of one port (`robustscan.py`), the train of each
port alone, or a run of the ring. The simulation itself is that of `../network-circuit`, unchanged; the calendars are
those of `../network-circuit-ring/ring.py`.

  run.py --out DIR --ngspice BIN --pdk DIR --id ID --kind scan --section tt_mm --seed 7401 --noise 0 --port a1
  run.py ... --kind train --seed 7401 --noise 0 --reads 10
  run.py ... --kind network --seed 7401 --noise 0 --calendar ring --laps 26 --guard 16
  run.py ... --kind network --seed 7401 --noise 0 --calendar control --laps 26 --guard 0

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
sys.path.insert(0, str(HERE.parent / "network-circuit-ring"))
sys.path.insert(0, str(NET))
sys.path.insert(0, str(HERE))
import measure
import net
import ring
import robustscan
import router

N = 3
NOISE_SAMPLES = 64


def fingerprint(tr, cells):
    """SHA-256 of the first 64 values drawn by the voltage noise sources of the cells, in nanovolts, at the sources'
    own sample dates. Without noise every value is zero and the fingerprint is that of zeros."""
    names = [v for c in cells for v in [f"v(x{c}.nzm)"] + [f"v(x{c}.x{p}.{n})" for p in net.PORTS for n in ("nzo", "nzc")]]
    grid = net.NOISE_STEP * np.arange(1, NOISE_SAMPLES + 1)
    assert tr.t[-1] >= grid[-1], "the waveform ends before the last sample date of the fingerprint"
    values = np.rint(np.column_stack([np.interp(grid, tr.t, tr.v[v]) for v in names]) * 1e9).astype("<i8")
    return hashlib.sha256(np.ascontiguousarray(values).tobytes()).hexdigest()


def run(a):
    began = time.time()
    seed = None if a.seed == "none" else int(a.seed)
    cells = ring.cells(N)
    assert tuple(robustscan.CELLS) == tuple(cells)          # the scan runs on the deck of the ring
    if a.kind == "scan":
        assert a.port in ring.ports(N) and not a.noise
        result = robustscan.scan(a.out, a.section, seed, a.port[0], int(a.port[1]), a.ngspice, a.pdk)
        result["wall_s"] = time.time() - began
        (a.out / "result.json").write_text(json.dumps(result, indent=1) + "\n")
        last = max(p["date_s"] for p in result["pulses"])
    else:
        if a.kind == "train":
            assert not a.noise
            calendar, guard = ring.train(N, a.reads), None
        else:
            assert a.laps >= 1 and (a.calendar, a.guard) in (("ring", ring.SEPARATION), ("control", 0))
            calendar = ring.control(N, a.laps) if a.calendar == "control" else ring.ring(N, a.laps)
            guard = a.guard or None
        result = router.run(a.out, calendar, a.ngspice, a.pdk, cells=cells, seed=seed, guard=guard, section=a.section, noise=bool(a.noise))
        last = router.ORIGIN + calendar["horizon"] * net.TU
    (a.out / "pdk").unlink()                                # the link that the session made to the PDK: evidence holds no link
    tr = measure.Trace(a.out / "trace.raw")
    reached = bool(tr.t[-1] >= last - 1e-9)
    mark = fingerprint(tr, cells)
    (a.out / "noise.sha256").write_text(mark + "\n")
    record = dict(id=a.id, kind=a.kind, section=a.section, seed=seed, noise=bool(a.noise), port=a.port, reads=a.reads if a.kind == "train" else None,
                  calendar=a.calendar if a.kind == "network" else None, laps=a.laps if a.kind == "network" else None,
                  guard_units=(a.guard or None) if a.kind == "network" else None,
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
    p.add_argument("--calendar", choices=("ring", "control"))
    p.add_argument("--laps", type=int, default=0)
    p.add_argument("--guard", type=int, default=0)
    r = run(p.parse_args())
    print(json.dumps(dict(id=r["id"], kind=r["kind"], reached_its_last_date=r["reached_its_last_date"], wall_s=round(r["wall_s"]))))


if __name__ == "__main__":
    main()
