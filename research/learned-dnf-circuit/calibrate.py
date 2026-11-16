"""Phase 0 of the learned monotone DNF on circuit cells: the calibration of CalibratedAdditiveRead on one cell.

  calibrate.py OUT NGSPICE PDK AMP GUARD [SECTION SEED]

One cell (nominal by default: `tt`, no seed). At each dose stage k = 0 .. STAGES-1, four read-only slots 22 units
apart, all under the test gate (`gate.py`): the empty read (no pulse), port 1 alone, port 2 alone, both ports at
the same date, every pulse of amplitude AMP. Then one clock-only dose on both ports at the same date, ungated: the
next stage. GUARD = on records the FIRE bit and its latency. GUARD = off is the matched guard-disabled charge probe:
the FIRE reference `vfire` is set to 0 V, so that the cell cannot fire and the main charge is not reset, and the
peak of the main charge q (0.1 at rest, 1 at the FIRE level) over the read is the score observable. Each stage
also records the stored voltage of both ports.

Writes `calibration.json` in OUT. Exploratory, phase 0: not a registered run.
"""
import json
from pathlib import Path
import sys

import numpy as np

HERE = Path(__file__).resolve().parent
NET = HERE.parent / "network-circuit"
sys.path.insert(0, str(NET))
import measure
import net

ORIGIN = 100e-6
PERIOD = 22 * net.TU
CELL = "a"
IDIS = 8.2e-9
STAGES = 8
READS = (("empty", ()), ("port 1", (1,)), ("port 2", (2,)), ("both", (1, 2)))


def q_of(tr, lo, hi):
    """Peak of the main charge q over [lo, hi]: q = (1.25 - v(vq)) / 0.5 + 0.1."""
    i0, i1 = np.searchsorted(tr.t, [lo, hi])
    return float(((1.25 - tr.v[f"v(x{CELL}.vq)"][i0:i1]) / 0.5 + 0.1).max())


def main():
    out, ngspice, pdk, amp, guard = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]), float(sys.argv[4]), sys.argv[5]
    section = sys.argv[6] if len(sys.argv) > 6 else "tt"
    seed = None if len(sys.argv) <= 7 or sys.argv[7] == "none" else int(sys.argv[7])
    assert guard in ("on", "off")
    s = net.Session(out, net.deck(cells=(CELL,), section=section), (CELL,), ngspice, pdk, seed=seed, stop_s=0.03)
    if guard == "off":
        s.set("vfire", 0.0)
    plan, t = [], ORIGIN + PERIOD

    def gate(on):
        for p in net.PORTS:
            s.set(f"i.x{CELL}.x{p}.idis", 0.0 if on else IDIS)

    def slot(ports, a, gated, **more):
        nonlocal t
        date = net.snap(t)
        s.run(date - 60e-6)
        gate(gated)
        s.run(date - net.LEAD - 1e-6)
        for p in ports:
            s.pulse(CELL, p, date, a)
        plan.append(dict(date_s=date, ports=list(ports), amp=a, gated=gated, **more))
        t += PERIOD

    for k in range(STAGES):
        for name, ports in READS:
            slot(ports, amp, True, stage=k, read=name)
        slot((1, 2), 0.0, False, stage=k, read="joint dose")
    s.run(t)
    tr = measure.Trace(s.close())
    rows = []
    for r in plan:
        d = r["date_s"]
        fires = tr.crossings(f"v(x{CELL}.p)", d, d + net.TU + 2e-6)
        u = {p: tr.u(CELL, p, d - 30e-6, d - 2e-6) * 1e3 for p in net.PORTS}
        after = {p: tr.u(CELL, p, d + net.CYCLE - 30e-6, d + net.CYCLE - 2e-6) * 1e3 for p in net.PORTS}
        rows.append(dict(r, u_before_mV=u, move_mV={p: u[p] - after[p] for p in net.PORTS}, fire=bool(fires),
                         latency=(fires[0] - d) / net.TU if fires else None, q_peak=q_of(tr, d, d + 3 * net.TU),
                         q_rest=q_of(tr, d - 3e-6, d - 1e-6)))
    (out / "calibration.json").write_text(json.dumps(dict(what="calibration of one cell; see calibrate.py", amp=amp, guard=guard, section=section, seed=seed,
                                                          reads=rows), indent=1) + "\n")
    (out / "pdk").unlink()
    for r in rows:
        if r["read"] != "joint dose":
            print(r["stage"], r["read"], r["fire"], None if r["latency"] is None else round(r["latency"], 3), round(r["q_peak"], 4))


if __name__ == "__main__":
    main()
