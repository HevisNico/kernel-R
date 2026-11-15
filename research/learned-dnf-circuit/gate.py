"""Phase 0 of the learned monotone DNF on circuit cells: the read-only test gate, on the nominal cell.

  gate.py OUT NGSPICE PDK

The gate is a change of the testbench only: the dose current of a port is its bias source `idis` (8.2 nA, the
mirror that the steering switch `xmsi` sends into the summing node while the write signal is high). Setting that
source to zero (`alter i.x<cell>.x<port>.idis dc = 0`) leaves the read path untouched (the gain mirror and the main
charge, which decide FIRE) and removes the charge of every write. The circuit itself is not changed.

The run, one nominal cell (`tt`, no mismatch, no seed), reads 22 units apart, each port alone or both together:

  1. ungated silent reads of port 1, port 2 and both: each must write one dose on each read port;
  2. gated silent reads of port 1, port 2 and both: each must move every stored voltage by less than 0.01 mV;
  3. ungated again: the dose must come back;
  4. port 1 trained to FIRE, then the same FIRE read ungated and gated: the latency must be the same, and neither
     writes (a FIRE has an empty write footprint).

Writes `gate.json` in OUT: per read, the stored voltage of both ports before and after, the write signal crossings,
FIRE and its latency. Exploratory, phase 0: not a registered run.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
NET = HERE.parent / "network-circuit"
sys.path.insert(0, str(NET))
import measure
import net

ORIGIN = 100e-6
PERIOD = 22 * net.TU
CELL = "a"
IDIS = 8.2e-9


def main():
    out, ngspice, pdk = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
    s = net.Session(out, net.deck(cells=(CELL,), section="tt"), (CELL,), ngspice, pdk, seed=None, stop_s=0.03)
    plan, t = [], ORIGIN + PERIOD

    def gate(on):
        for p in net.PORTS:
            s.set(f"i.x{CELL}.x{p}.idis", 0.0 if on else IDIS)

    def read(ports, label, gated):
        nonlocal t
        date = net.snap(t)
        s.run(date - 60e-6)
        gate(gated)                                         # set while the cell rests, 60 us before the read
        s.run(date - net.LEAD - 1e-6)
        for p in ports:
            s.pulse(CELL, p, date)
        plan.append(dict(date_s=date, ports=list(ports), label=label, gated=gated))
        t += PERIOD

    for ports in ((1,), (2,), (1, 2)):
        read(ports, "silent, ungated", False)
    for ports in ((1,), (2,), (1, 2)):
        read(ports, "silent, gated", True)
    for ports in ((1,), (2,), (1, 2)):
        read(ports, "silent, ungated again", False)
    for _ in range(4):                                      # port 1 alone, until it fires
        read((1,), "training port 1", False)
    for k in range(2):
        read((1,), "FIRE, ungated", False)
        read((1,), "FIRE, gated", True)
    s.run(t)
    tr = measure.Trace(s.close())
    rows = []
    for r in plan:
        d = r["date_s"]
        rec = measure.pulse_record(tr, CELL, r["ports"][0], d)
        u = {p: dict(before_mV=tr.u(CELL, p, d - 30e-6, d - 2e-6) * 1e3, after_mV=tr.u(CELL, p, d + net.CYCLE - 30e-6, d + net.CYCLE - 2e-6) * 1e3) for p in net.PORTS}
        for p in net.PORTS:
            u[p]["move_mV"] = u[p]["before_mV"] - u[p]["after_mV"]
            u[p]["write_crossings"] = len(tr.crossings(f"v(x{CELL}.x{p}.si)", d, d + net.CYCLE))
        rows.append(dict(r, fire=rec["fire"], latency=rec["latency"], ports_state=u))
    gated_silent = [abs(x["ports_state"][p]["move_mV"]) for x in rows if x["label"] == "silent, gated" for p in net.PORTS]
    fire_pairs = [(a["latency"], b["latency"]) for a, b in zip(rows, rows[1:]) if a["label"] == "FIRE, ungated" and b["label"] == "FIRE, gated"]
    summary = dict(largest_move_of_a_gated_silent_read_mV=max(gated_silent),
                   ungated_silent_doses_mV=[round(x["ports_state"][p]["move_mV"], 4) for x in rows if x["label"].startswith("silent, ungated") for p in x["ports"]],
                   fire_latency_ungated_and_gated=fire_pairs,
                   largest_move_across_a_fire_read_mV=max(abs(x["ports_state"][p]["move_mV"]) for x in rows if x["label"].startswith("FIRE") for p in net.PORTS))
    (out / "gate.json").write_text(json.dumps(dict(what="the read-only test gate on the nominal cell; see gate.py", summary=summary, reads=rows), indent=1) + "\n")
    (out / "pdk").unlink()
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
