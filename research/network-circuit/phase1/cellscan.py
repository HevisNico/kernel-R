"""One port of one cell of a network instance, measured with every other port idle. Phase 1, exploratory.

  cellscan.py OUT SECTION SEED CELL PORT NGSPICE PDK

The deck is that of the network instance: two cells, the given model section (`tt` or `tt_mm`), the
given seed for the mismatch sample, junction areas of stage J, no noise. Only the port named is
pulsed. What the run gives, all from reads at least 22 time units apart unless said:

  - the reads that train the port from its preset, with the dose of each silent read;
  - one more read 16 units after a FIRE of the same port: what a pulse 16 units earlier leaves;
  - the service threshold, by bisection: an imposed leak on this port alone, or a clock-only dose,
    moves its stored voltage between two reads, and the bracket between the highest stored voltage
    read correctly and the lowest read incorrectly is halved until it is under 20 uV.

Nothing is decided here: `constants.py` turns the records into the constants of the model.
"""
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import measure
import net

CELLS = ("a", "b")
ORIGIN = 100e-6
PERIOD = 22 * net.TU
LEAK_PER_MV = 4.42e-10          # conductance that loses about 1 mV in 170 us; refined on the run itself


def scan(out, section, seed, c, port, ngspice, pdk, coarse=0.25e-3, bracket=20e-6):
    text = net.deck(cells=CELLS, section=section, leak_per_port=True)
    s = net.Session(out, text, CELLS, ngspice, pdk, seed=seed, stop_s=0.06)
    me, leak, state, pulses = f"v(x{c}.vmem{port})", f"vgl{c}{port}", dict(t=ORIGIN, scale=LEAK_PER_MV), []

    def read(date, amp=1, **more):
        """One pulse at `date`; returns (FIRE?, latency)."""
        date = net.snap(date)
        s.run(date - net.LEAD - 1e-6)
        was = s.protected(c)
        s.pulse(c, port, date, amp)
        t = s.run(date + 25e-6, watch=() if was else (c,))
        pulses.append((date, more))
        if was or t >= date + 25e-6 - 1e-12 or not s.protected(c):
            return False, None
        when = s.fire_date(c, date - 1e-6)
        s.run(date + 25e-6)
        return True, (when - date) / net.TU

    def period(kind, delta=0.0):
        """22 units: a read, a clock-only dose or nothing, then an imposed leak of about `delta` volts on this port."""
        date = state["t"]
        state["t"] += PERIOD
        ok = None
        if kind != "idle":
            fired, latency = read(date, amp=1 if kind == "read" else 0, kind=kind)
            ok = bool(fired and latency <= 1.0) if kind == "read" else None
        s.run(date + 200e-6)
        before = s.mean(me, date + 160e-6, date + 195e-6)
        if delta > 0:
            s.set(leak, delta * 1e3 * state["scale"])
            s.run(date + 370e-6)
            s.set(leak, 0)
        s.run(date + PERIOD - 3e-6)
        after = s.mean(me, date + 400e-6, date + 435e-6)
        if delta > 0 and after - before > 0.2 * delta:
            state["scale"] *= delta / (after - before)
        return ok, after

    _, v = period("idle")
    pre = v
    for _ in range(30):                                     # silent reads train the port
        ok, v_new = period("read")
        if ok:
            break
        pre, v = v_new, v_new
    else:
        s.kill()
        raise RuntimeError("no correct read after thirty reads")
    correct, v = pre, v_new
    read(state["t"], kind="reference")                      # an isolated FIRE, then the same read 16 units after it
    read(state["t"] + 16 * net.TU, kind="16 units after a FIRE")
    state["t"] += 16 * net.TU + PERIOD
    incorrect = None
    for _ in range(40):                                     # coarse descent
        pre = v
        ok, v = period("read", coarse)
        if not ok:
            incorrect = pre
            break
        correct = pre
    assert incorrect is not None and incorrect > correct
    for _ in range(16):                                     # bisection
        if incorrect - correct <= bracket:
            break
        target = (correct + incorrect) / 2
        for _ in range(40):
            gap = target - v
            if gap < -2e-6:
                _, v = period("dose")
            elif gap <= 0.05e-3:
                if gap > 2e-6:
                    _, v = period("idle", gap)
                break
            else:
                _, v = period("idle", min(gap - 0.03e-3, 1.2e-3))
        pre = v
        ok, v = period("read")
        if ok:
            correct = max(correct, pre)
        else:
            incorrect = min(incorrect, pre)
    s.run(state["t"])
    raw = s.close()
    tr = measure.Trace(raw)
    records = [dict(measure.pulse_record(tr, c, port, d), **more) for d, more in pulses]
    other = [x for x in CELLS if x != c][0]
    idle = dict(fires_of_the_other_cell=len(tr.crossings(f"v(x{other}.p)", 0.0, tr.t[-1])),
                drift_of_the_other_cell_uV=[(tr.u(other, p, tr.t[-1] - 40e-6, tr.t[-1] - 2e-6) - tr.u(other, p, ORIGIN - 40e-6, ORIGIN - 5e-6)) * 1e6 for p in net.PORTS])
    return dict(kind="cellscan", section=section, seed=seed, cell=c, port=port, pulses=records, bracket_stored_V=[correct, incorrect], idle=idle,
                points=int(len(tr.t)), raw_sha256=net.sim.digest(raw), deck_sha256=net.sim.digest(Path(out) / "input.spice"))


def main():
    out, section, seed, c, port, ngspice, pdk = sys.argv[1:8]
    began = time.time()
    r = scan(Path(out), section, None if seed == "none" else int(seed), c, int(port), Path(ngspice), Path(pdk))
    r["wall_s"] = time.time() - began
    (Path(out) / "result.json").write_text(json.dumps(r, indent=1) + "\n")
    print(json.dumps(dict(cell=c, port=port, pulses=len(r["pulses"]), wall_s=round(r["wall_s"]),
                          word="".join("F" if p["fire"] else "s" if p["kind"] != "dose" else "d" for p in r["pulses"]))))


if __name__ == "__main__":
    main()
