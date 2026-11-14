"""What one cell does alone, measured on the deck of the network bench. Phase 0, exploratory.

  percell.py train OUT PORT SPACING COUNT         pulses on one port, SPACING time units apart
  percell.py threshold OUT PORT                   the service threshold of one port, by bisection (isolated reads)
  percell.py history OUT                          how a read depends on what the cell did just before

Each ends with NGSPICE PDK, after an optional `--layout DIR`. One cell (`a`), typical corner, 27 C, junction areas of stage J, no noise:
the cells of the nominal network are this cell twice.
"""
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import measure
import net

C = "a"
ORIGIN = 100e-6
PERIOD = 22 * net.TU            # isolated reads: the spacing of the earlier campaigns
LEAK_PER_MV = 4.42e-10          # conductance that loses about 1 mV in 170 us; refined on the run itself


LAYOUT = Path(sys.argv[sys.argv.index("--layout") + 1]) if "--layout" in sys.argv else None


def session(out, ngspice, pdk, stop_s):
    """With `--layout DIR` the areas and the wire capacitances are those of a layout extraction: DIR/p_areas.csv and
    DIR/p_caps_primary.csv, in the format of stage P of the layout study."""
    extraction = {} if LAYOUT is None else dict(areas=LAYOUT / "p_areas.csv", caps=LAYOUT / "p_caps_primary.csv")
    return net.Session(out, net.deck(cells=(C,), **extraction), (C,), ngspice, pdk, stop_s=stop_s)


def read(s, port, date, amp=1):
    """One pulse at `date`; returns (FIRE?, latency). Leaves the run 25 us after the start of the pulse."""
    s.run(date - net.LEAD - 1e-6)
    was = s.protected(C)
    s.pulse(C, port, date, amp)
    t = s.run(date + 25e-6, watch=() if was else (C,))
    if was or t >= date + 25e-6 - 1e-12 or not s.protected(C):
        return False, None
    when = s.fire_date(C, date - 1e-6)
    s.run(date + 25e-6)
    return True, (when - date) / net.TU


def finish(s, out, pulses, extra):
    raw = s.close()
    tr = measure.Trace(raw)
    records = [dict(measure.pulse_record(tr, C, p, d), **more) for d, p, more in pulses]
    result = dict(extra, cell=C, pulses=records, points=int(len(tr.t)), raw_sha256=net.sim.digest(raw), deck_sha256=net.sim.digest(Path(out) / "input.spice"))
    (Path(out) / "result.json").write_text(json.dumps(result, indent=1) + "\n")
    return result


def train(out, port, spacing, count, ngspice, pdk):
    s = session(out, ngspice, pdk, ORIGIN + (count + 1) * spacing * net.TU)
    pulses = []
    for k in range(count):
        date = net.snap(ORIGIN + k * spacing * net.TU)
        read(s, port, date)
        pulses.append((date, port, dict(index=k)))
    s.run(pulses[-1][0] + net.CYCLE + 5e-6)
    return finish(s, out, pulses, dict(kind="train", port=port, spacing_units=spacing))


def threshold(out, port, ngspice, pdk, coarse=0.25e-3, bracket=20e-6):
    """Isolated reads, one per 22 units. Between two reads an imposed leak, a clock-only dose or nothing moves the stored
    voltage; the scan halves the bracket between the highest stored voltage read correctly and the lowest read incorrectly."""
    s = session(out, ngspice, pdk, 0.05)
    me, state, pulses = f"v(x{C}.vmem{port})", dict(k=0, scale=LEAK_PER_MV, drift=0.0), []

    def period(kind, delta=0.0):
        date = net.snap(ORIGIN + state["k"] * PERIOD)
        state["k"] += 1
        ok, latency = None, None
        if kind != "idle":
            fired, latency = read(s, port, date, amp=1 if kind == "read" else 0)
            pulses.append((date, port, dict(kind=kind)))
            ok = bool(fired and latency <= 1.0) if kind == "read" else None
        s.run(date + 200e-6)
        before = s.mean(me, date + 160e-6, date + 195e-6)
        if delta > 0:
            s.set("vgl", delta * 1e3 * state["scale"])
            s.run(date + 370e-6)
            s.set("vgl", 0)
        s.run(date + PERIOD - 3e-6)
        after = s.mean(me, date + 400e-6, date + 435e-6)
        if delta > 0 and after - before > 0.2 * delta:
            state["scale"] *= delta / (after - before)
        if kind == "idle" and delta == 0:
            state["drift"] = after - before
        return ok, latency, after

    _, _, v = period("idle")
    pre = v
    for _ in range(30):
        ok, _, v_new = period("read")
        if ok:
            break
        pre, v = v_new, v_new
    else:
        s.kill()
        raise RuntimeError("no correct read after thirty reads")
    correct, incorrect, v = pre, None, v_new
    for _ in range(40):
        pre = v
        ok, _, v = period("read", coarse)
        if not ok:
            incorrect = pre
            break
        correct = pre
    assert incorrect is not None and incorrect > correct
    for _ in range(16):
        if incorrect - correct <= bracket:
            break
        target = (correct + incorrect) / 2
        for _ in range(40):
            gap = target - v
            if gap < -2e-6:
                _, _, v = period("dose")
            elif gap <= 0.05e-3:
                if gap > 2e-6:
                    _, _, v = period("idle", gap)
                break
            else:
                _, _, v = period("idle", min(gap - 0.03e-3, 1.2e-3))
        pre = v
        ok, _, v = period("read")
        if ok:
            correct = max(correct, pre)
        else:
            incorrect = min(incorrect, pre)
    return finish(s, out, pulses, dict(kind="threshold", port=port, bracket_stored_V=[correct, incorrect]))


def history(out, ngspice, pdk):
    """Port 1 is trained by isolated reads and then read again and again. Before each of these reads port 2 receives a
    pulse, `gap` units earlier: silent while port 2 still learns, a FIRE afterwards. The latency of the read of port 1,
    against that of an isolated read at the same stored voltage, says what the earlier pulse left in the cell."""
    s = session(out, ngspice, pdk, 0.06)
    pulses, t = [], ORIGIN

    def at(date, port, **more):
        date = net.snap(date)
        fired, latency = read(s, port, date)
        pulses.append((date, port, more))
        return fired

    fires = 0
    for k in range(14):                                     # train port 1, isolated; stop after three FIRE
        fires += at(t, 1, role="train")
        t += PERIOD
        if fires == 3:
            break
    gaps = [8, 6.5, 12, 16] + [8, 6.5, 12, 16, 2, 3, 4, 5, 5.5, 6, 7, 10, 22]
    for gap in gaps:                                        # the first four find port 2 untrained: it is silent and writes
        at(t, 2, role="before", gap_units=gap)
        at(t + gap * net.TU, 1, role="test", gap_units=gap)
        t += (gap + 30) * net.TU
    at(t, 1, role="isolated")
    s.run(t + net.CYCLE + 5e-6)
    return finish(s, out, pulses, dict(kind="history"))


def main():
    kind, out = sys.argv[1], Path(sys.argv[2])
    ngspice, pdk = Path(sys.argv[-2]), Path(sys.argv[-1])
    if LAYOUT is not None:
        del sys.argv[sys.argv.index("--layout"):sys.argv.index("--layout") + 2]
    began = time.time()
    if kind == "train":
        r = train(out, int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5]), ngspice, pdk)
    elif kind == "threshold":
        r = threshold(out, int(sys.argv[3]), ngspice, pdk)
    else:
        r = history(out, ngspice, pdk)
    r["wall_s"] = time.time() - began
    (out / "result.json").write_text(json.dumps(r, indent=1) + "\n")
    print(json.dumps(dict(kind=kind, pulses=len(r["pulses"]), wall_s=round(r["wall_s"]),
                          word="".join("-" if p["protected_at_start"] else "F" if p["fire"] else "s" for p in r["pulses"]))))


if __name__ == "__main__":
    main()
