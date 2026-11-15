"""The robust scan of campaign 3: one port of one cell of the ring, measured with every other port idle.

  robustscan.py OUT SECTION SEED CELL PORT NGSPICE PDK [force]

It is `../network-circuit/phase1/cellscan.py`, which is frozen by hash in the manifests of campaigns 1 and 2 and is
not edited, with only the two changes of `PREDICTION.md` of campaign 3:

1. **Two more fired states.** Right after the read 16 units after the reference, one dose is written with a
   clock-only pulse, the port is read isolated, a second dose is written, and the port is read again. An imposed
   leak on this port alone then brings the stored voltage back to the state of the first FIRE (within 2 uV, in
   steps of at most 1.2 mV, as the bisection does), and the coarse descent and the bisection go on unchanged.
2. **Contradictory states.** At the end of the bisection, if among the isolated reads a state that fired is not
   stronger than a state that stayed silent (the largest stored voltage that fired is not below the smallest that
   stayed silent), the port is brought back to each of the two disputed states, the largest stored voltage that
   fired and the smallest that stayed silent (within 2 uV), and each is read twice more, isolated. One round at
   most. The repeats are recorded with the kind "repeat" and the date of the read they repeat; the majority is
   taken by the prediction step, not here.

The stored voltage and FIRE of an isolated read are judged here as the records judge them: the stored voltage is
the mean of (stored node - summing node) over the 28 us that end 2 us before the read, as `measure.pulse_record`
takes it, and a FIRE is a rise of the protection latch through 0.9 V within one unit and 2 us of the start of the
read. `force` (rehearsal only, never in the campaign) makes the round of repeats happen even without a
contradiction, so that its cost can be measured.
"""
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
NET = HERE.parent / "network-circuit"
sys.path.insert(0, str(NET))
import measure
import net

CELLS = ("a", "b", "c")
ORIGIN = 100e-6
PERIOD = 22 * net.TU
LEAK_PER_MV = 4.42e-10          # conductance that loses about 1 mV in 170 us; refined on the run itself
FIRE_WINDOW = net.TU + 2e-6     # a FIRE rises within one unit and 2 us of the start of the read
ISOLATED = ("read", "reference")


def scan(out, section, seed, c, port, ngspice, pdk, coarse=0.25e-3, bracket=20e-6, force_round=False):
    text = net.deck(cells=CELLS, section=section, leak_per_port=True)
    s = net.Session(out, text, CELLS, ngspice, pdk, seed=seed, stop_s=0.06)
    me, leak, state, pulses = f"v(x{c}.vmem{port})", f"vgl{c}{port}", dict(t=ORIGIN, scale=LEAK_PER_MV, v=None), []
    isolated = []                                       # (date, the state v to come back to, stored voltage u, FIRE)

    def read(date, amp=1, **more):
        """One pulse at `date`; returns (FIRE?, latency)."""
        date = net.snap(date)
        s.run(date - net.LEAD - 1e-6)
        u = s.mean(me, date - 30e-6, date - 2e-6) - s.mean(f"v(x{c}.x{port}.sum)", date - 30e-6, date - 2e-6)
        was = s.protected(c)
        s.pulse(c, port, date, amp)
        t = s.run(date + 25e-6, watch=() if was else (c,))
        pulses.append((date, more))
        if was or t >= date + 25e-6 - 1e-12 or not s.protected(c):
            fired, latency = False, None
        else:
            when = s.fire_date(c, date - 1e-6)
            s.run(date + 25e-6)
            fired, latency = True, (when - date) / net.TU
        if more.get("kind") in ISOLATED:
            isolated.append(dict(date=date, v=state["v"], u=u, fire=bool(fired and latency * net.TU <= FIRE_WINDOW)))
        return fired, latency

    def period(kind, delta=0.0, label=None, **more):
        """22 units: a read, a clock-only dose or nothing, then an imposed leak of about `delta` volts on this port."""
        date = state["t"]
        state["t"] += PERIOD
        ok = None
        if kind != "idle":
            fired, latency = read(date, amp=1 if kind == "read" else 0, kind=label or kind, **more)
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
        state["v"] = after
        return ok, after

    def move(target):
        """Doses and imposed leaks until the stored voltage is within 2 uV of `target`, as the bisection does."""
        for _ in range(40):
            gap = target - state["v"]
            if gap < -2e-6:
                period("dose")
            elif gap <= 0.05e-3:
                if gap > 2e-6:
                    period("idle", gap)
                break
            else:
                period("idle", min(gap - 0.03e-3, 1.2e-3))

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
    first = state["v"]                                      # change 1: two more fired states, one and two doses further
    period("dose")
    period("read", label="read", robust="one dose further")
    period("dose")
    period("read", label="read", robust="two doses further")
    move(first)
    v = state["v"]
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
        move(target)
        pre = state["v"]
        ok, v = period("read")
        if ok:
            correct = max(correct, pre)
        else:
            incorrect = min(incorrect, pre)
    fired = [x for x in isolated if x["fire"]]               # change 2: one round of repeats on contradictory states
    silent = [x for x in isolated if not x["fire"]]
    contradictory = bool(fired and silent and max(x["u"] for x in fired) >= min(x["u"] for x in silent))
    disputed = []
    if (contradictory or force_round) and fired and silent:
        for x in (max(fired, key=lambda y: y["u"]), min(silent, key=lambda y: y["u"])):
            repeats = []
            for _ in range(2):
                move(x["v"])
                repeats.append(net.snap(state["t"]))
                period("read", label="repeat", repeat_of=x["date"])
            disputed.append(dict(date=x["date"], repeats=repeats, fired_at_first=x["fire"]))
    s.run(state["t"])
    raw = s.close()
    tr = measure.Trace(raw)
    records = [dict(measure.pulse_record(tr, c, port, d), **more) for d, more in pulses]
    other = [x for x in CELLS if x != c][0]
    idle = dict(fires_of_the_other_cell=len(tr.crossings(f"v(x{other}.p)", 0.0, tr.t[-1])),
                drift_of_the_other_cell_uV=[(tr.u(other, p, tr.t[-1] - 40e-6, tr.t[-1] - 2e-6) - tr.u(other, p, ORIGIN - 40e-6, ORIGIN - 5e-6)) * 1e6 for p in net.PORTS])
    return dict(kind="robustscan", section=section, seed=seed, cell=c, port=port, pulses=records, bracket_stored_V=[correct, incorrect], idle=idle,
                contradictory=contradictory, forced_round=bool(force_round), disputed=disputed,
                points=int(len(tr.t)), raw_sha256=net.sim.digest(raw), deck_sha256=net.sim.digest(Path(out) / "input.spice"))


def main():
    out, section, seed, c, port, ngspice, pdk = sys.argv[1:8]
    force = len(sys.argv) > 8 and sys.argv[8] == "force"
    began = time.time()
    r = scan(Path(out), section, None if seed == "none" else int(seed), c, int(port), Path(ngspice), Path(pdk), force_round=force)
    r["wall_s"] = time.time() - began
    (Path(out) / "result.json").write_text(json.dumps(r, indent=1) + "\n")
    (Path(out) / "pdk").unlink()
    print(json.dumps(dict(cell=c, port=port, pulses=len(r["pulses"]), wall_s=round(r["wall_s"]), contradictory=r["contradictory"], disputed=len(r["disputed"]),
                          simulated_ms=round(max(p["date_s"] for p in r["pulses"]) * 1e3, 2),
                          word="".join("F" if p["fire"] else "s" if p["kind"] != "dose" else "d" for p in r["pulses"]))))


if __name__ == "__main__":
    main()
