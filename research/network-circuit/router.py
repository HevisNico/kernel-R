"""A dated router around the transistor-level cells: who receives a pulse, and when. Phase 0, exploratory.

The router is the part of the network that the circuit does not have. It is ideal and lives outside the
simulator:

- a **source** is an external pulse on a port at a date fixed in advance;
- an **edge** carries each FIRE of its source cell to a port of its target cell: a pulse of the standard
  shape starts there `delay` after the date at which the protection latch of the source cell rose, if that
  date is inside the gate of the edge. The date is moved up to the next date that is 0.1 us after a noise
  sample (at most 0.4 us later), as every edge of the stimulus must be;
- nothing else passes between cells.

`run()` plays a calendar on a deck: it stops the simulator at each FIRE and before each pulse, schedules
the pulses, and records every occurrence with what the waveform shows for it. Dates are given in time
units of 20 us from an origin; the records keep seconds.
"""
import heapq
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import measure
import net

ORIGIN = 100e-6                 # date of calendar time 0: the preset of the integrators is over at 2.1 us


def native_reciprocal():
    """The calendar of the milestone-3 witness of ../network-stability (RECIPROCAL_CLOSURE.md), in its own time units.
    Cell a is native cell A, cell b is native cell B. Port 1 of a is native port 0 (its sources), port 2 of a is native
    port 2 (the return wire); port 1 of b is native port 1 (the forward wire), port 2 of b is native port 2 (its
    sources). The gates are the date bands in which the witness routes: the three forward sources of A, then the
    sources of B from its first FIRE. The sixteen sources of B from 480 are after the horizon and are left out."""
    return dict(name="native reciprocal witness",
                sources=[(d, "a", 1) for d in (0, 8, 16, 24, 32, 160, 168, 176)] + [(d, "b", 2) for d in (320, 328, 336, 344, 352, 360, 368)],
                edges=[dict(name="forward", source="a", cell="b", port=1, delay=7 / 20, gate=(160, 184)),
                       dict(name="return", source="b", cell="a", port=2, delay=7 / 20, gate=(344, 376))],
                horizon=4599 / 10)


def longer_reciprocal():
    """The same construction with enough sources for this circuit to finish learning: its ports need four doses where
    the native witness needs three or one. Eight forward sources instead of three, ten sources of B instead of seven,
    and gates that follow."""
    return dict(name="reciprocal construction, longer trains",
                sources=[(d, "a", 1) for d in (0, 8, 16, 24, 32)] + [(160 + 8 * k, "a", 1) for k in range(8)] + [(320 + 8 * k, "b", 2) for k in range(10)],
                edges=[dict(name="forward", source="a", cell="b", port=1, delay=7 / 20, gate=(160, 224)),
                       dict(name="return", source="b", cell="a", port=2, delay=7 / 20, gate=(344, 400))],
                horizon=4599 / 10)


def refusal(guard, protected, previous, date):
    """Why the guard refuses a pulse that would start at `date` (seconds) on a cell whose previous pulse started at
    `previous` (None if there was none), or None if it lets it through."""
    if guard is None:
        return None
    if protected:
        return "protected"
    if previous is not None and date - previous < guard * net.TU - 1e-9:
        return "too soon after the previous pulse of the cell"
    return None


def run(out, calendar, ngspice, pdk, cells=("a", "b"), seed=None, guard=None, **deck_args):
    """`guard`, if given, is the least number of time units between the starts of two pulses on one cell. The router
    then refuses, and records as refused, a pulse that would start sooner after the previous pulse of its cell, or
    while its cell is protected. A refused pulse is not delivered and is not put back in the queue."""
    text = net.deck(cells=cells, **deck_args)
    at = lambda units: ORIGIN + units * net.TU
    horizon = at(calendar["horizon"])
    began = time.time()
    s = net.Session(out, text, cells, ngspice, pdk, seed=seed, stop_s=horizon + 50e-6)
    queue, order, occurrences, fires = [], 0, [], []
    for date, c, p in calendar["sources"]:
        heapq.heappush(queue, (net.snap(at(date)), order, dict(cell=c, port=p, origin="source", calendar_date=date)))
        order += 1
    protected = {c: False for c in cells}
    last_fire = {c: 0.0 for c in cells}
    last_pulse = {c: None for c in cells}
    while True:
        target = min(queue[0][0] - net.LEAD - 1e-6, horizon) if queue else horizon
        now = s.run(target, watch=[c for c in cells if not protected[c]])
        for c in cells:
            state = s.protected(c)
            if state and not protected[c]:                  # a FIRE: date it, say which pulses were being admitted, route it
                when = s.fire_date(c, last_fire[c])
                last_fire[c] = when
                units = (when - ORIGIN) / net.TU
                causes = [o["id"] for o in occurrences if o["cell"] == c and o["date_s"] <= when <= o["date_s"] + net.TU + 2e-6]
                fire = dict(cell=c, date_s=when, calendar_date=units, during=causes, routed=[])
                for e in calendar["edges"]:
                    if e["source"] == c and e["gate"][0] <= units < e["gate"][1]:
                        date = net.snap(when + e["delay"] * net.TU)
                        heapq.heappush(queue, (date, order, dict(cell=e["cell"], port=e["port"], origin=e["name"], fire_date_s=when)))
                        fire["routed"].append(dict(edge=e["name"], cell=e["cell"], port=e["port"], date_s=date))
                        order += 1
                fires.append(fire)
            protected[c] = state
        if now < target - 1e-12:
            continue                                        # stopped by a FIRE: look again at what is next
        if not queue or now >= horizon - 1e-12:
            if now >= horizon - 1e-12:
                break
            continue
        date, _, o = heapq.heappop(queue)
        o.update(id=len(occurrences), date_s=date, protected_when_scheduled=protected[o["cell"]])
        previous = last_pulse[o["cell"]]
        reason = refusal(guard, protected[o["cell"]], previous, date)
        if reason:
            o.update(delivered=False, refused=reason, since_previous_units=None if previous is None else (date - previous) / net.TU)
        elif date < s.busy[(o["cell"], o["port"])]:         # the port is still in its previous cycle: the testbench cannot deliver
            o["delivered"] = False
        else:
            s.pulse(o["cell"], o["port"], date)
            o["delivered"] = True
            last_pulse[o["cell"]] = date
        occurrences.append(o)
    left = [dict(o, date_s=d) for d, _, o in sorted(queue)]
    raw = s.close()
    tr = measure.Trace(raw)
    for o in occurrences:
        if o["delivered"]:
            o.update(measure.pulse_record(tr, o["cell"], o["port"], o["date_s"]))
    result = dict(calendar=dict(calendar, edges=calendar["edges"]), cells=list(cells), deck=deck_args, seed=seed, guard_units=guard, origin_s=ORIGIN,
                  occurrences=occurrences, fires=fires, still_queued_at_the_horizon=left, wall_s=time.time() - began, points=int(len(tr.t)),
                  raw_sha256=net.sim.digest(raw), deck_sha256=net.sim.digest(Path(out) / "input.spice"),
                  final_u_V={f"{c}{p}": tr.u(c, p, horizon - 30e-6, horizon - 2e-6) for c in cells for p in net.PORTS},
                  initial_u_V={f"{c}{p}": tr.u(c, p, ORIGIN - 40e-6, ORIGIN - 5e-6) for c in cells for p in net.PORTS})
    (Path(out) / "result.json").write_text(json.dumps(result, indent=1) + "\n")
    return result


def word(result):
    """The decision word of each port: s for a silent read that wrote, F for a FIRE, - for a pulse that arrived while the
    cell was protected, r for a pulse the guard refused, x for a pulse the testbench could not deliver."""
    out = {}
    for o in result["occurrences"]:
        key = f"{o['cell']}{o['port']}"
        letter = "r" if o.get("refused") else "x" if not o["delivered"] else "-" if o["protected_at_start"] else "F" if o["fire"] else "s" if o[f"writes{o['port']}"] == 1 else "?"
        out[key] = out.get(key, "") + letter
    return out


if __name__ == "__main__":
    name, out, ngspice, pdk = sys.argv[1:5]
    r = run(Path(out), dict(native=native_reciprocal, longer=longer_reciprocal)[name](), Path(ngspice), Path(pdk))
    print(json.dumps(dict(word=word(r), fires=len(r["fires"]), wall_s=round(r["wall_s"]))))
