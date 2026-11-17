"""Campaign 4: one simulator session on the deck of the three cells, played from a plan of dated events. The router
of research/network-circuit/router.py with three additions that PREDICTION.md needs, and nothing else:

- **the read-only gate**: before a slot, the cells at rest, the dose bias `idis` of each port is set to zero or
  restored to 8.2 nA (`alter i.x<c>.x<p>.idis dc = ...`), 3 units ahead of the slot;
- **amplitudes**: each external pulse has its own amplitude (0.49 on layer 1, 1 on the lines of c);
- **routed FIRE**: an edge carries a FIRE of its source cell, rising inside its gate window, to its port of c,
  `delay` units after the FIRE, at amplitude 1. An upstream silence sends nothing.

Dates in the plan are in time units of 20 us from the origin of router.py; the records keep seconds.
"""
import heapq
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "network-circuit"))
import measure                                          # noqa: E402
import net                                              # noqa: E402
import router                                           # noqa: E402

ORIGIN = router.ORIGIN


def at(units):
    return ORIGIN + units * net.TU


def play(out, plan, text, ngspice, pdk, seed=None, guard_off=False, noise_id=None, shim=None):
    """plan: dict(cells, horizon (units), gates=[(date_units, {"a1": idis, ...})], sources=[(date_units, cell, port,
    amp)], edges=[dict(name, source, cell, port, delay, gate=(lo, hi), amp)]). Returns the result dict, also written
    as result.json in `out`."""
    cells = tuple(plan["cells"])
    horizon = at(plan["horizon"])
    began = time.time()
    s = net.Session(out, text, cells, ngspice, pdk, seed=seed, stop_s=horizon + 50e-6, noise_id=noise_id, shim=shim)
    if guard_off:
        s.set("vfire", 0.0)                             # the matched guard-disabled probe: no cell can fire
    queue, order = [], 0
    for date, settings in plan["gates"]:
        heapq.heappush(queue, (at(date), 0, order, dict(kind="gate", settings=settings, calendar_date=date)))
        order += 1
    for date, c, p, amp in plan["sources"]:
        heapq.heappush(queue, (net.snap(at(date)), 1, order, dict(kind="pulse", cell=c, port=p, amp=amp, origin="source", calendar_date=date)))
        order += 1
    protected = {c: False for c in cells}
    last_fire = {c: 0.0 for c in cells}
    occurrences, fires, gates = [], [], []
    while True:
        if queue:
            d0, kind, _, _ = queue[0]
            target = min(d0 - (net.LEAD + 1e-6 if kind == 1 else 0.0), horizon)
        else:
            target = horizon
        if queue and s.started and s.now >= target - 1e-12:
            now = s.now                                 # already there (several events at one date): no new step
        else:
            now = s.run(target, watch=[c for c in cells if not protected[c]])
        for c in cells:
            state = s.protected(c)
            if state and not protected[c]:
                when = s.fire_date(c, last_fire[c])
                last_fire[c] = when
                units = (when - ORIGIN) / net.TU
                fire = dict(cell=c, date_s=when, calendar_date=units, routed=[])
                for e in plan["edges"]:
                    if e["source"] == c and e["gate"][0] <= units < e["gate"][1]:
                        date = net.snap(when + e["delay"] * net.TU)
                        heapq.heappush(queue, (date, 1, order, dict(kind="pulse", cell=e["cell"], port=e["port"], amp=e["amp"],
                                                                     origin=e["name"], fire_date_s=when)))
                        fire["routed"].append(dict(edge=e["name"], cell=e["cell"], port=e["port"], date_s=date))
                        order += 1
                fires.append(fire)
            protected[c] = state
        if now < target - 1e-12:
            continue                                    # stopped by a FIRE
        if now >= horizon - 1e-12:
            break
        if not queue:
            continue
        date, kind, _, o = heapq.heappop(queue)
        if o["kind"] == "gate":
            for name, value in o["settings"].items():
                s.set(f"i.x{name[0]}.x{name[1]}.idis", value)
            gates.append(dict(date_s=date, calendar_date=o["calendar_date"], settings=o["settings"],
                              protected={c: protected[c] for c in cells}))
            continue
        o.update(id=len(occurrences), date_s=date, protected_when_scheduled=protected[o["cell"]])
        if date < s.busy[(o["cell"], o["port"])]:
            o["delivered"] = False                      # the port is still in its previous cycle
        else:
            s.pulse(o["cell"], o["port"], date, amp=o["amp"])
            o["delivered"] = True
        occurrences.append(o)
    left = [dict(o, date_s=d) for d, _, _, o in sorted(queue) if o["kind"] == "pulse"]
    raw = s.close()
    tr = measure.Trace(raw)
    result = dict(plan=plan, cells=list(cells), seed=seed, guard_off=guard_off, origin_s=ORIGIN, occurrences=occurrences,
                  fires=fires, gates=gates, still_queued_at_the_horizon=left, wall_s=time.time() - began, points=int(len(tr.t)),
                  waveform_ends_s=float(tr.t[-1]), horizon_s=horizon)
    (Path(out) / "result.json").write_text(json.dumps(result, indent=1) + "\n")
    return result, tr
