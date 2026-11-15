"""The periodic ring of N R cells at transistor level: its ports, its calendar, its model. Phase 0 of campaign 2,
design only: nothing here has been run on a cell with mismatch.

The ring has N cells, `a` (the root) then the relays `b`, `c`, ... Its ports, in the order a pulse meets them:

    port 0      a1   the launch port of the root: one external pulse per lap
    port k      <k-th relay>1, for k = 1 .. N-1: the forward wire from the cell before
    port N      a2   the return port of the root: the wire from the last relay

Port 2 of each relay is never pulsed. A lap starts every `period` units. The router (`../network-circuit/router.py`,
unchanged) carries a FIRE of the root to the first relay only if it rises within `GATE` units of a launch date:
one edge per lap, each with its own date band. A FIRE of the root on its return port is outside every band and
is routed nowhere: the return port only acknowledges. A FIRE of a relay is always carried to the next port.

Timing. `reach` is the least time between a launch and the pulse it can bring back on the return port; each wire
has the delay reach / N. With FIRE latencies between 0 and 1.06 unit and wire pulses at most 0.02 unit late, the
return pulse of a lap starts between `reach` and `reach + 0.02 + N x 1.08` units after the launch date. The period
adds `rest` units after the latest return. With reach = 17 and rest = 16.5 two pulses of one cell are never closer
than 16 units, whatever the latencies, and every lap is over before the next one starts.

Dates in time units of 20 us, as everywhere in `../network-circuit`.
"""
import math

NAMES = "abcdefgh"
LATENCY = (0.0, 1.06)           # a FIRE rises during the pulse, or within 0.06 unit of its end (phase 1)
SNAP = 0.02                     # a pulse starts at most 0.4 us after its nominal date
SEPARATION = 16                 # least distance between the starts of two pulses on one cell, in the hypotheses
PROTECTED_UNTIL = 6.5           # after the start of a firing pulse; measured 5.2 to 6.4 on the instances
GATE = 2                        # a FIRE of the root is routed forward within this many units of a launch date
REACH, REST = 17.0, 16.5        # the timing condition
CONTROL_ARRIVAL = 8.0           # the negative control: the return pulse starts about this long after the launch,
CONTROL_LATENCY = 0.9           # for the FIRE latencies seen on the nominal cell (0.87 to 0.92 unit). Not by construction
SETTLE = 12                     # units simulated after the latest return of the last lap


def cells(n):
    assert 2 <= n <= len(NAMES)
    return tuple(NAMES[:n])


def ports(n):
    """The N + 1 ports in the order of the chain."""
    return ["a1"] + [c + "1" for c in cells(n)[1:]] + ["a2"]


def period(n, reach=REACH, rest=REST):
    return math.ceil(reach + SNAP + n * (LATENCY[1] + SNAP) + rest)


def ring(n, laps, reach=REACH, rest=REST, period_units=None):
    """The calendar that `router.run` plays: `laps` launches, one per period."""
    names, P, delay = cells(n), period_units or period(n, reach, rest), reach / n
    horizon = (laps - 1) * P + reach + SNAP + n * (LATENCY[1] + SNAP) + SETTLE
    edges = [dict(name="forward a", source="a", cell="b", port=1, delay=delay, gate=(lap * P, lap * P + GATE)) for lap in range(laps)]
    for k in range(1, n):
        last = k == n - 1
        edges.append(dict(name="return" if last else f"forward {names[k]}", source=names[k], cell="a" if last else names[k + 1],
                          port=2 if last else 1, delay=delay, gate=(0, horizon + 1)))
    return dict(name=f"periodic ring of {n} cells, {laps} laps of {P} units, return at least {reach:g} units after the launch",
                n=n, laps=laps, period=P, reach=reach, rest=rest, sources=[(lap * P, "a", 1) for lap in range(laps)], edges=edges, horizon=horizon)


def train(n, reads=10, spacing=18, offset=2):
    """The measure of each port alone at the spacing of the closest pulses of the ring: sources only. The launch port
    of the root receives `reads` pulses `spacing` units apart, then its return port does; the forward port of each
    relay receives its `reads` pulses meanwhile, `offset` units later per relay, so that no two pulses share a date."""
    assert (n - 1) * offset < spacing
    sources = [(spacing * (i * reads + k), "a", port) for i, port in enumerate((1, 2)) for k in range(reads)]
    sources += [(spacing * k + offset * j, c, 1) for j, c in enumerate(cells(n)[1:], start=1) for k in range(reads)]
    return dict(name=f"each port of a ring of {n} cells alone, {reads} reads {spacing} units apart", n=n, sources=sorted(sources), edges=[],
                horizon=spacing * 2 * reads + spacing // 2)


def control(n, laps):
    """The negative control, outside the timing condition on the root only: the wires are shortened so that the return
    pulse starts about 8 units after the launch, as in the control of campaign 1, and the period keeps the pulses of
    each relay 16 units apart."""
    reach = CONTROL_ARRIVAL - CONTROL_LATENCY * n
    step = LATENCY[1] + SNAP
    P = math.ceil(max(reach + SNAP + n * step + CONTROL_ARRIVAL, SEPARATION + SNAP + (n - 1) * step))
    return ring(n, laps, reach, P - reach - SNAP - n * step, P)


def windows(calendar):
    """Every pulse the calendar can produce, as (cell, port index in the chain, lap, earliest start, latest start)."""
    n, P, delay = calendar["n"], calendar["period"], calendar["reach"] / calendar["n"]
    names, out = cells(n), []
    for lap in range(calendar["laps"]):
        for k in range(n + 1):
            cell = "a" if k in (0, n) else names[k]
            out.append((cell, k, lap, lap * P + k * (delay + LATENCY[0]), lap * P + SNAP + k * (delay + LATENCY[1] + SNAP)))
    return out


def separation(calendar):
    """The least distance that the calendar guarantees between the starts of two pulses on one cell, for every
    latency and whichever pulses exist: per cell, the smallest (earliest start of the later) - (latest start of the
    earlier) over consecutive windows."""
    out = {}
    for cell in cells(calendar["n"]):
        mine = sorted((lo, hi) for c, _, _, lo, hi in windows(calendar) if c == cell)
        out[cell] = min(later[0] - earlier[1] for earlier, later in zip(mine, mine[1:]))
    return out


def gates_hold(calendar):
    """Every launch FIRE of the root falls inside the band of its lap, and every return FIRE outside every band."""
    n, P = calendar["n"], calendar["period"]
    bands = [e["gate"] for e in calendar["edges"] if e["source"] == "a"]
    for _, k, lap, lo, hi in windows(calendar):
        first, last = lo + LATENCY[0], hi + LATENCY[1]
        if k == 0 and not (bands[lap][0] <= first and last < bands[lap][1]):
            return False
        if k == n and any(b[0] <= last and first < b[1] for b in bands):
            return False
    return True


def holds_by_construction(calendar):
    """Same-cell separation of at least 16 units (hence no arrival on a protected cell either), the launch gate, and
    a lap that is over, with its return port out of its cycle, before the next launch."""
    return min(separation(calendar).values()) >= SEPARATION > PROTECTED_UNTIL and gates_hold(calendar)


def zero_error(needs, laps):
    """The run of the model with zero read error. `needs[k]` is the number of silent reads of port k before its first
    FIRE. Returns the word of each port (s: a silent read and one dose, F: a FIRE), the lap of the freeze (the lap of
    the last write, counted from 1; 0 if nothing is written) and the pulses of each port after its last write."""
    words, arriving, freeze = [], laps, 0
    first = 1                                               # the lap at which the port receives its first pulse
    for need in needs:
        silent = min(need, arriving)
        words.append("s" * silent + "F" * (arriving - silent))
        if silent:
            freeze = max(freeze, first + silent - 1)
        first += silent
        arriving -= silent
    return dict(words=words, freeze_lap=freeze, after_the_last_write=[len(w) - 1 - w.rfind("s") for w in words])


def chain_run(needs, laps):
    """The same run, step by step in the queue order of the Lean model (`RingNetwork.lean`): the launches are pending
    at the start, a FIRE of port k < N appends a pulse for port k + 1. Returns the words."""
    n = len(needs) - 1
    pending, writes, words = [0] * laps, [0] * (n + 1), [""] * (n + 1)
    while pending:
        k = pending.pop(0)
        if writes[k] >= needs[k]:
            words[k] += "F"
            if k < n:
                pending.append(k + 1)
        else:
            words[k] += "s"
            writes[k] += 1
    return words


def laps_for(needs, after=10):
    """Enough laps for `after` laps after the predicted freeze."""
    return sum(needs) + after


if __name__ == "__main__":
    import json
    for n in (3, 4, 5, 6):
        for c in (ring(n, laps_for([4] * (n + 1))), control(n, laps_for([4] * (n + 1)))):
            print(json.dumps(dict(n=n, laps=c["laps"], period=c["period"], delay=round(c["reach"] / n, 4), horizon=round(c["horizon"], 2),
                                  simulated_ms=round(c["horizon"] * 0.02, 2), separation={k: round(v, 2) for k, v in separation(c).items()},
                                  gates_hold=gates_hold(c), holds_by_construction=holds_by_construction(c))))
