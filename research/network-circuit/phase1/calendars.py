"""The calendars of phase 1: the same reciprocal construction at two spacings. Phase 1, exploratory.

`reciprocal(18)` is the calendar on which the hypotheses hold by construction: two pulses on one cell are
never closer than 16 units, whatever the latencies. `reciprocal(8)` is the negative control: the spacing of
the milestone-3 witness, at which a pulse helps the next one by about half a dose. Neither has been run on
a cell with mismatch.

A calendar is what `router.run` plays: sources (date, cell, port), edges with a delay and a date band, a
horizon. Dates in time units of 20 us. Cell a is A: port 1 its sources, port 2 the return wire. Cell b is
B: port 1 the forward wire, port 2 its sources.
"""
BIRTH, GATE = 8, 10             # sources of each cell before its gate opens, and while it is open
DELAY = 7 / 20                  # of both edges, as in the witness
OFFSET = 2                      # B's sources are 2 units after A's grid, so that no two sources share a date
LATENCY = (0.0, 1.06)           # a FIRE rises during the pulse, or within 0.06 unit of its end
SNAP = 0.02                     # a wire pulse starts at most 0.4 us after its nominal date
SEPARATION = 16                 # least distance between the starts of two pulses on one cell, in the hypotheses
PROTECTED_UNTIL = 6.5           # after the start of a firing pulse; measured 5.2 to 6.4 on the instances


def reciprocal(spacing):
    a = [spacing * k for k in range(BIRTH + GATE)]
    b = [OFFSET + spacing * k for k in range(BIRTH)] + [OFFSET + spacing * (BIRTH + GATE + k) for k in range(GATE)]
    forward = (spacing * BIRTH, spacing * (BIRTH + GATE))
    back = (OFFSET + spacing * (BIRTH + GATE), OFFSET + spacing * (BIRTH + 2 * GATE))
    return dict(name=f"reciprocal construction, pulses {spacing} units apart",
                sources=sorted([(d, "a", 1) for d in a] + [(d, "b", 2) for d in b]),
                edges=[dict(name="forward", source="a", cell="b", port=1, delay=DELAY, gate=forward),
                       dict(name="return", source="b", cell="a", port=2, delay=DELAY, gate=back)],
                horizon=b[-1] + 12)


def counts(calendar):
    """(a0, a1, b0, b1): the sources of A before and inside the forward gate, those of B before and inside the return
    gate. Fails if a FIRE of a source could fall on either side of a gate boundary, or if a source is after its gate."""
    out = []
    for edge in calendar["edges"]:
        lo, hi = edge["gate"]
        before = inside = 0
        for date, c, _ in calendar["sources"]:
            if c != edge["source"]:
                continue
            first, last = date + LATENCY[0], date + LATENCY[1]
            if last < lo:
                assert inside == 0
                before += 1
            else:
                assert lo <= first and last < hi, (edge["name"], date)
                inside += 1
        out += [before, inside]
    return tuple(out)


def pulses(calendar):
    """Every pulse the calendar can produce, as (cell, port, earliest start, latest start)."""
    out = [(c, p, float(d), float(d)) for d, c, p in calendar["sources"]]
    for edge in calendar["edges"]:
        for d, c, _ in calendar["sources"]:
            if c == edge["source"] and edge["gate"][0] <= d < edge["gate"][1]:
                out.append((edge["cell"], edge["port"], d + LATENCY[0] + edge["delay"], d + LATENCY[1] + edge["delay"] + SNAP))
    return out


def separation(calendar):
    """The least distance that the calendar guarantees between the starts of two pulses on one cell, for every
    latency: per cell, the smallest (earliest start of the later pulse) - (latest start of the earlier one)."""
    out = {}
    for cell in sorted({c for c, *_ in pulses(calendar)}):
        mine = sorted((lo, hi) for c, _, lo, hi in pulses(calendar) if c == cell)
        out[cell] = min(later[0] - earlier[1] for earlier, later in zip(mine, mine[1:]))
    return out


def holds_by_construction(calendar):
    """Same-cell separation of at least 16 units, hence no arrival on a protected cell either."""
    return min(separation(calendar).values()) >= SEPARATION > PROTECTED_UNTIL


if __name__ == "__main__":
    for spacing in (18, 8):
        c = reciprocal(spacing)
        print(spacing, counts(c), {k: round(v, 2) for k, v in separation(c).items()}, holds_by_construction(c), "horizon", c["horizon"])
