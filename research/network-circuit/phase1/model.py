"""The guarded model of `CircuitNetwork.lean`, in Python: same state, same step, same margins. Phase 1, exploratory.

Integers only. One dose of a port is D units of that port's score; the gap of a port and the bounds of its
read error are given in the same units. The four ports, in the order of the Lean file: the source port of A
(`a1`), the return port of A (`a2`), the forward port of B (`b1`), the source port of B (`b2`).
"""
D = 100000
PORTS = ("a1", "a2", "b1", "b2")
PROBES = {("A", False): "a1", ("A", True): "a1", ("B", False): "b2", ("B", True): "b2", "forward": "b1", "back": "a2"}
ROUTE = {("A", True): ["forward"], ("B", True): ["back"]}


def seed(a0, a1, b0, b1):
    """`calendar a0 a1 b0 b1` of the Lean file."""
    return [("A", False)] * a0 + [("A", True)] * a1 + [("B", False)] * b0 + [("B", True)] * b1


def steps(a0, a1, b0, b1):
    return (a0 + 2 * a1 + b0 + 2 * b1) * 4


def run(gap, pending, n, forced=None):
    """`run` with zero error for n steps. `forced` maps a step to the decision imposed there (a read without room).
    Returns the log [(step, probe, port, score, fire)], the writes and what is still pending."""
    pending, writes, log = list(pending), dict.fromkeys(PORTS, 0), []
    for _ in range(n):
        if not pending:
            break
        probe = pending.pop(0)
        port = PROBES[probe]
        score = -gap[port] + D * writes[port]
        fire = score >= 0 if forced is None or len(log) not in forced else forced[len(log)]
        if fire:
            pending += ROUTE.get(probe, [])
        else:
            writes[port] += 1
        log.append((len(log), probe, port, score, fire))
    return log, writes, pending


def dated_run(gap, calendar, latency=0.95):
    """The zero-error run in the order of the dates of a calendar of `calendars.py`, instead of the queue order of
    the Lean model: sources at their dates, a wire pulse `latency + delay` after the start of the source pulse that
    fired inside the gate of its edge. Returns the word and the writes of each port."""
    import heapq
    name = {("a", 1): "a1", ("a", 2): "a2", ("b", 1): "b1", ("b", 2): "b2"}
    queue = [(float(d), i, name[(c, p)], True) for i, (d, c, p) in enumerate(calendar["sources"])]
    heapq.heapify(queue)
    writes, words, order = dict.fromkeys(PORTS, 0), dict.fromkeys(PORTS, ""), len(queue)
    while queue:
        date, _, port, source = heapq.heappop(queue)
        fire = -gap[port] + D * writes[port] >= 0
        words[port] += "F" if fire else "s"
        if not fire:
            writes[port] += 1
        elif source:
            for edge in calendar["edges"]:
                if edge["source"] == port[0] and edge["gate"][0] <= date + latency < edge["gate"][1]:
                    heapq.heappush(queue, (date + latency + edge["delay"], order, name[(edge["cell"], edge["port"])], False))
                    order += 1
    return words, writes


def room(score, lo, hi):
    """How far the read is from changing its decision under an error in [lo, hi]; `HasRoom` is room >= 0 for a FIRE
    and room > 0 for a silent read."""
    return score + lo if score >= 0 else -(score + hi)


def has_room(score, lo, hi):
    return (score < 0 and score + hi < 0) or (score >= 0 and score + lo >= 0)


def port_margins(gap, lo, hi, pending, n):
    """`PortMargins`: every read of the zero-error run has room for the bounds of its port."""
    return all(has_room(score, lo[port], hi[port]) for _, _, port, score, _ in run(gap, pending, n)[0])


def outcomes(gap, lo, hi, pending, n):
    """Every terminal state reachable when each read without room is decided either way and each read with room is
    decided by its score: a set of (writes, fires) per port, both in the order of PORTS. One element if
    `port_margins` holds. Runs that differ only in which read of a port was the silent one are counted once."""
    start = (tuple(pending), (0,) * len(PORTS), (0,) * len(PORTS))
    seen, frontier, done = {start}, [start], set()
    for _ in range(n):
        following = []
        for queue, writes, fires in frontier:
            if not queue:
                done.add((writes, fires))
                continue
            probe, i = queue[0], PORTS.index(PROBES[queue[0]])
            score = -gap[PORTS[i]] + D * writes[i]
            decisions = [score >= 0] if has_room(score, lo[PORTS[i]], hi[PORTS[i]]) else [True, False]
            for fire in decisions:
                bump = tuple(int(j == i) for j in range(len(PORTS)))
                state = (queue[1:] + tuple(ROUTE.get(probe, []) if fire else []),
                         writes if fire else tuple(map(sum, zip(writes, bump))), tuple(map(sum, zip(fires, bump))) if fire else fires)
                if state not in seen:
                    seen.add(state)
                    following.append(state)
        frontier = following
    assert all(not queue for queue, _, _ in frontier)
    return done | {(writes, fires) for _, writes, fires in frontier}


def word(log, port):
    return "".join("F" if fire else "s" for _, _, p, _, fire in log if p == port)
