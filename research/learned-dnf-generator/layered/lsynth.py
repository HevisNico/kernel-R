"""Synthetic layered traces from the additive model (LAYERED_GENERATOR_DESIGN.md 4(b)). No circuit, no simulation:
every score is the guarded additive score of LayeredMonotoneTarget.lean's Cell plus a residual chosen by a rule, and
every date comes from a fixed calendar.

`design(tag, M, net, function)` gives a network its parameters, in the units of the campaigns (THETA = 100 000, need
3, write limit 5, dose 10 000, budgets 2 000 on every cell):

  both    initial gain THETA/2 - 2.5 d on each port   (a pair; stop 3)
  either  initial gain THETA - 2.5 d on each port      (each line alone; stop 3 per group)
  copy    initial gain THETA - 2.5 d on port 0, 0 on port 1

Layer-1 cells read the external inputs directly (delay 0, as in LayeredMonotoneExample); routed lines between
layers have delay 3/2.

`observation(raw, rule)` fills the training trace and the tests. The calendar is strictly sequential, as the layered
separation premise requires (LayeredMonotoneTarget.lean:224-241): one batch per (layer, cell, group, round) in that
order, one slot each, then the 2^M tests. Slot spacing: 22 units for a network of depth 2 at most, 24 at depth 3, so
that a layer-3 read window (start + 4 + 19) ends before the next slot. External inputs arrive at the slot start; a
FIRE emits 1/2 after its last arrival (or after its start); a routed pulse arrives 3/2 after the emission; a read
starts at its first arrival, or 2 units after its upstream reads start when nothing arrives.

Residual rules: "zero", "plus" (+budget), "minus" (-budget), "seeded:N" (uniform integer in [-budget, budget] from
random.Random(N), one draw per read in the order the trace is built). On a firing read the same residual is added to
its four reference scores, so the firing-submask order and the anchors hold.
"""
from fractions import Fraction as F
import random

from lspec import GROUP_MASK, GROUPS, evaluate

THETA = 100000
RAIL = 10 * THETA
D, NEED, BUDGET = 10000, 3, 2000
LAT, DELAY = F(1, 2), F(3, 2)
LEFT = dict(skew="1/50", deadline="11/10", duration="22")
RIGHT = dict(skew="11/10", deadline="11/5", duration="19")
MASKS2 = [(False, False), (False, True), (True, False), (True, True)]


def s_(x):
    return str(F(x))


def gains(gate):
    half = F(THETA, 2) - F(5, 2) * D
    line = THETA - F(5, 2) * D
    g = dict(both=[half, half], either=[line, line], copy=[line, 0], on=[0, 0], off=[0, 0])[gate]
    assert all(F(v).denominator == 1 for v in g)
    return [int(v) for v in g]


def stimuli(M, layers, l, gate, src):
    """For each active group of a node at layer l (0-based) with sources src, the smallest external pattern (by size,
    then maskIndex) whose predicted lower outputs give exactly the group mask (Node.Valid's last clause)."""
    def lower_out(x):
        out = [j in x for j in range(M)]
        for k in range(l):
            out = [evaluate(n["gate"], tuple(out[s] if s is not None else False for s in n["source"])) for n in layers[k]]
        return out
    pats = sorted((frozenset(j for j in range(M) if w >> (M - 1 - j) & 1) for w in range(2 ** M)), key=lambda x: (len(x), sorted(x)))
    out = []
    for g in range(GROUPS[gate]):
        want = GROUP_MASK[gate][g]
        x = next((x for x in pats if tuple(lower_out(x)[s] if s is not None else False for s in src) == want), None)
        assert x is not None, f"no stimulus for layer {l + 1} gate {gate} sources {src} group {g}"
        out.append(sorted(x))
    return out + [None] * (2 - len(out))


def design(tag, M, net, function=None, delay="3/2"):
    """net: one list per layer of (gate, (source0, source1)) with None for an unused port."""
    layers = []
    for l, row in enumerate(net):
        nodes = []
        for i, (gate, src) in enumerate(row):
            src = list(src) + [None] * (2 - len(src))
            nodes.append(dict(name=f"L{l + 1}.{i}", gate=gate, source=src, delay=[delay if s is not None and l > 0 else "0" for s in src],
                              stimulus=None, initialGain=gains(gate), help=0, threshold=THETA, trainError=BUDGET, testError=BUDGET,
                              dose=D, maxWrites=NEED + 2, rail=RAIL))
        layers.append(nodes)
    for l, nodes in enumerate(layers):
        for n in nodes:
            n["stimulus"] = stimuli(M, layers, l, n["gate"], n["source"])
    return dict(tag=tag, M=M, layers=[dict(timing=LEFT if l == 0 else RIGHT, nodes=nodes) for l, nodes in enumerate(layers)],
                function=function)


class Residual:
    def __init__(self, rule):
        self.rule = rule
        self.rng = random.Random(int(rule.split(":")[1])) if rule.startswith("seeded:") else None

    def __call__(self, b):
        return dict(zero=0, plus=b, minus=-b).get(self.rule) if self.rng is None else self.rng.randint(-b, b)


def score(n, w, x):
    g = lambda a: n["initialGain"][a] + n["dose"] * w[a]
    return n["help"] + (g(0) if x[0] else 0) + (g(1) if x[1] else 0)


def observation(raw, rule="zero"):
    M = raw["M"]
    layers = [lay["nodes"] for lay in raw["layers"]]
    e = Residual(rule)
    slot = 22 if len(layers) <= 2 else 24
    settled = [[[0, 0] for _ in row] for row in layers]

    def cell_read(n, start_hint, incoming, w, budget):
        arr = [None if s is None or incoming[s] is None else incoming[s] + F(n["delay"][a]) for a, s in enumerate(n["source"])]
        got = [t for t in arr if t is not None]
        start = min(got) if got else start_hint
        x = tuple(t is not None for t in arr)
        ee = e(budget)
        v = score(n, w, x) + ee
        fire = v >= n["threshold"]
        em = [(max(got) if got else start) + LAT] if fire else []
        firing = evaluate(n["gate"], x)
        sc = [score(n, w, y) + (ee if firing else 0) for y in MASKS2]
        read = dict(start=s_(start), arrivals=[None if t is None else s_(t) for t in arr], emissions=[s_(t) for t in em], value=v)
        return read, sc, (em[0] if em else None)

    def replay(x, t0, upto):
        """A ReadTrace of layers 1..upto on external pattern x at slot start t0, all cells at their settled writes."""
        incoming = [F(t0) if j in x else None for j in range(M)]
        rt = dict(arrivals=[s_(t) if t is not None else None for t in incoming], layers=[])
        hint = F(t0)
        for l in range(upto):
            row, out = [], []
            for i, n in enumerate(layers[l]):
                read, sc, emitted = cell_read(n, hint, incoming, settled[l][i], n["testError"])
                row.append(dict(read=read, scores=sc))
                out.append(emitted)
            rt["layers"].append(row)
            incoming = out
            hint = hint + 2
        return rt, incoming, hint

    training, t = [], 0
    for l, row in enumerate(layers):
        per_node = []
        for i, n in enumerate(row):
            groups, written = [], [0, 0]
            for g in range(GROUPS[n["gate"]]):
                x = set(n["stimulus"][g])
                rounds = []
                for r in range(n["maxWrites"] + 1):
                    rt, incoming, hint = replay(x, t, l)
                    read, _, _ = cell_read(n, hint, incoming, list(written), n["trainError"])
                    if not read["emissions"]:
                        for a in (0, 1):
                            if read["arrivals"][a] is not None:
                                written[a] += 1
                    rounds.append(dict(replay=rt, read=read))
                    t += slot
                groups.append(rounds)
            settled[l][i] = written
            per_node.append(groups)
        training.append(per_node)
    tests = []
    for w in range(2 ** M):
        x = {j for j in range(M) if w >> (M - 1 - j) & 1}
        rt, _, _ = replay(x, t, len(layers))
        tests.append(rt)
        t += slot
    out = dict(raw, training=training, tests=tests)
    return out
