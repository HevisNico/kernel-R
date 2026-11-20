"""Premise-failure mutations of a passing synthetic spec (GENERATOR_DESIGN.md 3.5). Each mutation is a hand change of
the serialized numbers of one read or one parameter, nothing recomputed, as campaign 5's mirror_mutations.py does;
`KIND` gives the mirror condition kinds the mutation is meant to make false, and nothing else.

The reads chosen are found from the spec itself (so the same code serves any shape): "the first firing training read
of cell 0", "the test read of the pattern of line 0 alone", "the test read of the full pattern", "the test read of the
empty pattern", etc. Patterns are index sets; tables are in maskIndex order.
"""
import copy
from fractions import Fraction as F

from spec import mask_index

KIND = {
    "margin1": {"first: positive margin", "first: stops"},
    "margin2": {"second: line testing margin"},
    "rail": {"first: below rail"},
    "residual": {"residual"},
    "window": {"emission window"},
    "single": {"one emission"},
    "vt": {"v <= t"},
    "skew": {"skew"},
    "route": {"route"},
    "separation": {"training rounds"},
    "submask": {"submask"},
    "anchor": {"anchor"},
    "scoreat": {"scoreAt = value"},
    "firebit": {"FIRE bit"},
    "delay": {"delay >= 0"},
}

S = lambda x: str(F(x))


def need1(raw, a=0):
    """The training round at which cell a first fires, from the trace."""
    return next(r for r, row in enumerate(raw["observation"]["firstTrain"]) if row[a]["emissions"])


def mutate(raw, name):
    """A deep copy of raw with mutation `name` (tag suffixed)."""
    m = copy.deepcopy(raw)
    m["tag"] = f"{raw['tag']}m_{name}"
    o, M, A = m["observation"], m["shape"]["M"], m["shape"]["A"]
    K = next(iter(m["budgets"]))
    b = m["budgets"][K]
    t0 = m["first"]["terms"][0]
    line0 = mask_index(t0, M)
    full = mask_index(range(M), M)
    if name == "margin1":           # cell 0's testing error leaves no room at its need (residuals only get easier)
        k = need1(raw)
        # the testing margin is threshold + te <= score(need); te = score(need) - threshold + 1 breaks it
        score = sum(g + m["first"]["dose"] * k for j, g in enumerate(m["first"]["initialGain"][0]) if j in t0) + m["first"]["help"][0]
        b["first"]["testing"][0] = score - m["first"]["threshold"][0] + 1
    elif name == "margin2":         # c's testing error leaves no room for a line alone at its need (DOSE_ADDENDUM 2)
        g = m["second"]
        a = sorted(g["lines"][0])[0]
        k = next(k for k in range(g["maxWrites"] + 1) if g["help"][0] + g["initialGain"][0][a] + g["dose"] * k >= g["threshold"][0])
        b["second"]["testing"][0] = g["help"][0] + g["initialGain"][0][a] + g["dose"] * k - g["threshold"][0] + 1
    elif name == "rail":            # layer 1's rail at cell 0's trained gain on its first port
        k = need1(raw)
        j = sorted(t0)[0]
        m["first"]["rail"] = m["first"]["initialGain"][0][j] + m["first"]["dose"] * k
    elif name == "residual":        # test of the empty pattern, cell 0 (silent): measured score + budget + 1, still silent
        r = o["firstTest"][0][0]
        r["value"] += b["first"]["testing"][0] + 1 - (r["value"] - m["first"]["help"][0])
    elif name == "window":          # cell 0's first firing training read: emission past the deadline
        r = o["firstTrain"][need1(raw)][0]
        r["emissions"] = [S(F(r["start"]) + F(m["timing"]["left"]["deadline"]) + F(1, 10))]
    elif name == "single":          # the same read: its emission doubled
        r = o["firstTrain"][need1(raw)][0]
        r["emissions"] = r["emissions"] * 2
    elif name == "vt":              # c's test read of line 0's pattern: start 1/2 earlier, emission at its arrival - 1/4
        r = o["secondTest"][line0][0]
        arr = [F(a) for a in r["arrivals"] if a is not None]
        r["start"] = S(F(r["start"]) - F(1, 2))
        r["emissions"] = [S(max(arr) - F(1, 4))]
    elif name == "skew":            # test of the pattern {first input of term 0} alone, cell 0: that arrival past the skew
        j = sorted(t0)[0]
        r = o["firstTest"][mask_index([j], M)][0]
        r["arrivals"][j] = S(F(r["start"]) + F(m["timing"]["left"]["skew"]) + F(1, 10))
    elif name == "route":           # secondTrain 0: its arrival + 1/100 (within the skew)
        r = o["secondTrain"][0]
        a = next(a for a, v in enumerate(r["arrivals"]) if v is not None)
        r["arrivals"][a] = S(F(r["arrivals"][a]) + F(1, 100))
    elif name == "separation":      # firstTrain 1, cell 0 (silent): start 1/100 earlier, its arrivals unchanged
        r = o["firstTrain"][1][0]
        r["start"] = S(F(r["start"]) - F(1, 100))
    elif name == "submask":         # c's test read of the full pattern: value and scoreAt(input) = line 0 alone's - 1
        r, sc = o["secondTest"][full][0], o["scores"][full][0]
        one = sc[mask_index([sorted(m["second"]["lines"][0])[0]], A)]
        y = mask_index([a for a, v in enumerate(r["arrivals"]) if v is not None], A)
        r["value"] = one - 1
        sc[y] = one - 1
    elif name == "anchor":          # the same read: scoreAt(line 0 alone) below threshold
        sc = o["scores"][full][0]
        sc[mask_index([sorted(m["second"]["lines"][0])[0]], A)] = m["second"]["threshold"][0] - 1
    elif name == "scoreat":         # the same read: scoreAt(input) + 1, value unchanged
        r, sc = o["secondTest"][full][0], o["scores"][full][0]
        y = mask_index([a for a, v in enumerate(r["arrivals"]) if v is not None], A)
        sc[y] += 1
    elif name == "firebit":         # c's test read of the empty pattern (no arrival, silent): an emission at s + 1/2
        r = o["secondTest"][0][0]
        r["emissions"] = [S(F(r["start"]) + F(1, 2))]
    elif name == "delay":           # every delay -1/100, every routed arrival and second-layer date moved with it
        m["delay"] = [["-1/100"] * A for _ in m["delay"]]
        old = F(raw["delay"][0][0])
        shift = F(-1, 100) - old
        for r in o["secondTrain"] + [row[0] for row in o["secondTest"]]:
            had = any(v is not None for v in r["arrivals"])
            r["arrivals"] = [None if v is None else S(F(v) + shift) for v in r["arrivals"]]
            if had:
                r["start"] = S(F(r["start"]) + shift)
                r["emissions"] = [S(F(e) + shift) for e in r["emissions"]]
    else:
        raise KeyError(name)
    return m
