"""Premise-failure mutations of a passing synthetic layered spec (LAYERED_GENERATOR_DESIGN.md 4(c)). Each is a hand
change of the serialized numbers, nothing recomputed beyond what the change itself moves, as the two-layer
mutate.py does. KIND gives the mirror condition kinds each is meant to make false and nothing else. Where a
mutation cannot be built on a network (no suitable read), `mutate` raises NotApplicable with the reason.

Reads are located from the spec itself: "the top cell's read on the full test", "a silent lower read inside an
upper lesson's replay", etc. Tests are in maskIndex order: index 0 is the empty pattern, index 2^M - 1 the full one.
"""
import copy
from fractions import Fraction as F

import lmirror
import lspec

S = lambda x: str(F(x))

KIND = {
    "early": {"cell: early silence"},
    "stoprange": {"cell: stop in range"},
    "silentmask": {"cell: silent mask"},
    "anchorvalid": {"cell: anchor fires"},
    "rail": {"cell: below rail"},
    "copysource": {"node: source matches gate", "route"},
    "delay": {"node: delay >= 0"},
    "stimulus": {"node: stimulus gives the group mask", "replay input"},
    "oneslot": {"batches in order"},
    "testearly": {"training before tests"},
    "route": {"route"},
    "residual": {"residual"},
    "replayresidual": {"residual"},
    "submask": {"submask"},
    "anchor": {"anchor"},
    "scoreat": {"scoreAt = value"},
    "firebit": {"FIRE bit"},
    "window": {"emission window"},
    "single": {"one emission"},
    "vt": {"v <= t"},
    "skew": {"skew"},
    "timing": {"timing valid"},
}


class NotApplicable(Exception):
    pass


def model(raw):
    s = lspec.load(raw)
    return s, lmirror.Mirror(s)


def top(raw):
    return len(raw["layers"]) - 1


def first_node(raw, gate):
    for l, lay in enumerate(raw["layers"]):
        for i, n in enumerate(lay["nodes"]):
            if n["gate"] == gate:
                return l, i
    raise NotApplicable(f"no {gate} cell")


def shift_read(rd, dt):
    rd["start"] = S(F(rd["start"]) + dt)
    rd["arrivals"] = [None if a is None else S(F(a) + dt) for a in rd["arrivals"]]
    rd["emissions"] = [S(F(e) + dt) for e in rd["emissions"]]


def shift_trace(rt, dt):
    rt["arrivals"] = [None if a is None else S(F(a) + dt) for a in rt["arrivals"]]
    for row in rt["layers"]:
        for c in row:
            shift_read(c["read"], dt)


def mutate(raw, name):
    m = copy.deepcopy(raw)
    m["tag"] = f"{raw['tag']}m_{name}"
    s, mir = model(raw)
    L, M = len(m["layers"]), m["M"]
    full, T = 2 ** M - 1, top(m)
    topread = lambda w: m["tests"][w]["layers"][T][0]
    if name == "early":                      # L1.0's training budget leaves no room below its stop (residuals only get easier)
        n = m["layers"][0]["nodes"][0]
        c = mir.cells[0][0]
        st = c.stop(0)
        n["trainError"] = n["threshold"] - c.group_score(0, st - 1)
        assert n["threshold"] + n["trainError"] <= c.group_score(0, st), "the stop's margin would fail too"
    elif name == "stoprange":                # L1.0's write limit below its stop; its trace keeps the rounds up to the new limit
        n = m["layers"][0]["nodes"][0]
        st = mir.cells[0][0].stop(0)
        n["maxWrites"] = st - 1
        m["training"][0][0] = [rounds[:st] for rounds in m["training"][0][0]]
    elif name == "silentmask":               # a copy cell's unused port 1 given a gain at the threshold: the mask {1} is no longer silent
        l, i = first_node(m, "copy")
        m["layers"][l]["nodes"][i]["initialGain"][1] = m["layers"][l]["nodes"][i]["threshold"]
    elif name == "anchorvalid":              # L1.0's testing budget leaves no room for its anchor (tests only get easier)
        n = m["layers"][0]["nodes"][0]
        c = mir.cells[0][0]
        w = c.expected()
        y = lspec.ANCHORS[c.gate][0]
        n["testError"] = c.score(w, y) - n["threshold"] + 1
        assert all(c.score(w, x) + n["testError"] < n["threshold"] for x in lmirror.MASKS2 if not lspec.evaluate(c.gate, x)), "a silent mask would fail too"
    elif name == "rail":                     # L1.0's rail at its trained gain on port 0
        n = m["layers"][0]["nodes"][0]
        c = mir.cells[0][0]
        n["rail"] = c.gain(c.expected(), 0)
    elif name == "copysource":               # a copy cell's port 1 given a source (its reads keep no arrival on port 1)
        l, i = first_node(m, "copy")
        m["layers"][l]["nodes"][i]["source"][1] = 0
    elif name == "delay":                    # the top cell's delays set to -1/100, every arrival, start and emission of its reads moved with it
        n = m["layers"][T]["nodes"][0]
        if T == 0:
            raise NotApplicable("the top cell reads external inputs")
        dt = F(-1, 100) - F(n["delay"][0])
        assert n["delay"][0] == n["delay"][1]
        n["delay"] = ["-1/100", "-1/100"]
        reads = [x["read"] for g in m["training"][T][0] for x in g] + [rt["layers"][T][0]["read"] for rt in m["tests"]]
        for rd in reads:
            if any(a is not None for a in rd["arrivals"]):
                shift_read(rd, dt)
    elif name == "stimulus":                 # the top cell's group-0 stimulus replaced by the empty pattern (the trace keeps its lessons)
        m["layers"][T]["nodes"][0]["stimulus"][0] = []
    elif name == "oneslot":                  # campaign 6's schedule: L1.1's rounds moved into L1.0's slots
        if len(m["layers"][0]["nodes"]) < 2:
            raise NotApplicable("one layer-1 cell")
        a0 = F(m["training"][0][0][0][0]["read"]["start"])
        a1 = F(m["training"][0][1][0][0]["read"]["start"])
        for g in m["training"][0][1]:
            for x in g:
                shift_trace(x["replay"], a0 - a1)
                shift_read(x["read"], a0 - a1)
    elif name == "testearly":                # the empty-pattern test moved to the start of training
        t0 = F(m["tests"][0]["layers"][0][0]["read"]["start"])
        shift_trace(m["tests"][0], -t0)
    elif name == "route":                    # the top cell's read on the full test: one arrival + 1/100 (within the skew)
        rd = topread(full)["read"]
        a = next(k for k, v in enumerate(rd["arrivals"]) if v is not None)
        rd["arrivals"][a] = S(F(rd["arrivals"][a]) + F(1, 100))
        if T == 0:
            raise NotApplicable("the top cell reads external inputs")
    elif name == "residual":                 # L1.0's first lesson (silent): measured score at its model + training budget + 1
        x = m["training"][0][0][0][0]
        c = mir.cells[0][0]
        rd = x["read"]
        mod = c.score([0, 0], tuple(v is not None for v in rd["arrivals"]))
        rd["value"] = mod + m["layers"][0]["nodes"][0]["trainError"] + 1
        assert rd["value"] < m["layers"][0]["nodes"][0]["threshold"] and not rd["emissions"]
    elif name == "replayresidual":           # a silent lower read inside an upper lesson's replay: model + testing budget + 1, still silent
        for l in range(1, L):
            for i, groups in enumerate(m["training"][l]):
                for g, rounds in enumerate(groups):
                    for x in rounds:
                        for k, row in enumerate(x["replay"]["layers"]):
                            for j, cell in enumerate(row):
                                rd = cell["read"]
                                c = mir.cells[k][j]
                                inp = tuple(v is not None for v in rd["arrivals"])
                                if lspec.evaluate(c.gate, inp) or rd["emissions"]:
                                    continue
                                w = c.settled(s["training"][k][j])
                                v = c.score(w, inp) + c.n["testError"] + 1
                                if v < c.n["threshold"]:
                                    rd["value"] = v
                                    return m
        raise NotApplicable("no silent lower read inside an upper lesson's replay")
    elif name in ("submask", "anchor", "scoreat", "window", "single", "vt"):
        cell = topread(full)
        rd, sc = cell["read"], cell["scores"]
        c = mir.cells[T][0]
        inp = tuple(v is not None for v in rd["arrivals"])
        y_in = lmirror.mask_index2(inp)
        assert rd["emissions"], "the top cell fires on the full test"
        if name == "submask":                # a proper firing submask above the observed mask
            subs = [y for y in lmirror.MASKS2 if y != inp and lmirror.contains(inp, y) and sc[lmirror.mask_index2(y)] >= c.n["threshold"]]
            if not subs:
                raise NotApplicable(f"the top cell ({c.gate}) has no proper firing submask on the full test")
            v = sc[lmirror.mask_index2(subs[0])] - 1
            rd["value"], sc[y_in] = v, v
        elif name == "anchor":               # an anchor's reference score below its lower bound
            y = next(y for y in lspec.ANCHORS[c.gate] if lmirror.contains(inp, y))
            w = c.settled(s["training"][T][0])
            low = c.score(w, y) - c.n["testError"] - 1
            if y == inp:                     # the anchor is the observed mask itself: move the measured score with it (still firing)
                rd["value"] = low
                assert low >= c.n["threshold"]
            else:
                low = min(low, c.n["threshold"] - 1)
            sc[lmirror.mask_index2(y)] = low
        elif name == "scoreat":
            sc[y_in] += 1
        elif name == "window":
            rd["emissions"] = [S(F(rd["start"]) + F(m["layers"][T]["timing"]["deadline"]) + F(1, 10))]
        elif name == "single":
            rd["emissions"] = rd["emissions"] * 2
        elif name == "vt":                   # start 1/2 earlier, emission 1/4 before the last arrival
            last = max(F(a) for a in rd["arrivals"] if a is not None)
            rd["start"] = S(F(rd["start"]) - F(1, 2))
            rd["emissions"] = [S(last - F(1, 4))]
            if not all(a is None or F(rd["start"]) <= F(a) <= F(rd["start"]) + F(m["layers"][T]["timing"]["skew"]) for a in rd["arrivals"]):
                raise NotApplicable("the arrivals would leave the skew")
    elif name == "firebit":                  # the top cell's read on the empty test (silent): an emission at start + 1/2
        rd = topread(0)["read"]
        assert not rd["emissions"]
        rd["emissions"] = [S(F(rd["start"]) + F(1, 2))]
    elif name == "skew":                     # a layer-1 read in the last test: its start 0.12 earlier, so its arrivals leave the skew
        rd = m["tests"][full]["layers"][0][0]["read"]
        rd["start"] = S(F(rd["start"]) - F(m["layers"][0]["timing"]["skew"]) - F(1, 10))
    elif name == "timing":                   # the top layer's deadline set to its duration
        m["layers"][T]["timing"]["deadline"] = m["layers"][T]["timing"]["duration"]
    else:
        raise KeyError(name)
    return m
