"""The network spec: structure only, checked against the Lean types of LayeredMonotoneTarget.lean.

Accepted forms (JSON):
- this package's form: tag, inputs, front (inverter front end), expect (outputs in pattern-code order), layers[{nodes}];
- a generator lspec (research/learned-dnf-generator/layered/lspec.py): its tag, M and layers[{timing, nodes}] are read
  for the structure; its timing, cell parameters, training and tests are ignored (they come from this run).

A node: gate (off | on | copy | both | either), source [port 0, port 1] (an index in the layer below, or null), and
stimulus [group 0, group 1] (a set of line indices of the cascade, or null for an inactive group).

With `front`, the cascade reads 2 m lines (line j = input j, line m + j = its complement, as `rails` in
TwoRailsTarget.lean) and every stimulus must be the rails of an input pattern.
The pattern code of an input pattern x is sum over j of x_j 2^j: the order of `patterns` in MonotonePremiseTargets.lean.
"""
from fractions import Fraction as F
import json
from pathlib import Path

GATES = ("off", "on", "copy", "both", "either")
GROUPS = dict(off=0, on=0, copy=1, both=1, either=2)
USES = dict(off=(False, False), on=(False, False), copy=(True, False), both=(True, True), either=(True, True))
GROUP_MASK = dict(copy=[(True, False)], both=[(True, True)], either=[(True, False), (False, True)])


class SpecError(ValueError):
    pass


def evaluate(gate, x):
    return dict(off=False, on=True, copy=x[0], both=x[0] and x[1], either=x[0] or x[1])[gate]


def patterns(m):
    """Input patterns in code order; pattern k has x_j = bit j of k."""
    return [tuple(bool(k >> j & 1) for j in range(m)) for k in range(2 ** m)]


def code(x):
    return sum(1 << j for j, b in enumerate(x) if b)


def load(path):
    d = json.loads(Path(path).read_text())
    if "training" in d:                                  # a generator lspec: structure only
        m = d["M"]
        d = dict(tag=d["tag"], inputs=d.get("inputs") or [f"x{j}" for j in range(m)], front=d.get("front", False),
                 expect=d.get("expect"), layers=[dict(nodes=l["nodes"]) for l in d["layers"]])
    tag = d["tag"]
    if not tag or not all(c.isalnum() or c == "_" for c in tag) or not tag[0].isalpha():
        raise SpecError(f"tag {tag!r}")
    m = len(d["inputs"])
    front = bool(d.get("front", False))
    lines = 2 * m if front else m
    layers, below = [], lines
    for l, lay in enumerate(d["layers"]):
        nodes = []
        for i, n in enumerate(lay["nodes"]):
            w = f"layers[{l}].nodes[{i}]"
            g = n["gate"]
            if g not in GATES:
                raise SpecError(f"{w}: gate {g!r}")
            src = list(n["source"])
            if len(src) != 2:
                raise SpecError(f"{w}: two ports")
            for a in range(2):
                if (src[a] is not None) != USES[g][a]:
                    raise SpecError(f"{w}: port {a} source {src[a]!r} against gate {g}")
                if src[a] is not None and not (isinstance(src[a], int) and 0 <= src[a] < below):
                    raise SpecError(f"{w}: source {src[a]!r} not below {below}")
            stim = list(n["stimulus"])
            if len(stim) != 2:
                raise SpecError(f"{w}: two stimulus groups")
            for g_ in range(2):
                if (stim[g_] is not None) != (g_ < GROUPS[g]):
                    raise SpecError(f"{w}: stimulus of group {g_}")
            stim = [None if s is None else frozenset(s) for s in stim]
            nodes.append(dict(name=n.get("name", f"c{l + 1}_{i}"), gate=g, source=src, stimulus=stim))
        layers.append(nodes)
        below = len(nodes)
    s = dict(tag=tag, inputs=list(d["inputs"]), m=m, front=front, lines=lines, layers=layers, function=d.get("function", ""))
    for l, nodes in enumerate(layers):                   # Node.Valid's stimulus clause
        for i, n in enumerate(nodes):
            for g_ in range(GROUPS[n["gate"]]):
                x = line_pattern(s, n["stimulus"][g_])
                below = predict_layers(s, x)[l - 1] if l else x
                got = tuple(False if n["source"][a] is None else below[n["source"][a]] for a in range(2))
                if got != GROUP_MASK[n["gate"]][g_]:
                    raise SpecError(f"{n['name']}: stimulus {sorted(n['stimulus'][g_])} gives inputs {got}, not the group mask")
    exp = d.get("expect")
    if exp is None:
        raise SpecError("expect: the expected outputs, one per input pattern")
    if len(exp) != 2 ** m or len(layers[-1]) != 1:
        raise SpecError("expect: 2^m outputs of a last layer of width 1")
    s["expect"] = [bool(v) for v in exp]
    for x in patterns(m):
        if predict(s, rails(s, x))[0] != s["expect"][code(x)]:
            raise SpecError(f"the cascade does not compute expect at {x}")
    return s


def rails(s, x):
    """The line pattern of an input pattern."""
    return tuple(x) + tuple(not b for b in x) if s["front"] else tuple(x)


def line_pattern(s, lineset):
    """A stimulus line set as a line pattern; with a front end it must be the rails of an input pattern."""
    x = tuple(j in lineset for j in range(s["lines"]))
    if s["front"] and rails(s, x[:s["m"]]) != x:
        raise SpecError(f"stimulus {sorted(lineset)} is not the rails of an input pattern")
    return x


def input_of_lines(s, x):
    return tuple(x[:s["m"]])


def predict_layers(s, x):
    """The predicted pattern of each layer (list, layer 1 first) on line pattern x."""
    out, below = [], x
    for nodes in s["layers"]:
        below = tuple(evaluate(n["gate"], tuple(False if n["source"][a] is None else below[n["source"][a]] for a in range(2)))
                      for n in nodes)
        out.append(below)
    return out


def predict(s, x):
    return predict_layers(s, x)[-1]


def timing(s, cfg):
    """Design constants per layer (exact fractions, tu): offsets of the read starts from the slot base T, skew,
    deadline, duration; the external window w, the wire delay and the inverter timing."""
    t = cfg["timing"]
    q = lambda v: F(str(v))
    delta, dmax = q(t["delta"]), q(t["dmax_design"])
    if s["front"]:
        e, l, win = q(t["emit_early"]), q(t["emit_late"]), q(t["inverter_window"])
        w = max(win, l - e)
        off0 = e
    else:
        e = l = win = None
        w = q(t["external_w"])
        off0 = F(0)
    offset, skew, deadline, duration = {0: off0}, {}, {}, {}
    for k in range(1, len(s["layers"]) + 1):
        offset[k] = offset[k - 1] + delta
        skew[k] = w if k == 1 else skew[k - 1] + dmax
        deadline[k] = skew[k] + dmax
        duration[k] = deadline[k] + 1
    return dict(delta=delta, dmax_design=dmax, w=w, offset=offset, skew=skew, deadline=deadline, duration=duration,
                emit_early=e, emit_late=l, inverter_window=win)
