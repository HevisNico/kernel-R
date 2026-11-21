"""The instance spec of the layered kernel-gate generator (LAYERED_GENERATOR_DESIGN.md, section 4).

`load(d)` reads a JSON-shaped spec into exact values and checks every size against the Lean types of
research/learned-coincidence/LayeredMonotoneTarget.lean:

- a node's sources point into the layer just below (an index below its width), or are null;
- each active group has a stimulus and exactly maxWrites + 1 training rounds;
- each replay is a ReadTrace of exactly the layers below;
- there are 2^M tests, each a ReadTrace of the whole network.

A missing, extra or ragged row is refused, never filled. A value given for an inactive group is refused. Gate
semantics (groups, ports used) follow LayeredMonotoneTarget.lean:13-48.
"""
from fractions import Fraction as F
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from spec import SpecError, boolean, integer, nat, rat, sized  # noqa: E402,F401

GATES = ("off", "on", "copy", "both", "either")
GROUPS = dict(off=0, on=0, copy=1, both=1, either=2)                     # Gate.groups, T:31-34
USES = dict(off=(False, False), on=(False, False), copy=(True, False), both=(True, True), either=(True, True))  # T:26-29
GROUP_MASK = dict(copy=[(True, False)], both=[(True, True)], either=[(True, False), (False, True)])           # T:36-40
ANCHORS = dict(off=[], on=[(False, False)], copy=[(True, False)], both=[(True, True)],
               either=[(True, False), (False, True)])                                                    # T:43-48


def evaluate(gate, x):
    """Gate.eval (T:17-22) on a two-port mask x = (port 0, port 1)."""
    return dict(off=False, on=True, copy=x[0], both=x[0] and x[1], either=x[0] or x[1])[gate]


def read(d, width, where):
    if not isinstance(d, dict) or set(d) != {"start", "arrivals", "emissions", "value"}:
        raise SpecError(f"{where}: a read has exactly the keys start, arrivals, emissions, value")
    arr = [None if a is None else rat(a, f"{where}.arrivals[{j}]") for j, a in enumerate(sized(d["arrivals"], width, f"{where}.arrivals"))]
    if not isinstance(d["emissions"], list):
        raise SpecError(f"{where}.emissions: not a list")
    return dict(start=rat(d["start"], f"{where}.start"), arrivals=arr,
                emissions=[rat(e, f"{where}.emissions[{k}]") for k, e in enumerate(d["emissions"])],
                value=integer(d["value"], f"{where}.value"))


def read_trace(d, M, widths, where):
    """A ReadTrace of the layers of `widths` (bottom first): external arrivals, then per layer per cell a read and its
    four reference scores (maskIndex order over Pattern 2: index 0 = no port, 1 = port 1, 2 = port 0, 3 = both)."""
    if not isinstance(d, dict) or set(d) != {"arrivals", "layers"}:
        raise SpecError(f"{where}: a ReadTrace has exactly the keys arrivals, layers")
    arr = [None if a is None else rat(a, f"{where}.arrivals[{j}]") for j, a in enumerate(sized(d["arrivals"], M, f"{where}.arrivals"))]
    layers = []
    for l, (row, w) in enumerate(zip(sized(d["layers"], len(widths), f"{where}.layers"), widths)):
        cells = []
        for i, c in enumerate(sized(row, w, f"{where}.layers[{l}]")):
            if not isinstance(c, dict) or set(c) != {"read", "scores"}:
                raise SpecError(f"{where}.layers[{l}][{i}]: exactly read, scores")
            cells.append(dict(read=read(c["read"], 2, f"{where}.layers[{l}][{i}].read"),
                              scores=[integer(v, f"{where}.layers[{l}][{i}].scores[{y}]") for y, v in enumerate(sized(c["scores"], 4, f"{where}.layers[{l}][{i}].scores"))]))
        layers.append(cells)
    return dict(arrivals=arr, layers=layers)


CELL_KEYS = ("initialGain", "help", "threshold", "trainError", "testError", "dose", "maxWrites", "rail")


def node(d, M, below, where):
    keys = {"name", "gate", "source", "delay", "stimulus"} | set(CELL_KEYS)
    if not isinstance(d, dict) or set(d) != keys:
        raise SpecError(f"{where}: expected exactly the keys {sorted(keys)}, got {sorted(d) if isinstance(d, dict) else d!r}")
    if d["gate"] not in GATES:
        raise SpecError(f"{where}.gate: {d['gate']!r} is not one of {GATES}")
    n = dict(name=str(d["name"]), gate=d["gate"],
             initialGain=[nat(g, f"{where}.initialGain[{a}]") for a, g in enumerate(sized(d["initialGain"], 2, f"{where}.initialGain"))])
    for k in CELL_KEYS[1:]:
        n[k] = nat(d[k], f"{where}.{k}")
    src = []
    for a, s in enumerate(sized(d["source"], 2, f"{where}.source")):
        if s is None:
            src.append(None)
        elif isinstance(s, bool) or not isinstance(s, int) or not 0 <= s < below:
            raise SpecError(f"{where}.source[{a}]: {s!r} is not a cell index below {below} (the width of the layer below)")
        else:
            src.append(s)
    n["source"] = src
    n["delay"] = [rat(v, f"{where}.delay[{a}]") for a, v in enumerate(sized(d["delay"], 2, f"{where}.delay"))]
    stim = []
    for g, x in enumerate(sized(d["stimulus"], 2, f"{where}.stimulus")):
        active = g < GROUPS[n["gate"]]
        if x is None:
            if active:
                raise SpecError(f"{where}.stimulus[{g}]: an active group needs a stimulus")
            stim.append(frozenset())
            continue
        if not active:
            raise SpecError(f"{where}.stimulus[{g}]: group {g} is not active for gate {n['gate']}; give null")
        if not isinstance(x, list) or any(isinstance(j, bool) or not isinstance(j, int) or not 0 <= j < M for j in x):
            raise SpecError(f"{where}.stimulus[{g}]: {x!r} is not a set of input indices")
        stim.append(frozenset(x))
    n["stimulus"] = stim
    return n


def load(d):
    if not isinstance(d, dict):
        raise SpecError("a spec is an object")
    allowed = {"tag", "M", "inputs", "layers", "training", "tests", "verdicts", "lean", "notes", "function"}
    if set(d) - allowed or {"tag", "M", "layers", "training", "tests"} - set(d):
        raise SpecError(f"spec keys: unknown {sorted(set(d) - allowed)}, missing {sorted({'tag', 'M', 'layers', 'training', 'tests'} - set(d))}")
    tag = d["tag"]
    if not isinstance(tag, str) or not tag or not all(c.isalnum() or c == "_" for c in tag):
        raise SpecError(f"tag {tag!r}: letters, digits and _ only")
    M = nat(d["M"], "M")
    s = dict(tag=tag, M=M, inputs=list(d.get("inputs") or [chr(ord("A") + j) for j in range(M)]))
    sized(s["inputs"], M, "inputs")
    if not isinstance(d["layers"], list) or not d["layers"]:
        raise SpecError("layers: a non-empty list")
    layers, widths, below = [], [], M
    for l, lay in enumerate(d["layers"]):
        if not isinstance(lay, dict) or set(lay) != {"timing", "nodes"}:
            raise SpecError(f"layers[{l}]: exactly timing, nodes")
        tm = lay["timing"]
        if not isinstance(tm, dict) or set(tm) != {"skew", "deadline", "duration"}:
            raise SpecError(f"layers[{l}].timing: exactly skew, deadline, duration")
        timing = {k: rat(tm[k], f"layers[{l}].timing.{k}") for k in ("skew", "deadline", "duration")}
        if not isinstance(lay["nodes"], list) or not lay["nodes"]:
            raise SpecError(f"layers[{l}].nodes: a non-empty list")
        nodes = [node(nd, M, below, f"layers[{l}].nodes[{i}]") for i, nd in enumerate(lay["nodes"])]
        layers.append(dict(timing=timing, nodes=nodes))
        widths.append(len(nodes))
        below = len(nodes)
    s["layers"], s["widths"] = layers, widths
    tr = sized(d["training"], len(layers), "training")
    s["training"] = []
    for l, lay in enumerate(layers):
        per_node = []
        for i, nd in enumerate(sized(tr[l], widths[l], f"training[{l}]")):
            n = lay["nodes"][i]
            gs = sized(nd, GROUPS[n["gate"]], f"training[{l}][{i}] (one list per active group)")
            groups = []
            for g, rounds in enumerate(gs):
                rr = []
                for r, x in enumerate(sized(rounds, n["maxWrites"] + 1, f"training[{l}][{i}][{g}] (maxWrites + 1 rounds)")):
                    w = f"training[{l}][{i}][{g}][{r}]"
                    if not isinstance(x, dict) or set(x) != {"replay", "read"}:
                        raise SpecError(f"{w}: exactly replay, read")
                    rr.append(dict(replay=read_trace(x["replay"], M, widths[:l], f"{w}.replay"), read=read(x["read"], 2, f"{w}.read")))
                groups.append(rr)
            per_node.append(groups)
        s["training"].append(per_node)
    s["tests"] = [read_trace(t, M, widths, f"tests[{w}]") for w, t in enumerate(sized(d["tests"], 2 ** M, "tests"))]
    v = d.get("verdicts")
    if v is not None and (not isinstance(v, dict) or not all(isinstance(x, bool) for x in v.values())):
        raise SpecError("verdicts: Booleans")
    s["verdicts"] = v
    lean = dict(namespace="LearnedCoincidence.Layered.Generated", source="a layered spec", derive=True)
    lean.update(d.get("lean") or {})
    if not lean["namespace"].startswith("LearnedCoincidence.Layered."):
        raise SpecError("lean.namespace must be under LearnedCoincidence.Layered")
    s["lean"] = lean
    s["function"] = d.get("function")         # a Lean Bool expression in x, stated independently; optional
    s["physical"] = physical(s)
    return s


def physical(s):
    """A report, never a refusal: how many cell ports each external input and each cell output drives."""
    ext = [0] * s["M"]
    for n in s["layers"][0]["nodes"]:
        for j in n["source"]:
            if j is not None:
                ext[j] += 1
    inner = []
    for l in range(1, len(s["layers"])):
        cnt = [0] * s["widths"][l - 1]
        for n in s["layers"][l]["nodes"]:
            for j in n["source"]:
                if j is not None:
                    cnt[j] += 1
        inner.append(cnt)
    return dict(ports_per_input=ext, ports_per_cell_output=inner,
                copies=sum(n["gate"] == "copy" for lay in s["layers"] for n in lay["nodes"]))
