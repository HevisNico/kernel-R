"""The instance spec of the parameterized kernel-gate generator (GENERATOR_DESIGN.md, 3.1).

A spec is a JSON-shaped dict. `load` reads it into exact values (ints, Fractions) and checks every size against the
Lean sizes of `TraceTables` (research/learned-coincidence/MonotonePremiseTargets.lean): a missing or extra row is
refused, never filled. Dates and delays are exact rationals written as strings (or ints); a float is refused.
"""
from fractions import Fraction as F


class SpecError(ValueError):
    pass


def rat(x, where):
    if isinstance(x, bool) or isinstance(x, float):
        raise SpecError(f"{where}: {x!r} is not an exact rational (a float or a bool)")
    if isinstance(x, int):
        return F(x)
    if isinstance(x, F):
        return x
    if isinstance(x, str):
        try:
            return F(x)
        except (ValueError, ZeroDivisionError) as e:
            raise SpecError(f"{where}: {x!r} is not a rational") from e
    raise SpecError(f"{where}: {x!r} is not a rational")


def nat(x, where):
    if isinstance(x, bool) or not isinstance(x, int) or x < 0:
        raise SpecError(f"{where}: {x!r} is not a natural number")
    return x


def integer(x, where):
    if isinstance(x, bool) or not isinstance(x, int):
        raise SpecError(f"{where}: {x!r} is not an integer")
    return x


def boolean(x, where):
    if not isinstance(x, bool):
        raise SpecError(f"{where}: {x!r} is not a Boolean")
    return x


def sized(xs, n, where):
    if not isinstance(xs, list) or len(xs) != n:
        raise SpecError(f"{where}: expected a list of {n}, got {('a list of ' + str(len(xs))) if isinstance(xs, list) else repr(xs)}")
    return xs


def ports(xs, n, where):
    if not isinstance(xs, list) or any(isinstance(j, bool) or not isinstance(j, int) or not 0 <= j < n for j in xs) or len(set(xs)) != len(xs):
        raise SpecError(f"{where}: {xs!r} is not a set of indices below {n}")
    return sorted(xs)


def lessons(lines, Q2):
    """`lessons p` (MonotoneTarget.lean:112-115): for each round 0..Q2, each output cell i, each selected line a."""
    return [(i, a) for _ in range(Q2 + 1) for i, ls in enumerate(lines) for a in sorted(ls)]


def read(d, width, where):
    if not isinstance(d, dict) or set(d) != {"start", "arrivals", "emissions", "value"}:
        raise SpecError(f"{where}: a read has exactly the keys start, arrivals, emissions, value")
    arr = [None if a is None else rat(a, f"{where}.arrivals[{j}]") for j, a in enumerate(sized(d["arrivals"], width, f"{where}.arrivals"))]
    if not isinstance(d["emissions"], list):
        raise SpecError(f"{where}.emissions: not a list")
    return dict(start=rat(d["start"], f"{where}.start"), arrivals=arr,
                emissions=[rat(e, f"{where}.emissions[{k}]") for k, e in enumerate(d["emissions"])],
                value=integer(d["value"], f"{where}.value"))


def timing(d, where):
    if not isinstance(d, dict) or set(d) != {"skew", "deadline", "duration"}:
        raise SpecError(f"{where}: a timing has exactly skew, deadline, duration")
    return {k: rat(d[k], f"{where}.{k}") for k in ("skew", "deadline", "duration")}


def layer(d, n, width, where, second=False):
    keys = {"cells", "initialGain", "help", "threshold", "dose", "maxWrites", "rail"} | ({"lines", "alwaysFire"} if second else {"terms"})
    if not isinstance(d, dict) or set(d) != keys:
        raise SpecError(f"{where}: expected exactly the keys {sorted(keys)}, got {sorted(d) if isinstance(d, dict) else d!r}")
    out = dict(cells=list(sized(d["cells"], n, f"{where}.cells")),
               initialGain=[[nat(g, f"{where}.initialGain[{i}][{j}]") for j, g in enumerate(sized(row, width, f"{where}.initialGain[{i}]"))]
                            for i, row in enumerate(sized(d["initialGain"], n, f"{where}.initialGain"))],
               help=[nat(v, f"{where}.help[{i}]") for i, v in enumerate(sized(d["help"], n, f"{where}.help"))],
               threshold=[nat(v, f"{where}.threshold[{i}]") for i, v in enumerate(sized(d["threshold"], n, f"{where}.threshold"))],
               dose=nat(d["dose"], f"{where}.dose"), maxWrites=nat(d["maxWrites"], f"{where}.maxWrites"), rail=nat(d["rail"], f"{where}.rail"))
    if second:
        out["lines"] = [ports(ls, width, f"{where}.lines[{i}]") for i, ls in enumerate(sized(d["lines"], n, f"{where}.lines"))]
        out["alwaysFire"] = [boolean(v, f"{where}.alwaysFire[{i}]") for i, v in enumerate(sized(d["alwaysFire"], n, f"{where}.alwaysFire"))]
    else:
        out["terms"] = [ports(t, width, f"{where}.terms[{i}]") for i, t in enumerate(sized(d["terms"], n, f"{where}.terms"))]
    return out


TOP = {"tag", "shape", "inputs", "first", "second", "delay", "heldOut", "timing", "budgets", "observation", "verdicts", "lean"}
OPTIONAL = {"verdicts", "lean", "inputs", "notes"}


def load(d):
    """The spec as exact values; raises SpecError on any size, type or key that does not fit the Lean sizes."""
    if not isinstance(d, dict):
        raise SpecError("a spec is an object")
    extra = set(d) - TOP - OPTIONAL
    missing = TOP - OPTIONAL - set(d)
    if extra or missing:
        raise SpecError(f"spec keys: unknown {sorted(extra)}, missing {sorted(missing)}")
    sh = d["shape"]
    if not isinstance(sh, dict) or set(sh) != {"A", "B", "M"}:
        raise SpecError("shape has exactly A, B, M")
    A, B, M = (nat(sh[k], f"shape.{k}") for k in "ABM")
    tag = d["tag"]
    if not isinstance(tag, str) or not tag or not all(c.isalnum() or c == "_" for c in tag):
        raise SpecError(f"tag {tag!r}: letters, digits and _ only")
    s = dict(tag=tag, A=A, B=B, M=M, inputs=list(d.get("inputs") or [f"x{j}" for j in range(M)]))
    sized(s["inputs"], M, "inputs")
    s["first"] = layer(d["first"], A, M, "first")
    s["second"] = layer(d["second"], B, A, "second", second=True)
    s["delay"] = [[rat(v, f"delay[{i}][{a}]") for a, v in enumerate(sized(row, A, f"delay[{i}]"))] for i, row in enumerate(sized(d["delay"], B, "delay"))]
    if not isinstance(d["heldOut"], list):
        raise SpecError("heldOut: not a list")
    s["heldOut"] = [ports(x, M, f"heldOut[{k}]") for k, x in enumerate(d["heldOut"])]
    tm = d["timing"]
    if not isinstance(tm, dict) or set(tm) != {"left", "right"}:
        raise SpecError("timing has exactly left, right")
    s["timing"] = {k: timing(tm[k], f"timing.{k}") for k in ("left", "right")}
    if not isinstance(d["budgets"], dict) or not d["budgets"]:
        raise SpecError("budgets: a non-empty object of named budgets")
    s["budgets"] = {}
    for name, b in d["budgets"].items():
        if not isinstance(name, str) or not name or not all(c.isalnum() or c == "_" for c in name):
            raise SpecError(f"budget name {name!r}: letters, digits and _ only")
        if not isinstance(b, dict) or set(b) != {"first", "second"}:
            raise SpecError(f"budgets.{name}: exactly first, second")
        s["budgets"][name] = {}
        for lay, n in (("first", A), ("second", B)):
            bb = b[lay]
            if not isinstance(bb, dict) or set(bb) != {"training", "testing"}:
                raise SpecError(f"budgets.{name}.{lay}: exactly training, testing")
            s["budgets"][name][lay] = {k: [nat(v, f"budgets.{name}.{lay}.{k}[{i}]") for i, v in enumerate(sized(bb[k], n, f"budgets.{name}.{lay}.{k}"))]
                                      for k in ("training", "testing")}
    L = lessons(s["second"]["lines"], s["second"]["maxWrites"])
    s["lessons"] = L
    o = d["observation"]
    want = {"firstTrain", "teach", "secondTrain", "firstTest", "secondTest", "scores"}
    if not isinstance(o, dict) or set(o) != want:
        raise SpecError(f"observation: exactly the keys {sorted(want)}")
    Q1 = s["first"]["maxWrites"]
    ob = {}
    ob["firstTrain"] = [[read(c, M, f"firstTrain[{r}][{a}]") for a, c in enumerate(sized(row, A, f"firstTrain[{r}]"))]
                        for r, row in enumerate(sized(o["firstTrain"], Q1 + 1, "firstTrain"))]
    ob["teach"] = [[read(c, M, f"teach[{n}][{a}]") for a, c in enumerate(sized(row, A, f"teach[{n}]"))]
                   for n, row in enumerate(sized(o["teach"], len(L), "teach"))]
    ob["secondTrain"] = [read(c, A, f"secondTrain[{n}]") for n, c in enumerate(sized(o["secondTrain"], len(L), "secondTrain"))]
    ob["firstTest"] = [[read(c, M, f"firstTest[{w}][{a}]") for a, c in enumerate(sized(row, A, f"firstTest[{w}]"))]
                       for w, row in enumerate(sized(o["firstTest"], 2 ** M, "firstTest"))]
    ob["secondTest"] = [[read(c, A, f"secondTest[{w}][{i}]") for i, c in enumerate(sized(row, B, f"secondTest[{w}]"))]
                        for w, row in enumerate(sized(o["secondTest"], 2 ** M, "secondTest"))]
    ob["scores"] = [[[integer(v, f"scores[{w}][{i}][{y}]") for y, v in enumerate(sized(col, 2 ** A, f"scores[{w}][{i}]"))]
                     for i, col in enumerate(sized(row, B, f"scores[{w}]"))]
                    for w, row in enumerate(sized(o["scores"], 2 ** M, "scores"))]
    s["observation"] = ob
    v = d.get("verdicts")
    if v is not None:
        if not isinstance(v, dict) or set(v) != set(s["budgets"]) or not all(isinstance(x, bool) for x in v.values()):
            raise SpecError("verdicts: one Boolean per named budget")
    s["verdicts"] = v
    lean = dict(style="generic", namespace="LearnedCoincidence.MonotoneDNF.PremiseCheck.Generated", source="a spec", derive=True)
    lean.update(d.get("lean") or {})
    if lean["style"] not in ("generic", "gate4"):
        raise SpecError("lean.style is generic or gate4")
    if not lean["namespace"].startswith("LearnedCoincidence.MonotoneDNF.PremiseCheck."):
        raise SpecError("lean.namespace must be under LearnedCoincidence.MonotoneDNF.PremiseCheck")
    s["lean"] = lean
    s["physical"] = physical(s)
    return s


def physical(s):
    """The two-port report (GENERATOR_DESIGN.md 2.1): terms of at most 2 inputs, OR cells of at most 2 lines. A report,
    never a refusal."""
    over = [f"first-layer cell {s['first']['cells'][a]}: {len(t)} inputs" for a, t in enumerate(s["first"]["terms"]) if len(t) > 2]
    over += [f"second-layer cell {s['second']['cells'][i]}: {len(ls)} lines" for i, ls in enumerate(s["second"]["lines"]) if len(ls) > 2]
    return dict(two_port=not over, over=over)


def mask_index(x, n):
    """`maskIndex` (MonotonePremiseTargets.lean:16): port 0 is the most significant bit. x: a set of port indices."""
    return sum(1 << (n - 1 - j) for j in x)


def mask_of(w, n):
    """The set of ports of mask index w."""
    return frozenset(j for j in range(n) if w >> (n - 1 - j) & 1)
