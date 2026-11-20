"""Synthetic observations from the additive model (GENERATOR_DESIGN.md 3.4). No circuit and no simulation: every
score is the guarded additive score of the Lean model plus a residual e chosen by a rule, every date comes from a
fixed calendar.

`design(...)` chooses parameters for any terms and wiring, in the integer units of the campaigns (THETA = 100 000):
each first-layer cell of a term of c inputs has initial gain THETA / c - d1 (n1 - 1/2) on its ports, so that its
need is n1; each selected line of an output cell has initial gain THETA - d2 (n2 - 1/2), so that its need is n2.
`observation(raw, rule)` fills the trace tables of a raw spec in the order of `TraceTables`.

Calendar (the one of C5/predicted.py:355-444, generalized): slots S = 22 apart; first-layer rounds r = 0..Q1 at S r;
lessons in Lean `lessons` order; tests in maskIndex order. Every external input of a slot arrives at its start; a
first-layer FIRE emits at start + LAT1; a routed pulse arrives at emission + delay; a second-layer read starts at its
first arrival (or at slot start + 2 when nothing arrives) and a FIRE emits at its last arrival + LAT2.

Residual rules: "zero"; "plus" (+budget); "minus" (-budget); "seeded:N" (an integer uniform in [-budget, budget]
from random.Random(N), one draw per read in table order). The budget of a read is the one the checker uses for it
(training budget in training, testing budget otherwise), from the spec's first named budget. On a firing read of the
second layer the same e is added to every entry of its reference scores, so submask order and anchors hold.
"""
from fractions import Fraction as F
import random

from spec import lessons as lesson_list, mask_index, mask_of

THETA = 100000
RAIL = 10 * THETA
SLOT = 22
LAT1, LAT2 = F(1, 2), F(1, 2)
TIMING = dict(left=dict(skew="1/50", deadline="11/10", duration="22"), right=dict(skew="11/10", deadline="11/5", duration="19"))


def s_(x):
    return str(F(x))


def design(tag, M, terms, lines, always=None, n1=3, n2=3, d1=10000, d2=10000, budget=2000, delay="3/2",
           Q1=None, Q2=None, help2=None, inputs=None, extra_budgets=None):
    """A raw spec without observation. terms: one input set per first-layer cell; lines: one line set per output cell;
    always: alwaysFire per output cell (a constant cell has no line and help THETA + 2 budget)."""
    A, B = len(terms), len(lines)
    always = always or [False] * B
    ig1 = []
    for t in terms:
        g = F(THETA, len(t)) - d1 * (n1 - F(1, 2))
        assert g >= 0 and g.denominator == 1, f"choose d1, n1 so that THETA/{len(t)} - d1 (n1 - 1/2) is a natural: {g}"
        ig1.append([int(g) if j in t else 0 for j in range(M)])
    g2 = THETA - d2 * (n2 - F(1, 2))
    assert g2 >= 0 and g2.denominator == 1
    ig2 = [[int(g2) if a in lines[i] else 0 for a in range(A)] for i in range(B)]
    h2 = help2 or [THETA + 2 * budget if always[i] else 0 for i in range(B)]
    budgets = {"K0": dict(first=dict(training=[budget] * A, testing=[budget] * A), second=dict(training=[budget] * B, testing=[budget] * B))}
    budgets.update(extra_budgets or {})
    return dict(
        tag=tag, shape=dict(A=A, B=B, M=M), inputs=inputs or [chr(ord("A") + j) for j in range(M)],
        first=dict(cells=[f"a{k}" for k in range(A)], terms=[sorted(t) for t in terms], initialGain=ig1, help=[0] * A,
                   threshold=[THETA] * A, dose=d1, maxWrites=Q1 if Q1 is not None else n1 + 2, rail=RAIL),
        second=dict(cells=[f"c{k}" for k in range(B)], lines=[sorted(ls) for ls in lines], alwaysFire=list(always),
                    initialGain=ig2, help=h2, threshold=[THETA] * B, dose=d2, maxWrites=Q2 if Q2 is not None else n2 + 2, rail=RAIL),
        delay=[[delay] * A for _ in range(B)], heldOut=[], timing=TIMING, budgets=budgets)


class Residual:
    def __init__(self, rule):
        self.rule = rule
        self.rng = random.Random(int(rule.split(":")[1])) if rule.startswith("seeded:") else None

    def __call__(self, budget):
        if self.rule == "zero":
            return 0
        if self.rule == "plus":
            return budget
        if self.rule == "minus":
            return -budget
        if self.rng is not None:
            return self.rng.randint(-budget, budget)
        raise ValueError(self.rule)


def observation(raw, rule="zero"):
    """raw: a design() dict. Returns raw with its observation, built from the additive model."""
    A, B, M = raw["shape"]["A"], raw["shape"]["B"], raw["shape"]["M"]
    f, g = raw["first"], raw["second"]
    K = next(iter(raw["budgets"]))
    bud = raw["budgets"][K]
    terms = [frozenset(t) for t in f["terms"]]
    lines = [frozenset(ls) for ls in g["lines"]]
    Q1, Q2 = f["maxWrites"], g["maxWrites"]
    delay = [[F(v) for v in row] for row in raw["delay"]]
    e = Residual(rule)

    def score1(a, k, x):
        return f["help"][a] + sum(f["initialGain"][a][j] + f["dose"] * (k if j in terms[a] else 0) for j in range(M) if j in x)

    def view(i, w, x):
        return g["help"][i] + sum(g["initialGain"][i][a] + g["dose"] * w[i][a] for a in range(A) if a in x)

    def first_read(start, x, a, k, budget):
        v = score1(a, k, x) + e(budget)
        fire = v >= f["threshold"][a]
        return dict(start=s_(start), arrivals=[s_(start) if j in x else None for j in range(M)],
                    emissions=[s_(start + LAT1)] if fire else [], value=v)

    def second_read(slot, ups, i, w, budget):
        """ups: the first-layer reads of the slot (Fin A); returns (read, its e)."""
        arr = [None if not u["emissions"] else F(u["emissions"][0]) + delay[i][a] for a, u in enumerate(ups)]
        got = [t for t in arr if t is not None]
        start = min(got) if got else F(slot) + 2
        x = frozenset(a for a in range(A) if arr[a] is not None)
        ee = e(budget)
        v = view(i, w, x) + ee
        fire = v >= g["threshold"][i]
        em = [s_((max(got) if got else start) + LAT2)] if fire else []
        return dict(start=s_(start), arrivals=[None if t is None else s_(t) for t in arr], emissions=em, value=v), ee, x

    ob = dict(firstTrain=[], teach=[], secondTrain=[], firstTest=[], secondTest=[], scores=[])
    counts = [0] * A
    for r in range(Q1 + 1):
        row = []
        for a in range(A):
            rd = first_read(SLOT * r, terms[a], a, counts[a], bud["first"]["training"][a])
            row.append(rd)
        for a in range(A):
            if not row[a]["emissions"]:
                counts[a] += 1
        ob["firstTrain"].append(row)
    settled = counts
    L = lesson_list(g["lines"], Q2)
    w = [[0] * A for _ in range(B)]
    t0 = SLOT * (Q1 + 1)
    for n, (i, line) in enumerate(L):
        slot = t0 + SLOT * n
        row = [first_read(slot, terms[line], a, settled[a], bud["first"]["testing"][a]) for a in range(A)]
        ob["teach"].append(row)
        rd, _, x = second_read(slot, row, i, w, bud["second"]["training"][i])
        ob["secondTrain"].append(rd)
        if not rd["emissions"]:
            for a in x:
                w[i][a] += 1
    t1 = t0 + SLOT * len(L)
    for wi in range(2 ** M):
        x = mask_of(wi, M)
        slot = t1 + SLOT * wi
        row = [first_read(slot, x, a, settled[a], bud["first"]["testing"][a]) for a in range(A)]
        ob["firstTest"].append(row)
        srow, scrow = [], []
        for i in range(B):
            rd, ee, xin = second_read(slot, row, i, w, bud["second"]["testing"][i])
            srow.append(rd)
            firing = g["alwaysFire"][i] or any(a in lines[i] and a in xin for a in range(A))
            scrow.append([view(i, w, mask_of(y, A)) + (ee if firing else 0) for y in range(2 ** A)])
        ob["secondTest"].append(srow)
        ob["scores"].append(scrow)
    out = dict(raw, observation=ob)
    out["tag"] = raw["tag"]
    return out


def output_index(x, M):
    return mask_index(x, M)
