"""A generic Python mirror of the three kernel checkers (GENERATOR_DESIGN.md 3.3), for any Cascade A B M.

A direct transliteration, in exact ints and Fractions, of
  checkCascadeValid               (MonotonePremiseTargets.lean:114 -> Cascade.check, MonotoneTarget.lean:91-95)
  checkTrainingSeparation         (MonotonePremiseTargets.lean:116-140)
  checkCascadeCalibrationOneSided (MonotonePremiseTargets.lean:142-170)
with every sub-function they use (Target.lean, MonotoneTarget.lean, TwoLayerTarget.lean). It works on a loaded spec
(spec.load) and one named budget. It records every elementary condition as (checker, kind, where, ok) so a failure
can be located; the per-checker verdict is the conjunction of that checker's conditions, as the Lean `&&` and `all`
are conjunctions (evaluation order does not change a Boolean conjunction's value).

Nothing here is used to decide anything by itself: the Lean file asserts the verdict and the kernel checks it.
"""
from fractions import Fraction as F

from spec import lessons as lesson_list, mask_index, mask_of

VALID, SEP, CAL = "checkCascadeValid", "checkTrainingSeparation", "checkCascadeCalibrationOneSided"
CHECKERS = (VALID, SEP, CAL)


def contains(read, target):
    """`contains read target`: every port of target is in read."""
    return set(target) <= set(read)


def robust_fire(level, budget, value):
    return level + budget <= value


def robust_silence(level, budget, value):
    return value + budget < level


class Layer1:
    """`Parameters A M` with one budget's errors (Target.lean:23-33)."""

    def __init__(self, s, K):
        f = s["first"]
        self.N, self.M = s["A"], s["M"]
        self.target = [frozenset(t) for t in f["terms"]]
        self.g0 = f["initialGain"]
        self.help, self.th = f["help"], f["threshold"]
        self.tr, self.te = s["budgets"][K]["first"]["training"], s["budgets"][K]["first"]["testing"]
        self.dose, self.Q, self.rail = f["dose"], f["maxWrites"], f["rail"]

    def gain(self, i, k, j):
        return self.g0[i][j] + self.dose * (k if j in self.target[i] else 0)

    def score(self, i, k, x):
        return self.help[i] + sum(self.gain(i, k, j) for j in range(self.M) if j in x)

    def need(self, i):
        return next((k for k in range(self.Q + 1) if self.th[i] <= self.score(i, k, self.target[i])), self.Q + 1)


class View:
    """`readView p writes` (MonotoneTarget.lean:42-52), scored at index 0: help + sum of lineGain at the writes."""

    def __init__(self, L2, writes):
        self.L2, self.w = L2, writes

    def score(self, i, x):
        return self.L2.help[i] + sum(self.L2.line_gain(i, a, self.w[i][a]) for a in range(self.L2.A) if a in x)


class Layer2:
    """`Disjunctions B A` with one budget's errors (MonotoneTarget.lean:10-20)."""

    def __init__(self, s, K):
        g = s["second"]
        self.B, self.A = s["B"], s["A"]
        self.lines = [frozenset(ls) for ls in g["lines"]]
        self.always = g["alwaysFire"]
        self.g0, self.help, self.th = g["initialGain"], g["help"], g["threshold"]
        self.tr, self.te = s["budgets"][K]["second"]["training"], s["budgets"][K]["second"]["testing"]
        self.dose, self.Q, self.rail = g["dose"], g["maxWrites"], g["rail"]

    def line_gain(self, i, a, k):
        return self.g0[i][a] + self.dose * k

    def line_score(self, i, a, k):
        return self.help[i] + self.line_gain(i, a, k)

    def line_need(self, i, a):
        return next((k for k in range(self.Q + 1) if self.th[i] <= self.line_score(i, a, k)), self.Q + 1)

    def expected(self, i, a):
        return self.line_need(i, a) if a in self.lines[i] else 0


class Mirror:
    def __init__(self, s, K):
        self.s, self.K = s, K
        self.p1, self.p2 = Layer1(s, K), Layer2(s, K)
        self.A, self.B, self.M = s["A"], s["B"], s["M"]
        self.o = s["observation"]
        self.lt, self.rt = s["timing"]["left"], s["timing"]["right"]
        self.L = lesson_list(s["second"]["lines"], s["second"]["maxWrites"])
        self.out = []

    def cond(self, checker, kind, where, ok):
        self.out.append((checker, kind, where, bool(ok)))
        return bool(ok)

    # ------------------------------------------------------------------------------------------- the observations
    def ft(self, r, a):
        return self.o["firstTrain"][r][a] if r < self.p1.Q + 1 else EMPTY

    def fx(self, x, a):
        return self.o["firstTest"][mask_index(x, self.M)][a]

    def sx(self, x, i):
        return self.o["secondTest"][mask_index(x, self.M)][i]

    def score_at(self, x, i, y):
        return self.o["scores"][mask_index(x, self.M)][i][mask_index(y, self.A)]

    @staticmethod
    def inp(r):
        return frozenset(j for j, a in enumerate(r["arrivals"]) if a is not None)

    @staticmethod
    def fired(r):
        return len(r["emissions"]) > 0

    def observed_count(self, a, r):
        n = 0
        for k in range(r):
            if not self.fired(self.ft(k, a)):
                n += 1
        return n

    def settled(self, a):
        return self.observed_count(a, self.p1.Q + 1)

    def lesson_counts(self, n):
        w = [[0] * self.A for _ in range(self.B)]
        for m in range(min(n, len(self.L))):
            i, _ = self.L[m]
            r = self.o["secondTrain"][m]
            if not self.fired(r):
                for a in self.inp(r):
                    w[i][a] += 1
        return w

    def patterns(self, n):
        return [mask_of(w, n) for w in range(2 ** n)]

    # ---------------------------------------------------------------------------------------------- validity
    def valid(self):
        p, q, V = self.p1, self.p2, VALID
        # checkConjunctions (MonotoneTarget.lean:79-82; Target.lean:74-93)
        self.cond(V, "first: dose", "first", 0 < p.dose)
        for i in range(p.N):
            n = p.need(i)
            t = p.target[i]
            self.cond(V, "first: nonempty term", f"first {i}", len(t) > 0)
            for k in range(n):
                self.cond(V, "first: early silence", f"first {i} k={k}", robust_silence(p.th[i], p.tr[i], p.score(i, k, t)))
            self.cond(V, "first: stops", f"first {i} need={n}", 0 < n <= p.Q and robust_fire(p.th[i], p.tr[i], p.score(i, n, t)))
            for j in range(p.M):
                self.cond(V, "first: below rail", f"first {i} port {j}", p.gain(i, n, j) < p.rail)
            self.cond(V, "first: positive margin", f"first {i}", robust_fire(p.th[i], p.te[i], p.score(i, n, t)))
            for j in sorted(t):
                omits = frozenset(range(p.M)) - {j}
                self.cond(V, "first: negative margin", f"first {i} omits {j}", robust_silence(p.th[i], p.te[i], p.score(i, n, omits)))
        # Disjunctions.check (MonotoneTarget.lean:61-69)
        self.cond(V, "second: dose", "second", 0 < q.dose)
        exp = [[q.expected(i, a) for a in range(q.A)] for i in range(q.B)]
        for i in range(q.B):
            for a in range(q.A):
                self.cond(V, "second: below rail", f"second {i} line {a}", q.line_gain(i, a, exp[i][a]) < q.rail)
            if q.always[i]:
                self.cond(V, "second: constant cell has no line", f"second {i}", len(q.lines[i]) == 0)
                self.cond(V, "second: constant cell fires", f"second {i}", robust_fire(q.th[i], q.te[i], q.help[i]))
            else:
                for a in sorted(q.lines[i]):
                    k = q.line_need(i, a)
                    ok = 0 < k <= q.Q
                    ok = ok and all(robust_silence(q.th[i], q.tr[i], q.line_score(i, a, n)) for n in range(k))
                    ok = ok and robust_fire(q.th[i], q.tr[i], q.line_score(i, a, k))
                    self.cond(V, "second: line training", f"second {i} line {a} need={k}", ok)
                    self.cond(V, "second: line testing margin", f"second {i} line {a} need={k}", robust_fire(q.th[i], q.te[i], q.line_score(i, a, k)))
                rest = frozenset(range(q.A)) - q.lines[i]
                self.cond(V, "second: silent without its lines", f"second {i}", robust_silence(q.th[i], q.te[i], View(q, exp).score(i, rest)))
        # reachable (MonotoneTarget.lean:86-89)
        for a in range(p.N):
            if any(a in q.lines[i] for i in range(q.B)):
                for b in range(p.N):
                    self.cond(V, "reachable", f"line {a}, cell {b}", contains(p.target[a], p.target[b]) == (a == b))
        for i in range(q.B):
            for a in range(q.A):
                self.cond(V, "delay >= 0", f"delay {i} {a}", self.s["delay"][i][a] >= 0)
        for x in self.s["heldOut"]:
            for a in range(p.N):
                self.cond(V, "held out is not a term", f"heldOut {sorted(x)} term {a}", frozenset(x) != p.target[a])

    # -------------------------------------------------------------------------------------------- separation
    def ends_before(self, n, time):
        ld, rd = self.lt["duration"], self.rt["duration"]
        return all(self.o["teach"][n][a]["start"] + ld <= time for a in range(self.A)) and self.o["secondTrain"][n]["start"] + rd <= time

    def separation(self):
        S, Q, ld = SEP, self.p1.Q, self.lt["duration"]
        A, L = self.A, len(self.L)
        for r in range(Q):
            for a in range(A):
                for b in range(A):
                    self.cond(S, "training rounds", f"round {r} cell {a} -> {r + 1} cell {b}", self.ft(r, a)["start"] + ld <= self.ft(r + 1, b)["start"])
        last = [self.ft(Q, a)["start"] + ld for a in range(A)]
        for n in range(L):
            for a in range(A):
                for b in range(A):
                    self.cond(S, "first layer before teaching", f"lesson {n} cell {b}", last[a] <= self.o["teach"][n][b]["start"])
                self.cond(S, "first layer before teaching", f"lesson {n} second", last[a] <= self.o["secondTrain"][n]["start"])
        for n in range(L):
            for t in range(n + 1, L):
                for a in range(A):
                    self.cond(S, "lessons in order", f"lesson {n} before {t} cell {a}", self.ends_before(n, self.o["teach"][t][a]["start"]))
                self.cond(S, "lessons in order", f"lesson {n} before {t} second", self.ends_before(n, self.o["secondTrain"][t]["start"]))
        for x in self.patterns(self.M):
            for a in range(A):
                for b in range(A):
                    self.cond(S, "training before tests", f"test {sorted(x)} cell {b}", last[a] <= self.fx(x, b)["start"])
                for i in range(self.B):
                    self.cond(S, "training before tests", f"test {sorted(x)} second {i}", last[a] <= self.sx(x, i)["start"])
            for n in range(L):
                for a in range(A):
                    self.cond(S, "lessons before tests", f"lesson {n} test {sorted(x)} cell {a}", self.ends_before(n, self.fx(x, a)["start"]))
                for i in range(self.B):
                    self.cond(S, "lessons before tests", f"lesson {n} test {sorted(x)} second {i}", self.ends_before(n, self.sx(x, i)["start"]))

    # ------------------------------------------------------------------------------------------- calibration
    def threshold_read(self, where, level, tm, r):
        C = CAL
        self.cond(C, "timing valid", where, 0 <= tm["skew"] and 0 < tm["deadline"] and tm["skew"] <= tm["deadline"] < tm["duration"])
        self.cond(C, "skew", where, all(a is None or r["start"] <= a <= r["start"] + tm["skew"] for a in r["arrivals"]))
        em = r["emissions"]
        if len(em) > 1:
            self.cond(C, "one emission", where, False)
        elif len(em) == 1:
            t = em[0]
            self.cond(C, "emission window", where, r["start"] <= t <= r["start"] + tm["deadline"])
            self.cond(C, "v <= t", where, all(a is None or a <= t for a in r["arrivals"]))
        self.cond(C, "FIRE bit", where, self.fired(r) == (level <= r["value"]))

    def additive(self, where, level, tm, r, x, model, budget):
        self.threshold_read(where, level, tm, r)
        self.cond(CAL, "input", where, self.inp(r) == frozenset(x))
        e = r["value"] - model
        self.cond(CAL, "residual", where, -budget <= e <= budget)

    def route(self, where, delay, left, right):
        for a in range(self.A):
            em = left[a]["emissions"]
            want = None if not em else em[0] + delay[a]
            self.cond(CAL, "route", f"{where} line {a}", right["arrivals"][a] == want)

    def firing(self, where, i, w, r, sc):
        q = self.p2
        self.threshold_read(where, q.th[i], self.rt, r)
        inp = self.inp(r)
        self.cond(CAL, "scoreAt = value", where, sc(inp) == r["value"])
        for y in self.patterns(self.A):
            if contains(inp, y) and q.th[i] <= sc(y):
                self.cond(CAL, "submask", f"{where} submask {sorted(y)}", sc(y) <= sc(inp))
        if q.always[i]:
            self.cond(CAL, "anchor", f"{where} empty", q.help[i] - q.te[i] <= sc(frozenset()))
        else:
            for a in range(self.A):
                if a in q.lines[i] and a in inp:
                    self.cond(CAL, "anchor", f"{where} line {a}", q.line_score(i, a, w[i][a]) - q.te[i] <= sc(frozenset({a})))

    def calibration(self):
        p, q = self.p1, self.p2
        A = self.A
        for r in range(p.Q + 1):
            for a in range(A):
                k = self.observed_count(a, r)
                self.additive(f"firstTrain {r} cell {a}", p.th[a], self.lt, self.ft(r, a), p.target[a], p.score(a, k, p.target[a]), p.tr[a])
        settled = [self.settled(a) for a in range(A)]
        for n, (i, line) in enumerate(self.L):
            for a in range(A):
                self.additive(f"teach {n} cell {a}", p.th[a], self.lt, self.o["teach"][n][a], p.target[line], p.score(a, settled[a], p.target[line]), p.te[a])
            st = self.o["secondTrain"][n]
            self.route(f"secondTrain {n}", self.s["delay"][i], self.o["teach"][n], st)
            w = self.lesson_counts(n)
            self.additive(f"secondTrain {n}", q.th[i], self.rt, st, self.inp(st), View(q, w).score(i, self.inp(st)), q.tr[i])
        for x in self.patterns(self.M):
            for a in range(A):
                self.additive(f"firstTest {sorted(x)} cell {a}", p.th[a], self.lt, self.fx(x, a), x, p.score(a, settled[a], x), p.te[a])
        w = self.lesson_counts(len(self.L))
        for x in self.patterns(self.M):
            for i in range(self.B):
                r = self.sx(x, i)
                where = f"secondTest {sorted(x)} cell {i}"
                self.route(where, self.s["delay"][i], [self.fx(x, a) for a in range(A)], r)
                inp = self.inp(r)
                if q.always[i] or any(a in q.lines[i] and a in inp for a in range(A)):
                    self.firing(where, i, w, r, lambda y, x=x, i=i: self.score_at(x, i, y))
                else:
                    self.additive(where, q.th[i], self.rt, r, inp, View(q, w).score(i, inp), q.te[i])

    def run(self):
        self.valid()
        self.separation()
        self.calibration()
        return self.out


EMPTY = dict(start=F(0), arrivals=[], emissions=[], value=0)


def conditions(s, K):
    return Mirror(s, K).run()


def per_checker(conds):
    return {c: all(ok for ch, _, _, ok in conds if ch == c) for c in CHECKERS}


def failing(conds):
    return [(ch, kind, where) for ch, kind, where, ok in conds if not ok]


def verdicts(s):
    """{K: (conjunction, per-checker, failing conditions)} for every named budget of a loaded spec."""
    out = {}
    for K in s["budgets"]:
        c = conditions(s, K)
        pc = per_checker(c)
        out[K] = (all(pc.values()), pc, failing(c))
    return out
