"""A Python mirror of the four layered checkers (LAYERED_GENERATOR_DESIGN.md, section 4).

A direct transliteration, in exact ints and Fractions, of
  checkLayeredValid                (LayeredMonotoneCheckerTargets.lean:84-88)
  checkLayeredSeparation           (:90-93)
  checkLayeredTrainingCalibration  (:95-107)
  checkLayeredReadCalibration      (:109-111)
and of what they use from LayeredMonotoneTarget.lean (Cell.score, stop, expectedWrites, groupObserved, writesBefore,
settledWrites, Cascade.predict, readWindows, trainingBatches, pulseDates) and MonotonePremiseTargets.lean
(checkThresholdRead). It works on a loaded spec (lspec.load). Every elementary condition is recorded as
(checker, kind, where, ok). A checker's verdict is the conjunction of its conditions, as the Lean `&&` and `all`
are conjunctions.

The mirror decides nothing by itself: the Lean file asserts the verdict and the kernel checks it.
"""
from fractions import Fraction as F

from lspec import ANCHORS, GROUP_MASK, GROUPS, USES, evaluate

VALID, SEP, TRAIN, READ = "checkLayeredValid", "checkLayeredSeparation", "checkLayeredTrainingCalibration", "checkLayeredReadCalibration"
CHECKERS = (VALID, SEP, TRAIN, READ)
MASKS2 = [(False, False), (False, True), (True, False), (True, True)]   # maskIndex order (port 0 most significant)
EMPTY = dict(start=F(0), arrivals=[None, None], emissions=[], value=0)


def mask_index2(x):
    return 2 * x[0] + x[1]


def contains(read, y):
    return all(r or not t for r, t in zip(read, y))


class CellModel:
    def __init__(self, n):
        self.n = n
        self.gate = n["gate"]

    def gain(self, w, a):
        return self.n["initialGain"][a] + self.n["dose"] * w[a]

    def score(self, w, x):
        return self.n["help"] + (self.gain(w, 0) if x[0] else 0) + (self.gain(w, 1) if x[1] else 0)

    def group_writes(self, g, k):
        m = GROUP_MASK[self.gate][g]
        return [k if m[a] else 0 for a in (0, 1)]

    def group_score(self, g, k):
        return self.score(self.group_writes(g, k), GROUP_MASK[self.gate][g])

    def stop(self, g):
        Q = self.n["maxWrites"]
        return next((k for k in range(Q + 1) if self.n["threshold"] <= self.group_score(g, k)), Q + 1)

    def expected(self):
        G = GROUPS[self.gate]
        w = [0, 0]
        for g in range(G):
            gw = self.group_writes(g, self.stop(g))
            w = [w[a] + gw[a] for a in (0, 1)]
        return w

    # observed counts, from the cell's training reads train[g][r] (absent = the empty read)
    @staticmethod
    def get(train, g, r):
        if g < len(train) and r < len(train[g]):
            return train[g][r]["read"]
        return EMPTY

    def group_observed(self, train, g, a, r):
        return sum(1 for k in range(r) if not self.get(train, g, k)["emissions"] and self.get(train, g, k)["arrivals"][a] is not None)

    def writes_before(self, train, g, r):
        Q = self.n["maxWrites"]
        return [(0 if g == 0 else self.group_observed(train, 0, a, Q + 1)) + self.group_observed(train, g, a, r) for a in (0, 1)]

    def settled(self, train):
        Q, G = self.n["maxWrites"], GROUPS[self.gate]
        return [(self.group_observed(train, 0, a, Q + 1) if G > 0 else 0) + (self.group_observed(train, 1, a, Q + 1) if G > 1 else 0) for a in (0, 1)]


def inp(r):
    return tuple(a is not None for a in r["arrivals"])


class Mirror:
    def __init__(self, s):
        self.s = s
        self.L = len(s["layers"])
        self.cells = [[CellModel(n) for n in lay["nodes"]] for lay in s["layers"]]
        self.out = []

    def cond(self, ch, kind, where, ok):
        self.out.append((ch, kind, where, bool(ok)))
        return bool(ok)

    # ------------------------------------------------------------------------------------------- prediction
    def node_inputs(self, n, lower_out):
        return tuple((lower_out[n["source"][a]] if n["source"][a] is not None else False) for a in (0, 1))

    def predict(self, x, upto):
        """Outputs of layer `upto` (0 = the inputs) on an external pattern x (a set of input indices)."""
        out = [j in x for j in range(self.s["M"])]
        for l in range(upto):
            out = [evaluate(n["gate"], self.node_inputs(n, out)) for n in self.s["layers"][l]["nodes"]]
        return out

    # ---------------------------------------------------------------------------------------------- validity
    def timing_ok(self, t):
        return 0 <= t["skew"] and 0 < t["deadline"] and t["skew"] <= t["deadline"] < t["duration"]

    def valid(self):
        V = VALID
        for l, lay in enumerate(self.s["layers"]):
            self.cond(V, "timing valid", f"layer {l + 1}", self.timing_ok(lay["timing"]))
            for i, n in enumerate(lay["nodes"]):
                c, where = self.cells[l][i], f"L{l + 1}.{i}"
                th, tr, te = n["threshold"], n["trainError"], n["testError"]
                self.cond(V, "cell: dose", where, 0 < n["dose"])
                for g in range(GROUPS[c.gate]):
                    st = c.stop(g)
                    self.cond(V, "cell: stop in range", f"{where} group {g} stop {st}", 0 < st <= n["maxWrites"])
                    for k in range(st):
                        self.cond(V, "cell: early silence", f"{where} group {g} k={k}", c.group_score(g, k) + tr < th)
                    self.cond(V, "cell: stops", f"{where} group {g}", th + tr <= c.group_score(g, st))
                w = c.expected()
                for a in (0, 1):
                    self.cond(V, "cell: below rail", f"{where} port {a}", c.gain(w, a) < n["rail"])
                for x in MASKS2:
                    if not evaluate(c.gate, x):
                        self.cond(V, "cell: silent mask", f"{where} mask {x}", c.score(w, x) + te < th)
                for y in ANCHORS[c.gate]:
                    self.cond(V, "cell: anchor fires", f"{where} anchor {y}", th + te <= c.score(w, y))
                for a in (0, 1):
                    self.cond(V, "node: source matches gate", f"{where} port {a}", (n["source"][a] is not None) == USES[c.gate][a])
                    self.cond(V, "node: delay >= 0", f"{where} port {a}", n["delay"][a] >= 0)
                for g in range(GROUPS[c.gate]):
                    got = self.node_inputs(n, self.predict(n["stimulus"][g], l))
                    self.cond(V, "node: stimulus gives the group mask", f"{where} group {g}", got == GROUP_MASK[c.gate][g])

    # -------------------------------------------------------------------------------------------- separation
    def read_windows(self, rt, k):
        """readWindows of a ReadTrace of the layers 1..k."""
        out = [(a, a) for a in rt["arrivals"] if a is not None]
        for l in range(k):
            d = self.s["layers"][l]["timing"]["duration"]
            out += [(c["read"]["start"], c["read"]["start"] + d) for c in rt["layers"][l]]
        return out

    def batches(self):
        out = []
        for l, lay in enumerate(self.s["layers"]):
            d = lay["timing"]["duration"]
            for i, n in enumerate(lay["nodes"]):
                for g, rounds in enumerate(self.s["training"][l][i]):
                    for r, x in enumerate(rounds):
                        st = x["read"]["start"]
                        out.append((f"L{l + 1}.{i} group {g} round {r}", self.read_windows(x["replay"], l) + [(st, st + d)]))
        return out

    @staticmethod
    def before(earlier, later):
        return all(a[1] <= b[0] for a in earlier for b in later)

    def separation(self):
        S = SEP
        bs = self.batches()
        for k, (name, b) in enumerate(bs):
            for name2, b2 in bs[k + 1:]:
                self.cond(S, "batches in order", f"{name} before {name2}", self.before(b, b2))
        for w, t in enumerate(self.s["tests"]):
            tw = self.read_windows(t, self.L)
            for name, b in bs:
                self.cond(S, "training before tests", f"{name} before test {w}", self.before(b, tw))

    # ------------------------------------------------------------------------------------------- calibration
    def threshold_read(self, ch, where, level, t, r):
        self.cond(ch, "timing valid", where, self.timing_ok(t))
        self.cond(ch, "skew", where, all(a is None or r["start"] <= a <= r["start"] + t["skew"] for a in r["arrivals"]))
        em = r["emissions"]
        if len(em) > 1:
            self.cond(ch, "one emission", where, False)
        elif len(em) == 1:
            self.cond(ch, "emission window", where, r["start"] <= em[0] <= r["start"] + t["deadline"])
            self.cond(ch, "v <= t", where, all(a is None or a <= em[0] for a in r["arrivals"]))
        self.cond(ch, "FIRE bit", where, bool(em) == (level <= r["value"]))

    def pulse_dates(self, rt, k):
        """pulseDates of a ReadTrace of layers 1..k: the arrivals (k = 0) or the first emission of each top cell."""
        if k == 0:
            return rt["arrivals"]
        return [c["read"]["emissions"][0] if c["read"]["emissions"] else None for c in rt["layers"][k - 1]]

    def routed(self, ch, where, n, incoming, r):
        for a in (0, 1):
            s = n["source"][a]
            want = None if s is None or incoming[s] is None else incoming[s] + n["delay"][a]
            self.cond(ch, "route", f"{where} port {a}", r["arrivals"][a] == want)

    def additive(self, ch, where, c, w, budget, t, r):
        self.threshold_read(ch, where, c.n["threshold"], t, r)
        e = r["value"] - c.score(w, inp(r))
        self.cond(ch, "residual", where, -budget <= e <= budget)

    def firing(self, ch, where, c, w, t, r, scores):
        sc = lambda y: scores[mask_index2(y)]
        x = inp(r)
        self.threshold_read(ch, where, c.n["threshold"], t, r)
        self.cond(ch, "scoreAt = value", where, sc(x) == r["value"])
        for y in MASKS2:
            if contains(x, y) and c.n["threshold"] <= sc(y):
                self.cond(ch, "submask", f"{where} submask {y}", sc(y) <= sc(x))
        for y in ANCHORS[c.gate]:
            if contains(x, y):
                self.cond(ch, "anchor", f"{where} anchor {y}", c.score(w, y) - c.n["testError"] <= sc(y))

    def one_read(self, ch, where, x, rt, k):
        """Checker.oneRead on a ReadTrace of layers 1..k for external pattern x (a set of input indices)."""
        self.cond(ch, "replay input", f"{where} arrivals", [a is not None for a in rt["arrivals"]] == [j in x for j in range(self.s["M"])])
        for l in range(k):
            t = self.s["layers"][l]["timing"]
            incoming = self.pulse_dates(rt, l)
            for i, n in enumerate(self.s["layers"][l]["nodes"]):
                c = self.cells[l][i]
                cell = rt["layers"][l][i]
                r, w = cell["read"], c.settled(self.s["training"][l][i])
                wh = f"{where} L{l + 1}.{i}"
                self.routed(ch, wh, n, incoming, r)
                if evaluate(c.gate, inp(r)):
                    self.firing(ch, wh, c, w, t, r, cell["scores"])
                else:
                    self.additive(ch, wh, c, w, n["testError"], t, r)

    def training(self):
        T = TRAIN
        for l, lay in enumerate(self.s["layers"]):
            t = lay["timing"]
            for i, n in enumerate(lay["nodes"]):
                c = self.cells[l][i]
                train = self.s["training"][l][i]
                for g, rounds in enumerate(train):
                    for r, x in enumerate(rounds):
                        where = f"lesson L{l + 1}.{i} group {g} round {r}"
                        self.one_read(T, where + " replay", n["stimulus"][g], x["replay"], l)
                        self.routed(T, where, n, self.pulse_dates(x["replay"], l), x["read"])
                        self.additive(T, where, c, c.writes_before(train, g, r), n["trainError"], t, x["read"])

    def reads(self):
        for w, rt in enumerate(self.s["tests"]):
            x = frozenset(j for j in range(self.s["M"]) if w >> (self.s["M"] - 1 - j) & 1)   # maskIndex: input 0 is the MSB
            self.one_read(READ, f"test {sorted(x)}", x, rt, self.L)

    def run(self):
        self.valid()
        self.separation()
        self.training()
        self.reads()
        return self.out


def verdicts(s):
    out = Mirror(s).run()
    pc = {c: all(ok for ch, _, _, ok in out if ch == c) for c in CHECKERS}
    return all(pc.values()), pc, [(ch, k, w) for ch, k, w, ok in out if not ok]


def predict(s, x):
    return Mirror(s).predict(x, len(s["layers"]))
