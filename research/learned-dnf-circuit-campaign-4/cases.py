"""Campaign 4: the cases P0 to P6 and P4′ of the kernel gate (PREDICTION.md, The gate on "no" cases; amendment 1;
amendment 2), built from phase 0's CALIBRATION.json only (#172, commit 49684af), with no campaign data.

  cases.py OUT.json OUT_TARGETS.lean     writes the cases and the targets file; prints every failing condition

P0's table (amendment 1, section 8, item 5): a and b are the nominal cell at amplitude 0.49, c at amplitude 1; Z the
file's four decimals in integer units; the latency the file's; c's 0.3-late pair equal to its aligned pair; the dose
of a port at stage k the difference of the stored voltages of stages k and k + 1 (stage 7: that of stage 6), as the
file gives them for port 1, for both ports. The noisy budget uses the constants of decision 5 (the rehearsal has no
validated value). Every number is read exactly (decimals as Decimal, amendment 3). Each case is P0 with the single
change of the table of PREDICTION.md, P4 and P4′ by amendment 2:

  P1  the pair read of a at stage 3, Z set to theta - 1                       a measure; everything recomputed
  P2  the pair read of a at stage 4, Z set to theta                           a measure; everything recomputed
  P3  c's aligned pair at stage min(n1, n2), Z set to c's line a alone at n1, minus 1
                                                                              a measure; everything recomputed
  P4  b's guard-on latency of its pair read at its need + 1/10 unit           a measure; everything recomputed
      then the emission of c's test read on ABCD at the midpoint of its two arrivals (1/20 after the first)
  P4′ (tag P4p) the latency change of P4 alone                                a measure; everything recomputed
  P5  the arrival of line a on c, in the first test slot where a fires, moved 1/10 later  the observation
  P6  the start of a's firstTest read in the first test slot, moved 1/100 earlier         the observation

Choices the table leaves open, fixed before any verdict was computed (commit 3812038): P3 changes the aligned pair
(the 0.3-late copy is taken from P0's table; the test pair's score is the lower of the two, so it is the changed
value either way). P5 and P6 use the first test slot of the calendar (dnf.patterns order) that fits. P6's 1/100 is
below the layer-1 skew bound 1/50, so the arrivals stay within the skew and only the separation from the previous
slot (the last lesson) changes; TrainingSeparation does not order test slots among themselves (amendment 2,
section 5).

The targets (amendment 2, section 3). `conditions` is a Python mirror of the three Lean checkers
(`checkCascadeValid`, `checkTrainingSeparation`, `checkCascadeCalibrationOneSided`, MonotonePremiseTargets.lean,
MonotoneTarget.lean, Target.lean): it lists every condition they hold, read by read, each with its checker, its kind
and its truth, in exact arithmetic on the case's own numbers. `lean_targets` writes a second Lean file, importing the
gate file of gate4.py, that decides the three checkers separately on every case and budget (asserting the mirror's
verdict per checker, so that it compiles only if Lean agrees), and, for P4, the three propositions of amendment 2 on
c's test read on ABCD.
"""
from decimal import Decimal
from fractions import Fraction as F
import copy
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c4                                               # noqa: E402
import predicted as P                                   # noqa: E402
import gate4                                            # noqa: E402
from c4 import dnf                                      # noqa: E402

CALIBRATION = HERE.parent / "learned-dnf-circuit" / "CALIBRATION.json"
AMPLITUDE = dict(a="049", b="049", c="10")


def nominal():
    d = json.loads(CALIBRATION.read_text(), parse_float=Decimal)      # decimals at their exact value (amendment 3)
    t, dose = {}, {}
    for c in c4.CELLS:
        rows = sorted(d["amplitudes"][AMPLITUDE[c]]["table"], key=lambda r: r["stage"])
        assert [r["stage"] for r in rows] == list(range(c4.STAGES))
        for row in rows:
            k = row["stage"]
            for name in P.READS:
                m = row[name]
                z = P.zint(m["Z"])
                assert m["fire"] == (z >= P.THETA), (c, k, name)
                t[(c, k, name)] = dict(Z=z, fire=m["fire"], latency=m["latency"])
            if c == "c":
                t[(c, k, P.SKEWED)] = dict(t[(c, k, "both")])
        u = [r["u_mV"] for r in rows]
        for k in range(c4.STAGES):
            mv = P.exact(u[k] - u[k + 1] if k + 1 < c4.STAGES else u[k - 1] - u[k])
            for p in (1, 2):
                dose[(c, p, k)] = mv
    return t, dose


def predict(t, dose):
    x = P.instance(None, t, dose, [], c4.DECISION5)
    assert x.get("eligible") is not None and "observation" in x, x.get("why_not_eligible")
    return x


def fire_bits(t, key):
    t[key]["fire"] = t[key]["Z"] >= P.THETA


def first_slot(o, test):
    return next(k for k in (("".join(sorted(x)) or "-") for x in dnf.patterns()) if test(k))


def build():
    t0, dose = nominal()
    p0 = predict(t0, dose)
    n = p0["needs"]
    cases = [dict(p0, tag="P0", change="none")]

    t = copy.deepcopy(t0)
    t[("a", 3, "both")]["Z"] = P.THETA - 1
    fire_bits(t, ("a", 3, "both"))
    cases.append(dict(predict(t, dose), tag="P1", change="pair of a at stage 3: Z = theta - 1"))

    t = copy.deepcopy(t0)
    t[("a", 4, "both")]["Z"] = P.THETA
    fire_bits(t, ("a", 4, "both"))
    cases.append(dict(predict(t, dose), tag="P2", change="pair of a at stage 4: Z = theta"))

    t = copy.deepcopy(t0)
    lo = min(n["c1"], n["c2"])
    t[("c", lo, "both")]["Z"] = t0[("c", n["c1"], "port 1")]["Z"] - 1
    fire_bits(t, ("c", lo, "both"))
    cases.append(dict(predict(t, dose), tag="P3", change=f"aligned pair of c at stage {lo}: Z = line a alone at stage {n['c1']} minus 1"))

    t = copy.deepcopy(t0)
    key = ("b", n["b"], "both")
    t[key]["latency"] = P.exact(t0[key]["latency"]) + F(1, 10)
    p4p = predict(t, dose)
    x = copy.deepcopy(p4p)
    d = x["observation"]["secondTest"]["ABCD"]
    a1, a2 = (F(v) for v in d["arrivals"])
    assert a2 - a1 == F(1, 10), (a1, a2)
    d["emissions"] = [str((a1 + a2) / 2)]
    cases.append(dict(x, tag="P4", change=f"b's latency at stage {n['b']} + 1/10; then the emission of c's test read on ABCD at the midpoint {(a1 + a2) / 2} of its arrivals {a1} and {a2}"))
    cases.append(dict(p4p, tag="P4p", change=f"b's latency at stage {n['b']} + 1/10 only"))

    x = copy.deepcopy(p0)
    o = x["observation"]
    k = first_slot(o, lambda k: o["firstTest"][k][0]["emissions"])
    d = o["secondTest"][k]
    d["arrivals"][0] = str(F(d["arrivals"][0]) + F(1, 10))
    cases.append(dict(x, tag="P5", change=f"arrival of line a on c in test slot {k} moved 1/10 later"))

    x = copy.deepcopy(p0)
    o = x["observation"]
    k = first_slot(o, lambda k: True)
    d = o["firstTest"][k][0]
    d["start"] = str(F(d["start"]) - F(1, 100))
    cases.append(dict(x, tag="P6", change=f"start of a's firstTest read in test slot {k} (the first) moved 1/100 earlier"))
    return cases


# ----------------------------------------------------------------------- the Python mirror of the three checkers

VALID, SEP, CAL = "checkCascadeValid", "checkTrainingSeparation", "checkCascadeCalibrationOneSided"
CHECKERS = (VALID, SEP, CAL)
INPUTS = "ABCD"
FIRST = ("a", "b")
TARGET = dict(a={0, 1}, b={2, 3})


class Read:
    def __init__(self, d):
        self.start = F(d["start"])
        self.arrival = [None if v is None else F(v) for v in d["arrivals"]]
        self.emissions = [F(e) for e in d["emissions"]]
        self.value = d["value"]
        self.input = {j for j, v in enumerate(self.arrival) if v is not None}
        self.fired = bool(self.emissions)


class Mirror:
    """The conditions of the three checkers on one case and budget, as (checker, kind, where, ok)."""

    def __init__(self, x, K):
        g, h, dose, b = x["guarded"]["gain"], x["guarded"]["help"], x["guarded"]["dose"], x["budgets"][f"K{K}"]
        self.Q1, self.Q2 = x["Q1"], x["Q2"]
        self.ig = dict(a=[g["a1"], g["a2"], 0, 0], b=[0, 0, g["b1"], g["b2"]])
        self.help1 = dict(a=h["a"], b=h["b"])
        self.tr = dict(a=b["a"]["training"], b=b["b"]["training"])
        self.te = dict(a=b["a"]["testing"], b=b["b"]["testing"])
        self.d1 = dose["a"]
        assert dose["a"] == dose["b"]
        self.cg = [g["c1"], g["c2"]]
        self.ch, self.ctr, self.cte, self.d2 = h["c"], b["c"]["training"], b["c"]["testing"], dose["c"]
        o = x["observation"]
        self.firstTrain = [[Read(c) for c in row] for row in o["firstTrain"]]
        self.teach = [[Read(c) for c in row] for row in o["teach"]]
        self.secondTrain = [Read(c) for c in o["secondTrain"]]
        self.firstTest = {k: [Read(c) for c in row] for k, row in o["firstTest"].items()}
        self.secondTest = {k: Read(c) for k, c in o["secondTest"].items()}
        self.scores = o["scores"]
        # mutation overrides (mirror_mutations.py); the cases use the constants
        self.rail1, self.rail2 = x.get("rail1", P.RAIL), x.get("rail2", P.RAIL)
        self.delay = F(x.get("delay", "3/2"))
        self.timing2 = tuple(F(v) for v in x["timing2"]) if "timing2" in x else (P.SKEW_C, P.DEADLINE_C, P.DURATION_C)
        self.out = []

    def add(self, checker, kind, where, ok):
        self.out.append((checker, kind, where, bool(ok)))

    # first layer, Target.lean
    def gain(self, a, k, j):
        return self.ig[a][j] + self.d1 * (k if j in TARGET[a] else 0)

    def score(self, a, k, x):
        return self.help1[a] + sum(self.gain(a, k, j) for j in sorted(x))

    def need(self, a):
        return next((k for k in range(self.Q1 + 1) if P.THETA <= self.score(a, k, TARGET[a])), self.Q1 + 1)

    # second layer, MonotoneTarget.lean
    def line_gain(self, j, k):
        return self.cg[j] + self.d2 * k

    def line_score(self, j, k):
        return self.ch + self.line_gain(j, k)

    def line_need(self, j):
        return next((k for k in range(self.Q2 + 1) if P.THETA <= self.line_score(j, k)), self.Q2 + 1)

    def view_score(self, w, x):
        return self.ch + sum(self.line_gain(j, w[j]) for j in sorted(x))

    def valid(self):
        th = P.THETA
        self.add(VALID, "dose", "layer 1", 0 < self.d1)
        for a in FIRST:
            nd, tr, te, T = self.need(a), self.tr[a], self.te[a], TARGET[a]
            self.add(VALID, "target nonempty", f"cell {a}", len(T) > 0)
            for k in range(nd):
                self.add(VALID, "guarded margin (early silence)", f"cell {a} stage {k}", self.score(a, k, T) + tr < th)
            self.add(VALID, "need in 1..maxWrites", f"cell {a} need {nd}", 0 < nd <= self.Q1)
            self.add(VALID, "guarded margin (stop, training)", f"cell {a} stage {nd}", th + tr <= self.score(a, nd, T))
            for j in range(4):
                self.add(VALID, "rail", f"cell {a} port {INPUTS[j]} at need", self.gain(a, nd, j) < self.rail1)
            self.add(VALID, "guarded margin (positive, testing)", f"cell {a} stage {nd}", th + te <= self.score(a, nd, T))
            for j in sorted(T):
                omits = set(range(4)) - {j}
                self.add(VALID, "guarded margin (negative, testing)", f"cell {a} stage {nd} without {INPUTS[j]}",
                         self.score(a, nd, omits) + te < th)
        self.add(VALID, "dose", "layer 2", 0 < self.d2)
        for j in (0, 1):
            k = self.line_need(j)
            self.add(VALID, "rail", f"cell c line {'ab'[j]} at need", self.line_gain(j, k) < self.rail2)
            self.add(VALID, "need in 1..maxWrites", f"cell c line {'ab'[j]} need {k}", 0 < k <= self.Q2)
            for m in range(k):
                self.add(VALID, "guarded margin (line silence, training)", f"cell c line {'ab'[j]} stage {m}",
                         self.line_score(j, m) + self.ctr < th)
            self.add(VALID, "guarded margin (line fire, training)", f"cell c line {'ab'[j]} stage {k}", th + self.ctr <= self.line_score(j, k))
            self.add(VALID, "guarded margin (line fire, testing)", f"cell c line {'ab'[j]} stage {k}", th + self.cte <= self.line_score(j, k))
        self.add(VALID, "guarded margin (empty mask silent, testing)", "cell c", self.ch + self.cte < th)
        for a in FIRST:
            for bb in FIRST:
                self.add(VALID, "reachable", f"line {a}, cell {bb}", (TARGET[a] >= TARGET[bb]) == (a == bb))
        self.add(VALID, "delay nonnegative", "both lines", self.delay >= 0)

    def separation(self):
        L, R = P.DURATION_A, self.timing2[2]
        ft, te, st = self.firstTrain, self.teach, self.secondTrain
        for r in range(self.Q1):
            for i, a in enumerate(FIRST):
                for jj, bb in enumerate(FIRST):
                    self.add(SEP, "separation", f"firstTrain {r} {a} before firstTrain {r + 1} {bb}", ft[r][i].start + L <= ft[r + 1][jj].start)
        last = ft[self.Q1]
        for n in range(len(te)):
            for i, a in enumerate(FIRST):
                for jj, bb in enumerate(FIRST):
                    self.add(SEP, "separation", f"last firstTrain {a} before teach {n} {bb}", last[i].start + L <= te[n][jj].start)
                self.add(SEP, "separation", f"last firstTrain {a} before secondTrain {n}", last[i].start + L <= st[n].start)

        def ends(n, time, what):
            for i, a in enumerate(FIRST):
                self.add(SEP, "separation", f"teach {n} {a} before {what}", te[n][i].start + L <= time)
            self.add(SEP, "separation", f"secondTrain {n} before {what}", st[n].start + R <= time)
        for n in range(len(te)):
            for s in range(n + 1, len(te)):
                for jj, bb in enumerate(FIRST):
                    ends(n, te[s][jj].start, f"teach {s} {bb}")
                ends(n, st[s].start, f"secondTrain {s}")
        for k in self.firstTest:
            for i, a in enumerate(FIRST):
                for jj, bb in enumerate(FIRST):
                    self.add(SEP, "separation", f"last firstTrain {a} before firstTest {k} {bb}", last[i].start + L <= self.firstTest[k][jj].start)
                self.add(SEP, "separation", f"last firstTrain {a} before secondTest {k}", last[i].start + L <= self.secondTest[k].start)
        for k in self.firstTest:
            for n in range(len(te)):
                for jj, bb in enumerate(FIRST):
                    ends(n, self.firstTest[k][jj].start, f"firstTest {k} {bb}")
                ends(n, self.secondTest[k].start, f"secondTest {k}")

    def threshold_read(self, where, r, skew, deadline, duration):
        self.add(CAL, "timing valid", where, 0 <= skew and 0 < deadline and skew <= deadline and deadline < duration)
        for j, v in enumerate(r.arrival):
            if v is not None:
                self.add(CAL, "decoder: arrival within the skew", f"{where}, arrival {j}", r.start <= v <= r.start + skew)
        if len(r.emissions) > 1:
            self.add(CAL, "decoder: at most one emission", where, False)
        elif r.emissions:
            t = r.emissions[0]
            self.add(CAL, "decoder: emission within the deadline", where, r.start <= t <= r.start + deadline)
            for j, v in enumerate(r.arrival):
                if v is not None:
                    self.add(CAL, "decoder: v <= t", f"{where}, arrival {j}", v <= t)
        self.add(CAL, "decoder: FIRE bit is the threshold comparison", where, r.fired == (P.THETA <= r.value))

    def additive(self, where, r, x, expected, budget, layer):
        skew, deadline, duration = ((P.SKEW_A, P.DEADLINE_A, P.DURATION_A) if layer == 1 else self.timing2)
        self.threshold_read(where, r, skew, deadline, duration)
        self.add(CAL, "input mask", where, r.input == set(x))
        res = r.value - expected
        self.add(CAL, "residual", where, -budget <= res <= budget)

    def route(self, where, left, right):
        for j in (0, 1):
            e = left[j].emissions
            want = e[0] + self.delay if e else None
            self.add(CAL, "route", f"{where}, line {'ab'[j]}", right.arrival[j] == want)

    def calibration(self):
        observed = {a: [0] for a in FIRST}
        for i, a in enumerate(FIRST):
            for r in range(self.Q1 + 1):
                observed[a].append(observed[a][-1] + (0 if self.firstTrain[r][i].fired else 1))
        settled = {a: observed[a][self.Q1 + 1] for a in FIRST}
        for r in range(self.Q1 + 1):
            for i, a in enumerate(FIRST):
                k = observed[a][r]
                self.additive(f"firstTrain {r} {a}", self.firstTrain[r][i], TARGET[a], self.score(a, k, TARGET[a]), self.tr[a], 1)
        w = [0, 0]
        for n in range(len(self.teach)):
            line = n % 2
            x = TARGET[FIRST[line]]
            for i, a in enumerate(FIRST):
                self.additive(f"teach {n} {a}", self.teach[n][i], x, self.score(a, settled[a], x), self.te[a], 1)
            st = self.secondTrain[n]
            self.route(f"secondTrain {n}", self.teach[n], st)
            self.additive(f"secondTrain {n}", st, st.input, self.view_score(w, st.input), self.ctr, 2)
            if not st.fired:
                for j in st.input:
                    w[j] += 1
        for k, row in self.firstTest.items():
            x = {INPUTS.index(v) for v in k if v != "-"}
            for i, a in enumerate(FIRST):
                self.additive(f"firstTest {k} {a}", row[i], x, self.score(a, settled[a], x), self.te[a], 1)
        for k, r in self.secondTest.items():
            where = f"secondTest {k}"
            self.route(where, self.firstTest[k], r)
            if r.input:
                self.threshold_read(where, r, *self.timing2)
                sc = self.scores[k]
                at = lambda y: sc["".join(str(j + 1) for j in sorted(y)) or "-"]
                self.add(CAL, "measured score = scoreAt(input)", where, at(r.input) == r.value)
                for y in ({0}, {1}, {0, 1}, set()):
                    if y <= r.input and P.THETA <= at(y):
                        self.add(CAL, "submask comparison", f"{where}, submask {''.join('ab'[j] for j in sorted(y)) or 'empty'}", at(y) <= at(r.input))
                for j in sorted(r.input):
                    self.add(CAL, "anchor", f"{where}, line {'ab'[j]}", self.line_score(j, w[j]) - self.cte <= at({j}))
            else:
                self.additive(where, r, r.input, self.view_score(w, r.input), self.cte, 2)
        self.writes = w

    def run(self):
        self.valid()
        self.separation()
        self.calibration()
        return self.out


def conditions(x, K):
    return Mirror(x, K).run()


def per_checker(conds):
    return {c: all(ok for ch, _, _, ok in conds if ch == c) for c in CHECKERS}


# --------------------------------------------------------------------------------------------- the targets file

def lean_targets(cases, verdicts, gate_module):
    out = [f"import {gate_module}", "", "/-! Campaign 4: the targets of amendment 2, section 3, written by cases.py. Each checker is",
           "decided separately on every case and budget; the asserted value is the Python mirror's. -/", "",
           "namespace LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4", "", "open TwoLayer (SlotTiming ReadObservation)", ""]
    for x in cases:
        for K in (0, 3):
            tag, v = x["tag"], verdicts[(x["tag"], K)]
            cn, tn = f"cascade_{tag}_K{K}", f"trace_{tag}_K{K}"
            b = lambda c: "true" if v[c] else "false"
            out += ["set_option maxRecDepth 100000 in", "set_option maxHeartbeats 0 in",
                    f"theorem valid_{tag}_K{K} : checkCascadeValid {cn} = {b(VALID)} := by decide +kernel", "",
                    "set_option maxRecDepth 100000 in", "set_option maxHeartbeats 0 in",
                    f"theorem separation_{tag}_K{K} : checkTrainingSeparation {cn} left right {tn}.observations = {b(SEP)} := by decide +kernel", "",
                    "set_option maxRecDepth 100000 in", "set_option maxHeartbeats 0 in",
                    f"theorem calibration_{tag}_K{K} : checkCascadeCalibrationOneSided {cn} left right {tn}.observations {tn}.scoreAt = {b(CAL)} := by decide +kernel", ""]
    p4 = next(x for x in cases if x["tag"] == "P4")
    d = p4["observation"]["secondTest"]["ABCD"]
    t, vb = F(d["emissions"][0]), F(d["arrivals"][1])
    r = "(trace_P4_K0.observations.secondTest (pattern [0, 1, 2, 3]) 0)"
    out += [
        "/-! P4 (amendment 2, section 3): c's test read on ABCD. -/", "",
        f"theorem p4_emission : {r}.emissions = [{gate4.r(t)}] := by decide +kernel", "",
        f"theorem p4_arrival_b : {r}.arrival 1 = some {gate4.r(vb)} := by decide +kernel", "",
        "/-- `∀ j v, arrival j = some v → v ≤ t` is false: line b's arrival is after the emission. -/",
        f"theorem p4_not_all_arrivals_before : ¬ ∀ j v, {r}.arrival j = some v → v ≤ {gate4.r(t)} :=",
        f"  fun h => absurd (h 1 _ p4_arrival_b) (by decide +kernel)", "",
        "/-- The same condition as a check over the two lines. -/",
        f"theorem p4_arrivals_before_check : (List.finRange 2).all (fun j => ({r}.arrival j).all fun v => decide (v ≤ {gate4.r(t)})) = false := by decide +kernel", "",
        f"theorem p4_emission_window : {r}.start ≤ {gate4.r(t)} ∧ {gate4.r(t)} ≤ {r}.start + right.deadline := by decide +kernel", "",
        f"theorem p4_arrivals_in_skew_check : (List.finRange 2).all (fun j => ({r}.arrival j).all fun v => decide ({r}.start ≤ v ∧ v ≤ {r}.start + right.skew)) = true := by decide +kernel", "",
        "/-- Every arrival lies in `[s, s + skew]`. -/",
        f"theorem p4_arrivals_in_skew : ∀ j v, {r}.arrival j = some v → {r}.start ≤ v ∧ v ≤ {r}.start + right.skew := by",
        "  intro j v h",
        "  have all := p4_arrivals_in_skew_check",
        "  rw [List.all_eq_true] at all",
        "  have hj := all j (List.mem_finRange j)",
        "  rw [h] at hj",
        "  simpa using hj", "",
        "end LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4", ""]
    return "\n".join(out)


def main():
    print(c4.require_pinned())
    cases = build()
    Path(sys.argv[1]).write_text(json.dumps(dict(source="CALIBRATION.json, #172, 49684af", cases=cases), indent=1, default=str))
    verdicts = {}
    for x in cases:
        g = gate4.verdicts(x)
        for K in (0, 3):
            conds = conditions(x, K)
            v = per_checker(conds)
            verdicts[(x["tag"], K)] = v
            fails = [c for c in conds if not c[3]]
            print(f"{x['tag']} K{K}: gate {'yes' if g[f'K{K}'] else 'no'}; mirror " + ", ".join(f"{c}={'T' if v[c] else 'F'}" for c in CHECKERS)
                  + f"; {len(conds)} conditions, {len(fails)} failing" + (f" | {x['change']}" if K == 0 else ""))
            for ch, kind, where, _ in fails:
                print(f"    FAIL {ch}: {kind}: {where}")
    Path(sys.argv[2]).write_text(lean_targets(cases, verdicts, Path(sys.argv[3] if len(sys.argv) > 3 else "Gate4Cases").stem))


if __name__ == "__main__":
    main()
