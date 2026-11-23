"""Tests of family_predict.py that need no B2 file and no Lean (TOPUP_RULES.md 3.5.11, the synthetic part).

  PYTHONPATH=FUP/dev:PREP/dev:. python -B test_family_predict.py REPO GEN

- the unary-port rule of TOPUP_RULES.md 1 and the size rule of 2;
- the anchors of 3.5.2 on hand values, for each cell kind and both forms of c;
- synthetic decks: for every member, an exactly additive table (no residual) through the guarded fit, the budgets,
  the observation and the spec; the guarded tuple must return the model's numbers, epsilon must be 0, and the
  generator's mirror must give true at K = 0 and K = 3;
- the generator's own synth.py design for each member's shape through spec.load and the mirror;
- the refusals of 3.5.7 that need no deck: a run missing or not complete, a preset read not silent.
"""
from fractions import Fraction as F
import sys
import unittest

REPO, GEN = sys.argv.pop(1), sys.argv.pop(1)
import family_predict as FP                               # noqa: E402
FP.paths(REPO, GEN)
predict6, P, spec, mirror, emit = FP.mods()
THETA = P.THETA


def synthetic(member, uport, d=12500, dc=20000, s1=F(5, 2), s_c=F(5, 2), lat=F(1, 2)):
    """An exactly additive mapped table: layer 1 on one dose d, a pair cell's gains d (K - s1) with K = 4, a unary
    cell's gain THETA - d s1, c on dc with gains THETA - dc s_c; latencies `lat`; c's slot latencies its one FIRE."""
    kd = FP.kinds(member)
    nl = len(kd)
    K = 4
    gain = {}
    for c, k in kd.items():
        if k == "pair":
            gain[(c, 1)] = gain[(c, 2)] = int(d * (K - s1))
        else:
            gain[(c, uport[c])] = int(THETA - d * s1)
    for p in range(1, nl + 1):
        gain[("c", p)] = int(THETA - dc * s_c) if nl == 2 else int(THETA - dc * s_c)
    t = {}

    def put(c, k, r, ps, dose):
        z = sum(gain[(c, p)] + dose * k for p in ps)
        e = dict(Z=z, fire=z >= THETA, latency=lat if z >= THETA else None)
        if c == "c":
            e["slot_latencies"] = [lat] if z >= THETA else []
        t[(c, k, r)] = e
    for k in range(8):
        for c, kind in kd.items():
            for r in FP.cell_reads(kind, uport.get(c)):
                put(c, k, r, P.ports(r), d)
        for r in FP.c_reads(nl, P):
            put("c", k, r, (1, 2) if r in ("both", P.SKEWED) else P.ports(r), dc)
    dose = {(c, p, k): F(2) for c in list(kd) + ["c"] for p in (1, 2) for k in range(8)}
    return t, dose, gain


class Ports(unittest.TestCase):
    def scan(self, s):
        return dict(crossing=True, consistent=True, s_star=str(s))

    def test_choice(self):
        pr = dict(silent={"1": True, "2": True})
        self.assertEqual(FP.unary_port({1: self.scan(F(201, 128)), 2: self.scan(F(150, 128))}, pr)[0], 1)
        self.assertEqual(FP.unary_port({1: self.scan(F(150, 128)), 2: self.scan(F(201, 128))}, pr)[0], 2)
        self.assertEqual(FP.unary_port({1: self.scan(F(3, 2) + F(1, 512)), 2: self.scan(F(5, 2) - F(1, 512))}, pr)[0], 1)   # exact tie
        self.assertEqual(FP.margin(F(3, 2) + F(1, 512)), FP.margin(F(5, 2) - F(1, 512)))

    def test_eligibility(self):
        pr = dict(silent={"1": True, "2": False})
        self.assertEqual(FP.unary_port({1: self.scan(F(150, 128)), 2: self.scan(F(201, 128))}, pr)[0], 1)   # 2 not silent
        self.assertEqual(FP.unary_port({1: None, 2: self.scan(F(150, 128))}, dict(silent={"1": True, "2": True}))[0], 2)
        bad = dict(crossing=True, consistent=False, s_star="3/2")
        self.assertEqual(FP.unary_port({1: bad, 2: self.scan(F(150, 128))}, dict(silent={"1": True, "2": True}))[0], 2)
        self.assertEqual(FP.unary_port({1: None, 2: None}, None)[0], 1)                                    # neither: port 1
        port, det = FP.unary_port({1: self.scan(F(150, 128)), 2: self.scan(F(201, 128))}, None)
        self.assertEqual(port, 1)
        self.assertFalse(det["ports"][1]["eligible"] or det["ports"][2]["eligible"])


class Size(unittest.TestCase):
    def rows(self, r):
        rows = [dict(seed=s, members={}) for s in FP.SEEDS]
        for m, n in r.items():
            for i in range(n):
                rows[i]["members"][m] = dict(room_K3=True)
        return rows

    def test_rule(self):
        s = FP.summary(self.rows(dict(X1=4, X2=6, F4=2, F2=3, F3=1)), FP.STEP1)
        self.assertEqual(s["removed"], ["F3"])
        self.assertEqual(s["kept"], ["X1", "X2", "F4", "F2"])
        self.assertEqual(s["I"], 16)                        # ceil(30 / 2) = 15, up to a multiple of 4
        s = FP.summary(self.rows(dict(X1=1, X2=6, F4=0, F2=3, F3=1)), FP.STEP1)
        self.assertFalse(s["campaign"])                     # 2 members left
        self.assertIsNone(s["I"])
        s = FP.summary(self.rows(dict(X1=10, X2=10, F4=10, F2=10, F3=10)), FP.STEP1)
        self.assertEqual(s["I"], 5)                          # ceil(30 / 10) = 3, up to a multiple of 5


class Anchors(unittest.TestCase):
    def test_kinds(self):
        S = {("a", "pair"): F(3, 2), ("b", "pair"): F(5, 2), ("a", "unary"): F(7, 4), ("b", "unary"): F(9, 4),
             ("c", "line1"): F(2), ("c", "line2"): F(3)}
        an = FP.anchors("F3", {"a": 1}, S, dict(a=True, b=True), THETA)
        K = max(8 - F(3, 2), F(3, 2), 8 - F(5, 2), F(5, 2))
        self.assertEqual(an["K"], K)
        d = round(F(THETA) / (2 * K))
        self.assertEqual(an["d"], d)
        self.assertEqual(an["gain"][("a", 1)], round(THETA - d * F(7, 4)))
        self.assertNotIn(("a", 2), an["gain"])
        self.assertEqual(an["gain"][("b", 1)], round(d * (K - F(5, 2))))
        self.assertEqual(an["d_c"], round(F(THETA) / 5))
        an = FP.anchors("X1", {"a": 2}, S, dict(a=False, b=False), THETA)
        self.assertEqual(an["K"], 8)                         # neither pair scan consistent
        self.assertEqual(an["K_c"], max(8 - F(2), F(2)))
        self.assertEqual(an["d_c"], round(F(THETA) / 12))
        self.assertEqual(an["gain"][("c", 1)], round(THETA - an["d_c"] * 2))
        self.assertNotIn(("c", 2), an["gain"])
        an = FP.anchors("X2", {}, S, dict(a=True, b=False), THETA)
        self.assertEqual(an["K"], max(8 - F(3, 2), F(3, 2)))  # only a's pair scan

    def test_same_as_predict6_for_F1(self):
        S = {("a", "pair"): F(781, 512), ("b", "pair"): F(1001, 512), ("c", "line1"): F(1201, 512), ("c", "line2"): F(700, 512)}
        a6 = predict6.anchors(S)
        an = FP.anchors("F1", {}, S, dict(a=True, b=True), THETA)
        self.assertEqual((an["K"], an["d"], an["d_c"], an["W"]), (a6["K"], a6["d"], a6["d_c"], a6["W"]))
        self.assertEqual(an["gain"], a6["gain"])


class Synthetic(unittest.TestCase):
    """Each member on an exactly additive deck: the whole chain after the mapping, to the mirror."""

    def chain(self, member, uport):
        t, dose, gain = synthetic(member, uport)
        kd = FP.kinds(member)
        n = {c: 3 for c in kd}
        n.update({f"c{p}": 3 for p in range(1, len(kd) + 1)})
        H = {c: 50 for c in list(kd) + ["c"]}
        x = dict(member=member, unary_ports={c: uport[c] for c, k in kd.items() if k == "unary"})
        x.update(FP.budget_and_tuple(member, x["unary_ports"], t, dose, n, H, {c: 0 for c in H}, P))
        x["observation"] = FP.observation(member, x["unary_ports"], t, n, x["Q1"], x["Q2"], P)
        return x, gain

    def test_members(self):
        for member in FP.STEP1 + ("F1",):
            for up in ({"a": 1, "b": 1}, {"a": 2, "b": 2}, {"a": 1, "b": 2}):
                with self.subTest(member=member, ports=up):
                    x, gain = self.chain(member, up)
                    self.assertEqual(x["Q1"], 5)
                    self.assertEqual({k: 0 for k in x["epsilon"]}, x["epsilon"])
                    self.assertEqual(x["guarded"]["dose"][list(FP.kinds(member))[0]], 12500)
                    self.assertEqual(x["guarded"]["dose"]["c"], 20000)
                    self.assertEqual({k: v for k, v in x["guarded"]["gain"].items()}, {f"{c}{p}": g for (c, p), g in gain.items()})
                    self.assertTrue(all(v == 0 for v in x["guarded"]["help"].values()))
                    s = spec.load(FP.raw_spec(x, f"S_{member}", "test"))
                    v = FP.mirror_verdicts(s)
                    self.assertTrue(v["K0"]["checks"], v["K0"]["failing"][:5])
                    self.assertTrue(v["K3"]["checks"], v["K3"]["failing"][:5])
                    shape = {"X1": (1, 1, 1), "X2": (1, 1, 2), "F4": (2, 1, 2), "F2": (2, 1, 3), "F3": (2, 1, 3), "F1": (2, 1, 4)}[member]
                    self.assertEqual((s["A"], s["B"], s["M"]), shape)
                    self.assertTrue(s["physical"]["two_port"])

    def test_F2_partial_teaching_rows(self):
        """F2: in lesson a, b reads A alone (port 1); in lesson b, a reads A alone (port 1) (3.5.8)."""
        x, _ = self.chain("F2", {})
        t, _, _ = synthetic("F2", {})
        teach = x["observation"]["teach"]
        self.assertEqual(teach[0][1]["value"], t[("b", 3, "port 1")]["Z"])
        self.assertEqual(teach[1][0]["value"], t[("a", 3, "port 1")]["Z"])
        self.assertEqual(teach[0][1]["emissions"], [])
        x3, _ = self.chain("F3", {"a": 2})
        t3, _, _ = synthetic("F3", {"a": 2})
        self.assertEqual(x3["observation"]["teach"][0][1]["value"], t3[("b", 3, "empty")]["Z"])   # F3: nothing shared

    def test_spec_refuses_a_broken_observation(self):
        x, _ = self.chain("X1", {"a": 1})
        raw = FP.raw_spec(x, "S_X1", "test")
        raw["observation"]["teach"].pop()
        with self.assertRaises(spec.SpecError):
            spec.load(raw)

    def test_mirror_fails_a_residual_over_budget(self):
        x, _ = self.chain("F3", {"a": 1})
        raw = FP.raw_spec(x, "S_F3", "test")
        raw["observation"]["firstTest"][0][0]["value"] += x["budgets"]["K0"]["a"]["testing"] + 1
        v = FP.mirror_verdicts(spec.load(raw))
        self.assertFalse(v["K0"]["checks"])
        self.assertTrue(all(f[1] == "residual" for f in v["K0"]["failing"]))


class GeneratorSynth(unittest.TestCase):
    def test_each_shape(self):
        import synth
        for member in FP.STEP1:
            m = FP.MEMBERS[member]
            terms = [sorted(m["inputs"].index(i) for i in m["terms"][c]) for c in FP.kinds(member)]
            raw = synth.observation(synth.design(f"G_{member}", len(m["inputs"]), terms, [list(range(len(terms)))]), "zero")
            s = spec.load(raw)
            self.assertTrue(mirror.verdicts(s)["K0"][0], member)


class Refusals(unittest.TestCase):
    def test_missing_runs(self):
        row = FP.one_seed(8301, ["X1", "X2"], "/nonexistent", ["/nonexistent"], {}, {})
        for m in ("X1", "X2"):
            x = row["members"][m]
            self.assertFalse(x["measured"])
            self.assertTrue(any("did not complete: missing" in w for w in x["why_not_measured"]))

    def test_listed_but_not_on_disk(self):
        st = {f"8301-{t}": "complete" for t in ("cal-on", "cal-off", "scan-a-pair", "onesided-a", "scan-c-line1")}
        x = FP.one_seed(8301, ["X2"], "/nonexistent", [], st, {})["members"]["X2"]
        self.assertFalse(x["measured"])
        self.assertTrue(any("missing on disk" in w for w in x["why_not_measured"]))

    def test_ids(self):
        self.assertEqual(FP.b2_run_ids(8305, "X1"), ["8305-cal-on", "8305-cal-off", "8305-scan-c-line1"])
        self.assertEqual(FP.tu_run_ids(8305, "F4", {"a": 2, "b": 1}),
                         ["8305-cal-on-unary", "8305-cal-off-unary", "8305-unary-scan-a2", "8305-preset-a", "8305-unary-scan-b1", "8305-preset-b"])
        self.assertEqual(FP.b2_run_ids(8305, "F2"), ["8305-cal-on", "8305-cal-off", "8305-scan-a-pair", "8305-onesided-a", "8305-scan-b-pair",
                                                     "8305-onesided-b", "8305-scan-c-line1", "8305-scan-c-line2", "8305-bothfire-c"])
        self.assertEqual(FP.tu_run_ids(8305, "F2", {}), [])

    def test_wiring(self):
        self.assertEqual(FP.wiring("F2", {}), dict(a=dict(A=1, B=2), b=dict(A=1, C=2)))
        self.assertEqual(FP.wiring("F3", {"a": 2}), dict(a=dict(A=2), b=dict(B=1, C=2)))
        self.assertEqual(FP.wiring("F4", {"a": 1, "b": 2}), dict(a=dict(A=1), b=dict(B=2)))
        self.assertEqual(len(FP.patterns(("A", "B", "C"))), 8)
        self.assertEqual(FP.patterns(("A", "B", "C", "D")), [frozenset(x) for x in __import__("dnf").patterns()])


if __name__ == "__main__":
    unittest.main(verbosity=1)
