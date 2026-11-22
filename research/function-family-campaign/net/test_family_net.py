"""Tests of family_net.py. No simulation: session4.play is never called for real (the runner's test replaces it with a
fake that writes empty evidence files).

  test_family_net.py REPO        REPO: research/learned-dnf-circuit-campaign-6-impl at ecfcd1c1
"""
from fractions import Fraction as F
import itertools
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

REPO = sys.argv.pop(1) if len(sys.argv) > 1 and not sys.argv[1].startswith("-") else os.environ.get("REPO")
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import family_net as N                                     # noqa: E402

N.paths(REPO)
import c4                                                  # noqa: E402
import plans4                                              # noqa: E402
import predicted as P                                      # noqa: E402  (campaign 5's P: q, mask_read, SKEWED, as family_predict uses it)
from c4 import dnf                                         # noqa: E402
import family_predict as fp                                # noqa: E402

CONTROLS = (None, "skew", "untrained")
STEP1 = ("X1", "X2", "F4", "F2", "F3")


def js(x):
    return json.dumps(x, sort_keys=True)


def unary_cells(member):
    return [c for c, k in fp.kinds(member).items() if k == "unary"]


def port_choices(member):
    """Every assignment of a port 1 or 2 to the member's unary cells ({} for a member without one)."""
    u = unary_cells(member)
    return [dict(zip(u, ps)) for ps in itertools.product((1, 2), repeat=len(u))]


def needs_grid(member, top, low=0):
    keys = N.needs_keys(member)
    return [dict(zip(keys, v)) for v in itertools.product(range(low, top + 1), repeat=len(keys))]


SYNTHETIC = [(1, 1, 1, 1), (4, 4, 4, 4), (0, 3, 2, 5), (5, 2, 0, 1), (3, 5, 4, 0), (2, 2, 5, 3)]


def synthetic(member):
    k = N.needs_keys(member)
    seen, out = set(), []
    for v in SYNTHETIC:
        d = dict(zip(k, v[:len(k)] if len(k) == 4 else (v[0], v[2])))
        if js(d) not in seen:
            seen.add(js(d))
            out.append(d)
    return out


class FakeT:
    """A synthetic table for family_predict.observation: every Z 0, every latency 1/2 unit, no slot latencies. The
    observation's dates (firstTrain, teach, firstTest) depend on none of them."""

    def __getitem__(self, key):
        return dict(Z=0, latency=0.5, slot_latencies=None)


def observe(member, ports, needs):
    L1 = N.layer1(member)
    Q1 = max(needs[c] for c in L1) + 2                      # family_predict.budget_and_tuple
    Q2 = max(needs[f"c{p}"] for p in range(1, len(L1) + 1)) + 2
    return fp.observation(member, ports, FakeT(), needs, Q1, Q2, P)


class F1Regression(unittest.TestCase):
    def test_plan_and_slots_equal_plans4(self):
        n = 0
        for needs in [(1, 1, 1, 1), (4, 4, 4, 4), (2, 5, 3, 1), (7, 0, 6, 2), (3, 3, 7, 7), (0, 0, 0, 0), (5, 1, 2, 6)]:
            for control in CONTROLS:
                self.assertEqual(js(N.network("F1", needs, {}, control)), js(plans4.network(needs, control)), (needs, control))
                self.assertEqual(js(N.calendar("F1", needs, control)), js(dnf.calendar(*needs, control)))
                n += 1
        self.assertEqual(n, 21)

    def test_generic_hypotheses_equal_dnf_on_f1(self):
        for needs in [(1, 1, 1, 1), (4, 4, 4, 4), (2, 5, 3, 1)]:
            for control in CONTROLS:
                s = dnf.calendar(*needs, control)
                self.assertEqual(sorted(N.pulses("F1", {}, s)), sorted(dnf.pulses(s)))
                self.assertEqual(N.separation("F1", {}, s), dnf.separation(s))
                self.assertEqual(N.settled("F1", {}, s), dnf.settled(s)[:2])


class Binding(unittest.TestCase):
    """The calendar's slots are the observation's rows: the same dates, in the same order, the same inputs."""

    def check(self, member, ports, needs):
        obs = observe(member, ports, needs)
        slots = N.calendar(member, needs, None)
        L1 = N.layer1(member)
        inputs = fp.MEMBERS[member]["inputs"]
        rows = [("layer 1", r) for r in obs["firstTrain"]] + [("layer 2", r) for r in obs["teach"]]
        rows += [("test", obs["firstTest"][k]) for k in obs["firstTest"]]
        self.assertEqual(len(rows), len(slots), (member, ports, needs))
        keys = list(obs["firstTest"])
        self.assertEqual(keys, ["".join(sorted(x)) or "-" for x in fp.patterns(inputs)])
        tests = [s for s in slots if s["stage"] == "test"]
        self.assertEqual([s["pattern"] for s in tests], keys)
        for (stage, row), s in zip(rows, slots):
            self.assertEqual(s["stage"], stage)
            self.assertEqual(len(row), len(L1))
            starts = {F(r["start"]) for r in row}
            self.assertEqual(starts, {F(s["date"])}, (member, stage, s["date"]))
            w = fp.wiring(member, ports)
            union = set()
            for c, r in zip(L1, row):                  # the observation's rows are in L1 order
                active = {n for n, a in zip(inputs, r["arrivals"]) if a is not None}
                union |= active
                self.assertEqual(active & set(w[c]), set(s["inputs"]) & set(w[c]), (member, stage, c))
                if stage == "layer 1":                 # a layer-1 row lists the cell's own term
                    self.assertEqual(active, set(fp.MEMBERS[member]["terms"][c]))
                else:                                  # other rows list the slot's stimulus on every cell
                    self.assertEqual(active, set(s["inputs"]))
                self.assertTrue(all(F(a) == F(s["date"]) + s["inputs"][n] for n, a in zip(inputs, r["arrivals"]) if a is not None))
            self.assertEqual(union, set(s["inputs"]))
            self.assertEqual(s["writes"], {"layer 1": L1, "layer 2": ("c",), "test": ()}[stage])
            self.assertEqual(s["routed"], stage != "layer 1")
        lessons = [s for s in slots if s["stage"] == "layer 2"]
        self.assertEqual([s["line"] for s in lessons], [L1[a] for a in range(len(L1))] * (len(lessons) // len(L1)))
        for s in lessons:
            self.assertEqual(set(s["inputs"]), set(fp.MEMBERS[member]["terms"][s["line"]]))
        return len(slots)

    def test_each_member(self):
        count = {}
        for member in STEP1 + ("F1",):
            for ports in port_choices(member):
                for needs in synthetic(member):
                    self.check(member, ports, needs)
                    count[member] = count.get(member, 0) + 1
        self.assertEqual(set(count), set(STEP1) | {"F1"})

    def test_controls_extend_the_run(self):
        for member in STEP1:
            for ports in port_choices(member):
                needs = synthetic(member)[2]
                base = N.calendar(member, needs, None)
                skew = N.calendar(member, needs, "skew")
                self.assertEqual(js(skew[:len(base)]), js(base))
                extra = skew[len(base):]
                pairs = [c for c, k in fp.kinds(member).items() if k == "pair"]
                self.assertEqual(len(extra), len(pairs))
                for s, c in zip(extra, pairs):
                    a, b = fp.MEMBERS[member]["terms"][c]
                    self.assertEqual(s["inputs"], {a: 0, b: 2})
                    self.assertEqual(s["writes"], ())
                un = N.calendar(member, needs, "untrained")
                self.assertEqual([s["stage"] for s in un], ["test"] * 2 ** len(fp.MEMBERS[member]["inputs"]))
                self.assertEqual([s["date"] for s in un], [dnf.SLOT * i for i in range(len(un))])
                self.assertEqual([s["date"] for s in skew], [dnf.SLOT * i for i in range(len(skew))])


class Wiring(unittest.TestCase):
    def test_sources_at_their_ports_and_amplitudes(self):
        for member in STEP1 + ("F1",):
            for ports in port_choices(member):
                for control in CONTROLS:
                    needs = synthetic(member)[2]
                    plan, slots = N.network(member, needs, ports, control)
                    w = fp.wiring(member, ports)
                    kd = fp.kinds(member)
                    want = []
                    for s in slots:
                        for n, off in s["inputs"].items():
                            for c in N.layer1(member):
                                if n in w[c]:
                                    want.append((s["date"] + off, c, w[c][n], c4.AMP_AND if kd[c] == "pair" else c4.AMP_OR))
                    self.assertEqual(sorted(plan["sources"]), sorted(want))
                    for date, c, p, amp in plan["sources"]:
                        self.assertIn(p, w[c].values())
                        self.assertEqual(amp, 0.49 if kd[c] == "pair" else 1.0)
                    for c, k in kd.items():
                        if k == "unary":
                            other = 3 - ports[c]
                            self.assertFalse([x for x in plan["sources"] if x[1] == c and x[2] == other], (member, c))
                    if len(kd) == 1:                              # X1, X2: no b
                        self.assertFalse([x for x in plan["sources"] if x[1] == "b"])
                        self.assertFalse([e for e in plan["edges"] if e["source"] == "b" or e["port"] == 2])
                    for e in plan["edges"]:
                        self.assertEqual((e["cell"], e["port"], e["delay"], e["amp"]), ("c", fp.LINE_PORT[e["source"]], c4.WIRE, c4.AMP_OR))
                        self.assertAlmostEqual(e["gate"][1] - e["gate"][0], c4.WINDOW)
                    for (g, gs), s in zip(plan["gates"], slots):
                        self.assertEqual(g, s["date"] - c4.GATE_LEAD)
                        self.assertEqual(gs, plans4.gates(s["writes"]))
                    self.assertEqual(plan["horizon"], slots[-1]["date"] + dnf.SLOT + dnf.SETTLE)

    def test_f2_fan_out(self):
        plan, slots = N.network("F2", (2, 3, 1, 2), {}, None)
        a_dates = {s["date"] for s in slots if "A" in s["inputs"]}
        self.assertTrue(a_dates)
        for d in a_dates:
            here = {(c, p) for t, c, p, _ in plan["sources"] if t == d}
            self.assertLessEqual({("a", 1), ("b", 1)}, here)
        layer1 = [s for s in slots if s["stage"] == "layer 1"]
        for s in layer1:
            self.assertEqual(sorted((c, p) for t, c, p, _ in plan["sources"] if t == s["date"]), [("a", 1), ("a", 2), ("b", 1), ("b", 2)])

    def test_edges_one_per_cell_with_an_input(self):
        for member in STEP1:
            for ports in port_choices(member):
                plan, slots = N.network(member, synthetic(member)[1], ports, "skew")
                w = fp.wiring(member, ports)
                want = sorted((s["date"], c) for s in slots if s["routed"] for c in N.layer1(member) if set(s["inputs"]) & set(w[c]))
                got = sorted((int(e["name"].split("@")[1]), e["source"]) for e in plan["edges"])
                self.assertEqual(got, want)


class PublishedPorts(unittest.TestCase):
    PRED = HERE.parent.parent / "function-family" / "topup-verdict" / "PREDICTIONS.json"

    def test_every_published_row_is_accepted(self):
        n = 0
        for seed in range(8301, 8311):
            for member in STEP1:
                ports = N.published_ports(self.PRED, seed, member)
                self.assertEqual(sorted(ports), sorted(unary_cells(member)))
                N.network(member, synthetic(member)[0], ports, "skew")
                n += 1
        self.assertEqual(n, 50)
        self.assertEqual(N.published_ports(self.PRED, 8305, "F4"), {"a": 2, "b": 1})
        with self.assertRaisesRegex(AssertionError, "published 0 times"):
            N.published_ports(self.PRED, 8311, "X1")


class Hypotheses(unittest.TestCase):
    """H generalised: per cell, pulse groups at least SEPARATION apart; every slot settles before the next gates."""

    def test_each_member_up_to_5(self):
        n = 0
        for member in STEP1 + ("F1",):
            for ports in port_choices(member):
                for needs in needs_grid(member, 5):
                    for control in CONTROLS:
                        slots = N.calendar(member, needs, control)
                        sep = N.separation(member, ports, slots)
                        self.assertTrue(all(v >= dnf.SEPARATION for v in sep.values()), (member, ports, needs, control, sep))
                        ok, per_slot = N.settled(member, ports, slots)
                        self.assertTrue(ok, (member, needs, control, per_slot))
                        n += 1
        self.assertGreater(n, 4000)


class Refusals(unittest.TestCase):
    def test_unknown_member(self):
        with self.assertRaisesRegex(AssertionError, "not a member"):
            N.calendar("F9", (1, 1), None)
        with self.assertRaisesRegex(AssertionError, "not a member"):
            N.network("x1", (1, 1), {"a": 1}, None)

    def test_unary_ports(self):
        for bad in (0, 3, -1, "1", 1.0, True):
            with self.assertRaisesRegex(AssertionError, "1 or 2"):
                N.network("X1", (1, 1), {"a": bad}, None)
        with self.assertRaisesRegex(AssertionError, "has no unary cell; no unary port"):
            N.network("F1", (1, 1, 1, 1), {"a": 1}, None)
        with self.assertRaisesRegex(AssertionError, "has no unary cell; no unary port"):
            N.network("X2", (1, 1), {"a": 2}, None)
        with self.assertRaisesRegex(AssertionError, "no unary cell 'b'"):
            N.network("F3", (1, 1, 1, 1), {"a": 1, "b": 1}, None)
        with self.assertRaisesRegex(AssertionError, "no unary port for"):
            N.network("F4", (1, 1, 1, 1), {"a": 1}, None)

    def test_needs(self):
        with self.assertRaisesRegex(AssertionError, "above 7"):
            N.calendar("F1", (1, 8, 1, 1), None)
        with self.assertRaisesRegex(AssertionError, "above 7"):
            N.network("X1", (1, 9), {"a": 1}, None)
        with self.assertRaisesRegex(AssertionError, "above 7"):
            N.calendar("F2", (1, 1, -1, 1), None)
        with self.assertRaisesRegex(AssertionError, "has 2 needs"):
            N.calendar("X2", (1, 1, 1, 1), None)
        with self.assertRaisesRegex(AssertionError, "not an integer"):
            N.calendar("F4", (1, 1, 1.0, 1), None)
        self.assertEqual(len(N.calendar("F1", (7, 7, 7, 7), None)), 10 + 20 + 16)

    def test_control(self):
        with self.assertRaisesRegex(AssertionError, "control"):
            N.calendar("F1", (1, 1, 1, 1), "none")

    def test_python_O(self):
        env = dict(os.environ, PYTHONPATH=os.pathsep.join([str(HERE), os.environ.get("PYTHONPATH", "")]))
        code = f"import family_net as N; N.paths({REPO!r}); N.calendar('F1', (1, 1, 1, 1), None)"
        for flags in (["-O"], ["-OO"]):
            r = subprocess.run([sys.executable, "-B", *flags, "-c", code], env=env, capture_output=True, text=True)
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("refused: not with python -O", r.stderr)
        r = subprocess.run([sys.executable, "-B", "-c", code], env=env, capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        r = subprocess.run([sys.executable, "-B", "-c", code], env=dict(env, PYTHONOPTIMIZE="1"), capture_output=True, text=True)
        self.assertIn("refused: not with python -O", r.stderr)


NET6_KEYS = ("id", "kind", "section", "seed", "stage", "needs", "control", "round", "slots", "noise", "reached_its_last_date", "horizon_s",
             "waveform_ends_s", "points", "files", "noise_fingerprint", "wall_s", "peak_rss_MB")     # net6.network's, `campaign6` aside


class Runner(unittest.TestCase):
    """network_run with session4.play replaced by a fake (no ngspice): the plan and the deck it would play, the
    record's keys, and the refusals before anything is written."""

    def fake(self, seen):
        import run4
        import session4

        class Tr:
            t = [1.0]

        def play(out, plan, text, ngspice, pdk, seed=None, guard_off=False, noise_id=None, shim=None):
            seen.update(plan=plan, text=text, seed=seed, noise_id=noise_id, guard_off=guard_off)
            out = Path(out)
            out.mkdir(parents=True, exist_ok=True)
            for x in ("input.spice", "session.log", "trace.raw", "result.json"):
                (out / x).write_text(x)
            (out / "pdk").symlink_to(out)
            return dict(horizon_s=0.5, waveform_ends_s=1.0, points=3), Tr()
        return [(session4, "play", play), (run4, "trnoise_fingerprint", lambda tr, cells: "fake")]

    def run_fake(self, out, *args):
        seen = {}
        saved = []
        for mod, name, f in self.fake(seen):
            saved.append((mod, name, getattr(mod, name)))
            setattr(mod, name, f)
        try:
            rec = N.network_run(REPO, out, *args)
        finally:
            for mod, name, f in saved:
                setattr(mod, name, f)
        return rec, seen

    def test_record_plan_and_2x_deck(self):
        import batch2x
        import dosedev2
        import dosedev_tol
        import net
        with tempfile.TemporaryDirectory() as d:
            for member, ports, needs in (("F3", {"a": 2}, [3, 2, 4, 1]), ("X1", {"a": 1}, [2, 3]), ("F1", {}, [4, 4, 4, 4])):
                out = Path(d) / member
                rec, seen = self.run_fake(out, "rid", "8305", member, ports, needs, "skew", "none", 0, "/usr/bin/ngspice", "/nonexistent-pdk")
                self.assertEqual(js(seen["plan"]), js(N.network(member, needs, ports, "skew")[0]))
                with dosedev_tol.tolerance(), dosedev2.window(batch2x.PARAMS):
                    self.assertEqual(seen["text"], net.deck(cells=c4.CELLS, section=c4.SECTION))
                self.assertNotEqual(seen["text"], net.deck(cells=c4.CELLS, section=c4.SECTION))
                self.assertEqual(seen["seed"], 8305)
                self.assertEqual(tuple(rec)[:len(NET6_KEYS)], NET6_KEYS)
                self.assertEqual(tuple(rec)[len(NET6_KEYS):], ("member", "wiring", "unary_ports", "dosedev"))
                self.assertEqual(rec["member"], member)
                self.assertEqual(rec["wiring"], fp.wiring(member, ports))
                self.assertEqual(rec["unary_ports"], ports)
                self.assertEqual(rec["section"], c4.SECTION)
                self.assertEqual(json.loads((out / "record.json").read_text())["member"], member)
                self.assertFalse((out / "evidence" / "pdk").exists())
                if member == "F1":
                    self.assertEqual(js(seen["plan"]), js(plans4.network(tuple(needs), "skew")[0]))

    def test_refusals_before_anything_is_written(self):
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "r"
            for seed, member, ports, needs, err in (("7701", "F1", {}, [1, 1, 1, 1], "not one of this batch"),
                                                    ("none", "F1", {}, [1, 1, 1, 1], "nominal cell"),
                                                    ("8301", "F7", {}, [1, 1], "not a member"),
                                                    ("8301", "X1", {"a": 3}, [1, 1], "1 or 2"),
                                                    ("8301", "F2", {}, [1, 8, 1, 1], "above 7")):
                with self.assertRaisesRegex(AssertionError, err):
                    self.run_fake(out, "rid", seed, member, ports, needs, None, "none", 0, "/usr/bin/ngspice", "/x")
                self.assertFalse(out.exists())
            with self.assertRaisesRegex(AssertionError, "a noisy run has a round"):
                self.run_fake(out, "rid", "8301", "F1", {}, [1, 1, 1, 1], None, "none", 1, "/usr/bin/ngspice", "/x")
            with self.assertRaisesRegex(AssertionError, "injected model only"):
                self.run_fake(out, "rid", "8301", "F1", {}, [1, 1, 1, 1], None, "trnoise", 1, "/usr/bin/ngspice", "/x")
            self.assertFalse(out.exists())
        with self.assertRaisesRegex(AssertionError, "inside the repository"):
            self.run_fake(Path(REPO) / "tmp-run", "rid", "8301", "F1", {}, [1, 1, 1, 1], None, "none", 0, "/usr/bin/ngspice", "/x")
        self.assertFalse((Path(REPO) / "tmp-run").exists())


if __name__ == "__main__":
    unittest.main(verbosity=2)
