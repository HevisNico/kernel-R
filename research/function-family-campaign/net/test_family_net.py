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
HEAD = dict(stage=dict(name="test", protocol_sha256=None))


class Fake:
    """session4.play and run4.trnoise_fingerprint replaced for the time of a call (no ngspice). `seen` gets what the
    runner would have played and fingerprinted."""

    def __init__(self):
        self.seen = {}

    def __enter__(self):
        import run4
        import session4
        seen = self.seen

        class Tr:
            t = [1.0]
        self.tr = Tr()

        def play(out, plan, text, ngspice, pdk, seed=None, guard_off=False, noise_id=None, shim=None):
            seen.update(plan=plan, text=text, seed=seed, noise_id=noise_id, guard_off=guard_off, shim_name=None if shim is None else Path(shim).name,
                        shim_exists=None if shim is None else Path(shim).exists())
            out = Path(out)
            out.mkdir(parents=True, exist_ok=True)
            for x in ("input.spice", "session.log", "trace.raw", "result.json"):
                (out / x).write_text(x)
            (out / "pdk").symlink_to(out)
            return dict(horizon_s=0.5, waveform_ends_s=1.0, points=3), self.tr

        def fingerprint(tr, cells):
            seen.update(fingerprint_tr_is_play_tr=tr is self.tr, fingerprint_cells=tuple(cells))
            return "fake"
        self.saved = [(session4, "play", session4.play), (run4, "trnoise_fingerprint", run4.trnoise_fingerprint)]
        session4.play, run4.trnoise_fingerprint = play, fingerprint
        return self

    def __exit__(self, *exc):
        for mod, name, f in self.saved:
            setattr(mod, name, f)


class Runner(unittest.TestCase):
    """play_run (the runner's body) with the fake: the plan and the deck it would play, the record's keys."""

    def test_record_plan_and_2x_deck(self):
        import batch2x
        import dosedev2
        import dosedev_tol
        import net
        with tempfile.TemporaryDirectory() as d:
            for member, ports, needs in (("F3", {"a": 2}, [3, 2, 4, 1]), ("X1", {"a": 1}, [2, 3]), ("F1", {}, [4, 4, 4, 4])):
                out = Path(d) / member
                with Fake() as f:
                    rec = N.play_run(REPO, out, "rid", 8505, member, ports, needs, "skew", None, 0, "/usr/bin/ngspice", "/nonexistent-pdk", HEAD)
                seen = f.seen
                self.assertEqual(js(seen["plan"]), js(N.network(member, needs, ports, "skew")[0]))
                with dosedev_tol.tolerance(), dosedev2.window(batch2x.PARAMS):
                    self.assertEqual(seen["text"], net.deck(cells=c4.CELLS, section=c4.SECTION))
                self.assertNotEqual(seen["text"], net.deck(cells=c4.CELLS, section=c4.SECTION))
                self.assertEqual(seen["seed"], 8505)
                self.assertEqual(tuple(rec)[:len(NET6_KEYS)], NET6_KEYS)
                self.assertEqual(tuple(rec)[len(NET6_KEYS):], ("family", "member", "wiring", "unary_ports", "dosedev"))
                self.assertEqual((rec["member"], rec["wiring"], rec["unary_ports"], rec["section"]), (member, fp.wiring(member, ports), ports, c4.SECTION))
                self.assertEqual(json.loads((out / "record.json").read_text())["member"], member)
                self.assertFalse((out / "evidence" / "pdk").exists())
                if member == "F1":
                    self.assertEqual(js(seen["plan"]), js(plans4.network(tuple(needs), "skew")[0]))

    def test_refusals_before_anything_is_written(self):
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "r"
            for member, ports, needs, ctl, nid, rnd, err in (("F7", {}, [1, 1], None, None, 0, "not a member"),
                                                             ("X1", {"a": 3}, [1, 1], None, None, 0, "1 or 2"),
                                                             ("F2", {}, [1, 8, 1, 1], None, None, 0, "above 7"),
                                                             ("F1", {}, [1, 1, 1, 1], None, None, 1, "a noisy run has a round"),
                                                             ("F1", {}, [1, 1, 1, 1], None, 85011, 0, "a noisy run has a round"),
                                                             ("F1", {}, [1, 1, 1, 1], "none", None, 0, "control")):
                with self.assertRaisesRegex(AssertionError, err), Fake():
                    N.play_run(REPO, out, "rid", 8501, member, ports, needs, ctl, nid, rnd, "/usr/bin/ngspice", "/x", HEAD)
                self.assertFalse(out.exists())
        with self.assertRaisesRegex(AssertionError, "inside the repository"), Fake():
            N.play_run(REPO, Path(REPO) / "tmp-run", "rid", 8501, "F1", {}, [1, 1, 1, 1], None, None, 0, "/usr/bin/ngspice", "/x", HEAD)
        self.assertFalse((Path(REPO) / "tmp-run").exists())


class InjectedNoise(unittest.TestCase):
    """The injected-noise path, without simulation: on F1, the runner gives session4.play and run4.trnoise_fingerprint
    exactly what net6.network gives them (plan, deck text, seed, noise seed, shim built by noisemodel.shim), with the
    same 2x window around both, and writes the same record values. net6's campaign guards (stage file, seed guard,
    header) are replaced for the time of the call, since its guard knows campaign 6's seeds only."""

    def net6_run(self, out, needs, control, rnd, seed):
        import batch2x
        import c6
        import dosedev2
        import dosedev_tol
        import net6
        saved = (c6.stage_check, c6.guard_seed, c6.run_header)
        c6.stage_check = lambda f: dict(stage="N1")
        c6.guard_seed = lambda text, stage=None, out=None: int(text)
        c6.run_header = lambda *a, **k: {}
        try:
            with Fake() as f, dosedev_tol.tolerance(), dosedev2.window(batch2x.PARAMS):
                rec = net6.network("stage-file", out, "rid", str(seed), list(needs), control, "injected" if rnd else "none", rnd,
                                   Path("/usr/bin/ngspice"), Path("/x"))
        finally:
            c6.stage_check, c6.guard_seed, c6.run_header = saved
        return rec, f.seen

    def test_f1_equals_net6(self):
        import c6
        with tempfile.TemporaryDirectory() as d:
            for needs, control, rnd in (((3, 4, 2, 5), None, 1), ((4, 4, 4, 4), None, 3), ((2, 2, 2, 2), "skew", 0)):
                seed = 8501
                r6, s6 = self.net6_run(Path(d) / f"n6-{rnd}-{control}", needs, control, rnd, seed)
                nid = N.noise_seed(seed, "F1", rnd, "N1") if rnd else None
                self.assertEqual(nid, c6.noise_seed(seed, rnd) if rnd else None)
                with Fake() as f:
                    rf = N.play_run(REPO, Path(d) / f"fam-{rnd}-{control}", "rid", seed, "F1", {}, needs, control, nid, rnd, "/usr/bin/ngspice", "/x", HEAD)
                sf = f.seen
                self.assertEqual(js(sf["plan"]), js(s6["plan"]))
                self.assertEqual(sf["text"], s6["text"])
                for k in ("seed", "noise_id", "guard_off", "shim_name", "shim_exists", "fingerprint_tr_is_play_tr", "fingerprint_cells"):
                    self.assertEqual(sf[k], s6[k], k)
                self.assertEqual(sf["fingerprint_cells"], tuple(c4.CELLS))
                if rnd:
                    self.assertTrue(sf["shim_exists"])
                for k in NET6_KEYS:
                    if k not in ("wall_s", "peak_rss_MB", "stage"):
                        self.assertEqual(js(rf[k]), js(r6[k]), k)
                self.assertFalse(list((Path(d) / f"fam-{rnd}-{control}").glob("fakepid.so")))

    def test_noisy_deck_differs_from_quiet(self):
        with tempfile.TemporaryDirectory() as d:
            with Fake() as q:
                N.play_run(REPO, Path(d) / "q", "rid", 8501, "F1", {}, (2, 2, 2, 2), None, None, 0, "/usr/bin/ngspice", "/x", HEAD)
            with Fake() as n:
                N.play_run(REPO, Path(d) / "n", "rid", 8501, "F1", {}, (2, 2, 2, 2), None, 85011, 1, "/usr/bin/ngspice", "/x", HEAD)
        self.assertNotEqual(q.seen["text"], n.seen["text"])
        self.assertEqual(n.seen["noise_id"], 85011)
        self.assertIsNone(q.seen["noise_id"])


class SeedsAndNoise(unittest.TestCase):
    def test_seed_guard(self):
        for s in range(8501, 8516):
            for st in ("Q", "N1", "N2", "N3"):
                self.assertEqual(N.guard_seed(str(s), st), s)
            with self.assertRaisesRegex(AssertionError, "8303 and 8306 only"):
                N.guard_seed(str(s), "rehearsal")
        for s in (8303, 8306):
            self.assertEqual(N.guard_seed(str(s), "rehearsal"), s)
            for st in ("Q", "N1", "N2", "N3"):
                with self.assertRaisesRegex(AssertionError, "8501 to 8515 only"):
                    N.guard_seed(str(s), st)
        for bad in ("8500", "8516", "8301", "8305", "7701", "7601", "08501"):
            for st in N.STAGES:
                with self.assertRaises(AssertionError):
                    N.guard_seed(bad, st)
        with self.assertRaisesRegex(AssertionError, "nominal cell"):
            N.guard_seed("none", "Q")
        with self.assertRaisesRegex(AssertionError, "stage"):
            N.guard_seed("8501", "N4")
        with self.assertRaisesRegex(AssertionError, "stage"):
            N.guard_seed("8501", "D")

    def test_campaign_noise_seeds(self):
        got = {N.noise_seed(s, "X1", n, f"N{n}") for s in range(8501, 8516) for n in (1, 2, 3)}
        self.assertEqual(min(got), 85011)
        self.assertEqual(max(got), 85153)
        self.assertEqual(len(got), 45)
        for n in (0, 4, -1):
            with self.assertRaisesRegex(AssertionError, "n from 1 to 3"):
                N.noise_seed(8501, "X1", n, "N1")

    def test_rehearsal_table_exactly(self):
        want = {(8303, "F2", 1): 83031, (8303, "F2", 2): 83032, (8303, "F2", 3): 83033, (8303, "F2", 4): 83034,
                (8303, "X1", 5): 83035, (8303, "X2", 6): 83036,
                (8306, "F2", 1): 83061, (8306, "F2", 2): 83062, (8306, "F2", 3): 83063, (8306, "F2", 4): 83064,
                (8306, "F4", 5): 83065, (8306, "F3", 6): 83066}
        self.assertEqual(N.REHEARSAL_NOISE, want)
        for s in (8303, 8306):
            for m in fp.MEMBERS:
                for n in range(0, 9):
                    if (s, m, n) in want:
                        self.assertEqual(N.noise_seed(s, m, n, "rehearsal"), want[(s, m, n)])
                    else:
                        with self.assertRaisesRegex(AssertionError, "no rehearsal noise seed"):
                            N.noise_seed(s, m, n, "rehearsal")

    def test_stage_and_kind(self):
        self.assertEqual(N.run_of("Q", "quiet", 0), ("skew", "none"))
        self.assertEqual(N.run_of("Q", "untrained", 0), ("untrained", "none"))
        for n in (1, 2, 3):
            self.assertEqual(N.run_of(f"N{n}", "noisy", n), (None, "injected"))
            for m in (1, 2, 3):
                if m != n:
                    with self.assertRaisesRegex(AssertionError, "does not belong to stage"):
                        N.run_of(f"N{n}", "noisy", m)
            for k in ("quiet", "untrained"):
                with self.assertRaisesRegex(AssertionError, "belongs to stage Q"):
                    N.run_of(f"N{n}", k, 0)
        with self.assertRaisesRegex(AssertionError, "does not belong to stage Q"):
            N.run_of("Q", "noisy", 1)
        with self.assertRaisesRegex(AssertionError, "round 0"):
            N.run_of("Q", "quiet", 1)
        with self.assertRaisesRegex(AssertionError, "kind"):
            N.run_of("Q", "skew", 0)
        self.assertEqual(N.run_of("rehearsal", "noisy", 5), (None, "injected"))

    def test_pushed_files(self):
        self.assertEqual(N.protocol_check(), N.PROTOCOL_SHA256)
        d = N.draw()
        self.assertEqual(sorted(d), list(range(8501, 8516)))
        self.assertEqual({m: sorted(s for s, x in d.items() if x == m) for m in STEP1},
                         dict(X1=[8501, 8504, 8512], X2=[8502, 8508, 8513], F4=[8505, 8507, 8514], F2=[8506, 8510, 8515], F3=[8503, 8509, 8511]))


def row(seed, member, measured=True, K0=True, K3=True, needs=None, ports=None, **extra):
    """A synthetic row in family_predict.py's output shape (the per-member fields of topup-verdict/PREDICTIONS.json)."""
    keys = N.needs_keys(member)
    needs = needs or dict(zip(keys, (2, 3, 1, 2)[:len(keys)] if len(keys) == 4 else (2, 1)))
    ports = {c: 1 for c in unary_cells(member)} if ports is None else ports
    L1 = N.layer1(member)
    x = dict(member=member, seed=seed, measured=measured, needs=needs, unary_ports=ports,
             Q1=max(needs[c] for c in L1) + 2, Q2=max(needs[k] for k in keys[len(L1):]) + 2, why_not_measured=[] if measured else ["synthetic"])
    if measured:
        x.update(gate=dict(kernel=dict(K0=K0, K3=K3), kernel_agrees_with_mirror=True), gate_K0=K0, room_K3=K3)
    else:
        x.update(room_K3=False)
    x.update(extra)
    return x


def record(rows, path):
    """rows: row dicts, filed under their own seed and member, or (seed, member, row) triples, filed as given."""
    by = {}
    for x in rows:
        s, m, x = x if isinstance(x, tuple) else (x["seed"], x["member"], x)
        by.setdefault(s, {})[m] = x
    Path(path).write_text(json.dumps(dict(summary={}, instances=[dict(seed=s, unary=None, members=m) for s, m in sorted(by.items())]), indent=1))
    return path


class Stages(unittest.TestCase):
    """The stage checks on a synthetic PREDICTED.json: X1 on 8501 not eligible, 8504 eligible without room, 8512
    eligible with room; F4 on 8505 eligible with room; F2 on 8506 not measured; every other seed eligible with room."""

    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.TemporaryDirectory()
        D = N.draw()
        rows = []
        for s, m in sorted(D.items()):
            if s == 8501:
                rows.append(row(s, m, K0=False, K3=False))
            elif s == 8504:
                rows.append(row(s, m, K3=False))
            elif s == 8506:
                rows.append(row(s, m, measured=False))
            else:
                rows.append(row(s, m, ports={"a": 2, "b": 1} if m == "F4" else None))
        cls.path = record(rows, Path(cls.dir.name) / "PREDICTED.json")
        cls.pred = N.read_predicted(cls.path)

    @classmethod
    def tearDownClass(cls):
        cls.dir.cleanup()

    def ok(self, stage, kind, rnd, seed, member):
        return N.admit(stage, kind, rnd, seed, member, self.pred)

    def no(self, msg, stage, kind, rnd, seed, member, pred=None):
        with self.assertRaisesRegex(AssertionError, msg):
            N.admit(stage, kind, rnd, seed, member, pred or self.pred)

    def test_eligibility(self):
        self.no("not eligible", "Q", "quiet", 0, 8501, "X1")
        self.no("not eligible", "N1", "noisy", 1, 8501, "X1")
        self.no("not eligible", "Q", "quiet", 0, 8506, "F2")
        a = self.ok("Q", "quiet", 0, 8504, "X1")
        self.assertEqual((a["control"], a["noise"], a["noise_id"], a["round"]), ("skew", "none", None, None))
        self.assertEqual(a["needs"], dict(a=2, c1=1))
        self.assertEqual(a["unary_ports"], {"a": 1})

    def test_room(self):
        for n in (1, 2, 3):
            self.no("no room", f"N{n}", "noisy", n, 8504, "X1")
            a = self.ok(f"N{n}", "noisy", n, 8512, "X1")
            self.assertEqual((a["control"], a["noise"], a["noise_id"], a["round"]), (None, "injected", 85120 + n, n))
        a = self.ok("N2", "noisy", 2, 8505, "F4")
        self.assertEqual(a["unary_ports"], {"a": 2, "b": 1})

    def test_untrained_on_the_first_eligible_only(self):
        self.no("first eligible instance, 8504, not 8512", "Q", "untrained", 0, 8512, "X1")    # 8501 not eligible: 8504 is first
        a = self.ok("Q", "untrained", 0, 8504, "X1")
        self.assertEqual(a["control"], "untrained")
        self.ok("Q", "untrained", 0, 8505, "F4")
        self.no("first eligible instance, 8505, not 8507", "Q", "untrained", 0, 8507, "F4")
        self.no("first eligible instance, 8510, not 8515", "Q", "untrained", 0, 8515, "F2")    # 8506 not measured
        self.ok("Q", "untrained", 0, 8510, "F2")

    def test_untrained_needs_every_earlier_row(self):
        D = N.draw()
        rows = [row(s, m) for s, m in sorted(D.items()) if s != 8501]
        with tempfile.TemporaryDirectory() as d:
            pred = N.read_predicted(record(rows, Path(d) / "P.json"))
        self.no("first eligible instance is undecided", "Q", "untrained", 0, 8504, "X1", pred)
        self.no("no row for X1 of 8501", "Q", "quiet", 0, 8501, "X1", pred)

    def test_member_must_be_the_drawn_one(self):
        self.no("drawn for X1, not F4", "Q", "quiet", 0, 8504, "F4")
        self.no("drawn for X2, not F1", "Q", "quiet", 0, 8502, "F1")

    def test_stage_mismatch(self):
        self.no("belongs to stage Q", "N1", "quiet", 0, 8512, "X1")
        self.no("does not belong to stage Q", "Q", "noisy", 1, 8512, "X1")
        self.no("round 2 does not belong to stage N1", "N1", "noisy", 2, 8512, "X1")

    def test_bad_rows(self):
        D = N.draw()
        for bad, msg in ((dict(room_K3=False), "room_K3 disagrees"), (dict(gate_K0=False), "gate_K0 disagrees"),
                         (dict(Q1=9), "Q1 is not max"), (dict(needs=dict(a=8, c1=1)), "above 7"), (dict(unary_ports={"a": 3}), "1 or 2"),
                         (dict(unary_ports={}), "no unary port"), (dict(member="X2"), "names another member")):
            rows = [(s, m, {**row(s, m), **(bad if s == 8512 else {})}) for s, m in sorted(D.items())]
            with tempfile.TemporaryDirectory() as d:
                pred = N.read_predicted(record(rows, Path(d) / "P.json"))
            self.no(msg, "N1", "noisy", 1, 8512, "X1", pred)
        rows = [row(8512, "X1", eligible_needs=False)]
        with tempfile.TemporaryDirectory() as d:
            pred = N.read_predicted(record(rows, Path(d) / "P.json"))
        self.no("not eligible", "Q", "quiet", 0, 8512, "X1", pred)
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "P.json"
            p.write_text(json.dumps(dict(instances=[dict(seed=8512, members={}), dict(seed=8512, members={})])))
            with self.assertRaisesRegex(AssertionError, "listed twice"):
                N.read_predicted(p)

    def test_network_run_end_to_end_with_the_fake(self):
        with tempfile.TemporaryDirectory() as d:
            with Fake() as f:
                rec = N.network_run(REPO, Path(d) / "a", "8512-N2", "8512", "X1", "N2", "noisy", 2, self.path, "/usr/bin/ngspice", "/x")
            self.assertEqual(f.seen["noise_id"], 85122)
            self.assertEqual(rec["noise"]["noise_seed"], 85122)
            self.assertEqual(rec["stage"]["name"], "N2")
            self.assertEqual(rec["stage"]["predicted_sha256"], N.sha256_file(self.path))
            self.assertEqual(rec["stage"]["protocol_sha256"], N.PROTOCOL_SHA256)
            self.assertEqual(rec["needs"], [2, 1])
            self.assertEqual(js(f.seen["plan"]), js(N.network("X1", dict(a=2, c1=1), {"a": 1}, None)[0]))
            with Fake() as f:
                rec = N.network_run(REPO, Path(d) / "b", "8505-Q", "8505", "F4", "Q", "quiet", 0, self.path, "/usr/bin/ngspice", "/x")
            self.assertEqual((rec["control"], rec["noise"], rec["unary_ports"]), ("skew", dict(model="none"), {"a": 2, "b": 1}))
            for args, msg in ((("8504", "X1", "N1", "noisy", 1), "no room"), (("8501", "X1", "Q", "quiet", 0), "not eligible"),
                              (("8303", "F2", "Q", "quiet", 0), "8501 to 8515 only"), (("8512", "X1", "rehearsal", "quiet", 0), "8303 and 8306 only"),
                              (("8512", "X1", "Q", "untrained", 0), "first eligible")):
                out = Path(d) / "r"
                with self.assertRaisesRegex(AssertionError, msg), Fake():
                    N.network_run(REPO, out, "rid", *args, self.path, "/usr/bin/ngspice", "/x")
                self.assertFalse(out.exists())


class Rehearsal(unittest.TestCase):
    """R-N on 8303 and 8306, against the published top-up verdict (topup-verdict/PREDICTIONS.json, the same shape as
    PREDICTED.json): every member is eligible with room there [TV], so every run of section 7's list is admitted."""
    PRED = HERE.parent.parent / "function-family" / "topup-verdict" / "PREDICTIONS.json"

    def test_every_listed_run_is_admitted(self):
        pred = N.read_predicted(self.PRED)
        n = 0
        for s in (8303, 8306):
            for m in STEP1:
                for kind in ("quiet", "untrained"):
                    a = N.admit("rehearsal", kind, 0, s, m, pred)
                    self.assertEqual(a["needs"], N.check_needs(m, pred[s][m]["needs"]))
                    self.assertEqual(a["unary_ports"], pred[s][m]["unary_ports"])
                    n += 1
        for (s, m, r), nid in N.REHEARSAL_NOISE.items():
            a = N.admit("rehearsal", "noisy", r, s, m, pred)
            self.assertEqual((a["noise_id"], a["control"], a["noise"]), (nid, None, "injected"))
            n += 1
        self.assertEqual(n, 32)
        with self.assertRaisesRegex(AssertionError, "no rehearsal noise seed"):
            N.admit("rehearsal", "noisy", 1, 8303, "X1", pred)
        with self.assertRaisesRegex(AssertionError, "8303 and 8306 only"):
            N.guard_seed("8301", "rehearsal")


if __name__ == "__main__":
    unittest.main(verbosity=2)
