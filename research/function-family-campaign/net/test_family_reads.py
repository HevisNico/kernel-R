"""Tests of family_reads.py. No simulation: every trace is a synthetic ngspice binary raw file, written here and parsed
by the frozen measure.Trace; every result.json is written here from family_net's plan.

  test_family_reads.py REPO        REPO: research/learned-dnf-circuit-campaign-6-impl at ecfcd1c1
"""
import itertools
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

REPO = sys.argv.pop(1) if len(sys.argv) > 1 and not sys.argv[1].startswith("-") else os.environ.get("REPO")
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import family_net as N                                     # noqa: E402

N.paths(REPO)
import family_reads as R                                   # noqa: E402
import family_predict as fp                                # noqa: E402
import c4                                                  # noqa: E402
import net                                                 # noqa: E402
import numpy as np                                         # noqa: E402
import plans4                                              # noqa: E402
import reads4                                              # noqa: E402
from c4 import dnf                                         # noqa: E402

STEP1 = ("X1", "X2", "F4", "F2", "F3")
TU = 20e-6
at = reads4.c4_at


def port_choices(member):
    u = [c for c, k in fp.kinds(member).items() if k == "unary"]
    return [dict(zip(u, ps)) for ps in itertools.product((1, 2), repeat=len(u))]


def truth(member, x):
    """{cell: output} of a trained network on pattern x: a layer-1 cell fires on its term; c is the OR of its lines."""
    terms = fp.MEMBERS[member]["terms"]
    out = {c: set(t) <= set(x) for c, t in terms.items()}
    out["c"] = any(out.values())
    return out


def behaviour(member, needs, ports, control):
    """The zero-error run (dnf.zero_error generalised): per slot, per cell that reads, (fire, {port: writes})."""
    plan, slots = N.network(member, needs, ports, control)
    w = fp.wiring(member, ports)
    terms = fp.MEMBERS[member]["terms"]
    L1 = N.layer1(member)
    done = {c: 0 for c in L1}
    lines = {p: 0 for p in (1, 2)}
    trained = control != "untrained"
    out = []
    for s in slots:
        x = set(s["inputs"])
        b = {}
        fired = []
        for c in L1:
            got = x & set(w[c])
            if not got:
                continue
            if s["stage"] == "layer 1":
                f = done[c] >= needs[c]
                b[c] = (f, {} if f else {p: 1 for p in w[c].values()})
                done[c] += 0 if f else 1
            elif s["stage"] == "skew control":
                b[c] = (False, {})
            else:
                f = trained and set(terms[c]) <= x
                b[c] = (f, {})
            if b[c][0] and s["routed"]:
                fired.append(c)
        if fired:
            if s["stage"] == "layer 2":
                p = fp.LINE_PORT[s["line"]]
                f = lines[p] >= needs[f"c{p}"]
                b["c"] = (f, {} if f else {p: 1})
                lines[p] += 0 if f else 1
            else:
                b["c"] = (trained, {})
        out.append(b)
    return plan, slots, out


def expected_words(member, needs, ports):
    L1 = N.layer1(member)
    r1 = max(needs[c] for c in L1) + dnf.EXTRA
    r2 = max(needs[f"c{fp.LINE_PORT[c]}"] for c in L1) + dnf.EXTRA
    w = {}
    for c, k in fp.kinds(member).items():
        for p in ((1, 2) if k == "pair" else (ports[c],)):
            w[f"{c}{p}"] = "s" * needs[c] + "F" * (r1 - needs[c])
    for c in L1:
        p = fp.LINE_PORT[c]
        w[f"c{p}"] = "s" * needs[f"c{p}"] + "F" * (r2 - needs[f"c{p}"])
    return w


SIGNALS = [f"v(x{c}.{s})" for c in "abc" for s in ("vq", "p", "x1.si", "x2.si", "vmem1", "vmem2", "x1.sum", "x2.sum")]


def synthesise(folder, member, needs, ports, control, beh=None, reached=True, noise="none", move=None, seed=8505):
    """A run folder: record.json, evidence/result.json and evidence/trace.raw, from the behaviour (or the zero-error
    one). result.json has session4.play's keys (plan, cells, seed, guard_off, origin_s, occurrences, fires, gates,
    still_queued_at_the_horizon, wall_s, points, waveform_ends_s, horizon_s). Each pulse's 0.9 V crossing falls on
    its nominal date exactly (see pulse), so that a FIRE 10 us after a read's start is 1/2 unit late.
    Occurrences are at their snapped dates, as session4 delivers them (net.snap: about 0.1 us late, 0.005 unit).
    move: (slot, cell, port, mV) steps the stored voltage during that read."""
    plan, slots, zero = behaviour(member, needs, ports, control)
    beh = zero if beh is None else beh
    horizon = at(plan["horizon"]) + 50e-6
    t = np.arange(0.0, horizon, 1e-6)
    v = {n: np.zeros_like(t) for n in SIGNALS}
    for c in "abc":
        v[f"v(x{c}.vq)"][:] = 1.2
    def pulse(name, t0, width):
        """A pulse whose 0.9 V crossing, by measure.Trace's linear interpolation, falls at t0: its first sample at or
        after t0 is 0.9 V scaled by the grid step over (t0 - the sample before); the others up to t0 + width 1.8 V."""
        i = int(np.searchsorted(t, t0 - 1e-12))
        frac = (t0 - t[i - 1]) / (t[i] - t[i - 1])
        sel = (t > t[i]) & (t <= t0 + width)
        v[name][sel] = 1.8
        v[name][i] = 0.9 / frac
        return t0
    occ, fire_events = [], []
    for date, c, p, amp in plan["sources"]:
        occ.append(dict(kind="pulse", cell=c, port=p, amp=amp, origin="source", calendar_date=date, id=len(occ), date_s=net.snap(at(date)),
                        protected_when_scheduled=False, delivered=True))
    for i, (s, b) in enumerate(zip(slots, beh)):
        lo = at(s["date"])
        fires = {}
        for c in N.layer1(member):
            if c not in b:
                continue
            mine = [o["date_s"] for o in occ if o["origin"] == "source" and o["cell"] == c and at(s["date"]) - 1e-9 <= o["date_s"] < at(s["date"] + dnf.SLOT) - 1e-9]
            start = min(mine)
            f, wr = b[c]
            if f:
                fires[c] = pulse(f"v(x{c}.p)", start + 10e-6, 3e-6)
                fire_events.append(dict(cell=c, date_s=fires[c], calendar_date=(fires[c] - at(0)) / TU, routed=[]))
            for p, n in wr.items():
                for k in range(n):
                    pulse(f"v(x{c}.x{p}.si)", start + 40e-6 + 10e-6 * k, 3e-6)
        if "c" in b or (s["routed"] and fires):
            arr = []
            for src, fd in fires.items():
                e = next(e for e in plan["edges"] if e["source"] == src and e["gate"][0] == s["date"] + min(o for n, o in s["inputs"].items() if n in fp.wiring(member, ports)[src]))
                occ.append(dict(kind="pulse", cell="c", port=e["port"], amp=e["amp"], origin=e["name"], fire_date_s=fd, id=len(occ),
                                date_s=fd + c4.WIRE * TU, protected_when_scheduled=False, delivered=True))
                next(x for x in fire_events if x["cell"] == src and x["date_s"] == fd)["routed"].append(e["name"])
                arr.append(fd + c4.WIRE * TU)
            if arr and "c" in b:
                f, wr = b["c"]
                if f:
                    fc = pulse("v(xc.p)", max(arr) + 10e-6, 3e-6)
                    fire_events.append(dict(cell="c", date_s=fc, calendar_date=(fc - at(0)) / TU, routed=[]))
                for p, n in wr.items():
                    for k in range(n):
                        pulse(f"v(xc.x{p}.si)", min(arr) + 40e-6 + 10e-6 * k, 3e-6)
        if move and move[0] == i:
            _, c, p, mv = move
            v[f"v(x{c}.vmem{p})"][t >= lo + 60e-6] += mv * 1e-3
    ev = Path(folder) / "evidence"
    ev.mkdir(parents=True, exist_ok=True)
    head = ["Title: synthetic", "Date: none", "Plotname: Transient Analysis", "Flags: real", f"No. Variables: {1 + len(SIGNALS)}",
            f"No. Points: {len(t)}", "Variables:", "\t0\ttime\ttime"] + [f"\t{i + 1}\t{n}\tvoltage" for i, n in enumerate(SIGNALS)]
    data = np.column_stack([t] + [v[n] for n in SIGNALS]).astype("<f8")
    (ev / "trace.raw").write_bytes(("\n".join(head) + "\nBinary:\n").encode() + data.tobytes())
    gates = [dict(date_s=at(d), calendar_date=d, settings=g, protected=dict(a=False, b=False, c=False)) for d, g in plan["gates"]]
    result = dict(plan=json.loads(json.dumps(plan)), cells=list(c4.CELLS), seed=seed, guard_off=False, origin_s=at(0), occurrences=occ,
                  fires=sorted(fire_events, key=lambda x: x["date_s"]), gates=gates, still_queued_at_the_horizon=[], wall_s=0.0,
                  points=int(len(t)), waveform_ends_s=float(t[-1]), horizon_s=at(plan["horizon"]))
    (ev / "result.json").write_text(json.dumps(result))
    rec = dict(id="synthetic", kind="network", seed=seed, member=member, unary_ports=ports, needs=list(N.check_needs(member, needs).values()),
               control=control, noise=dict(model=noise), reached_its_last_date=reached)
    (Path(folder) / "record.json").write_text(json.dumps(rec))
    return plan, slots, beh


NEEDS = dict(X1=dict(a=2, c1=1), X2=dict(a=3, c1=2), F4=dict(a=1, b=2, c1=2, c2=1), F2=dict(a=2, b=3, c1=1, c2=2),
             F3=dict(a=2, b=1, c1=1, c2=3), F1=dict(a=2, b=3, c1=1, c2=2))


class Base(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.d = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()


class F1Equality(Base):
    def test_f1_words_equal_reads4(self):
        needs = NEEDS["F1"]
        for control in ("skew", None):
            f = self.d / f"f1-{control}"
            synthesise(f, "F1", needs, {}, control)
            rows, _ = R.rows_of(f, "F1", needs, {}, control)
            import measure
            ref = reads4.network_reads(measure.Trace(f / "evidence" / "trace.raw"), json.loads((f / "evidence" / "result.json").read_text()),
                                       dnf.calendar(*needs.values(), control))
            self.assertEqual(R.js(rows), R.js(ref))
            self.assertEqual(R.js(R.words("F1", {}, rows)), R.js(reads4.words(rows)))
            self.assertEqual(R.js(R.words("F1", {}, rows, prime=True)), R.js(reads4.words(rows, prime=True)))
            self.assertEqual(R.js(plans4.network(tuple(needs.values()), control)[0]), json.dumps(json.loads((f / "evidence" / "result.json").read_text())["plan"], sort_keys=True))


class Members(Base):
    def test_each_member_both_ports(self):
        n = 0
        for member in STEP1 + ("F1",):
            for ports in port_choices(member):
                for control in ("skew", None):
                    f = self.d / f"{member}-{n}"
                    synthesise(f, member, NEEDS[member], ports, control)
                    x = R.record_of(f, "complete")
                    self.assertTrue(x["counts"])
                    self.assertEqual(x["words"], expected_words(member, NEEDS[member], ports), (member, ports))
                    self.assertEqual(list(x["words"]), R.ports_of(member, ports))
                    inputs = fp.MEMBERS[member]["inputs"]
                    self.assertEqual(list(x["tests"]), ["".join(sorted(p)) or "-" for p in fp.patterns(inputs)])
                    for k, v in x["tests"].items():
                        self.assertEqual(v, truth(member, set(k) - {"-"}), (member, k))
                    self.assertEqual(list(x["skew"]), R.skew_keys(member) if control == "skew" else [])
                    self.assertTrue(all(not f for v in x["skew"].values() for f in v.values()))
                    self.assertEqual(x["G"], [])
                    n += 1
        self.assertEqual(n, 2 * (2 + 1 + 4 + 1 + 2 + 1))      # X1 X2 F4 F2 F3 F1 port choices, 2 controls

    def test_unary_port_only(self):
        for ports in ({"a": 1}, {"a": 2}):
            f = self.d / f"x1-{ports['a']}"
            synthesise(f, "X1", NEEDS["X1"], ports, "skew")
            x = R.record_of(f, "complete")
            self.assertEqual(list(x["words"]), [f"a{ports['a']}", "c1"])
            self.assertEqual(set(x["tests"]["A"]), {"a", "c"})
            self.assertEqual(x["skew"], {})

    def test_untrained(self):
        for member in STEP1:
            ports = port_choices(member)[-1]
            f = self.d / f"u-{member}"
            synthesise(f, member, NEEDS[member], ports, "untrained")
            x = R.record_of(f, "complete")
            self.assertEqual(set(x["words"].values()), {""})
            self.assertTrue(all(not o for v in x["tests"].values() for o in v.values()))


class Caught(Base):
    """One wrong letter, one wrong output and a skew firing, each visible in the record."""

    def test_wrong_letter(self):
        member, ports = "F3", {"a": 2}
        needs = NEEDS[member]
        plan, slots, beh = behaviour(member, needs, ports, "skew")
        i = [k for k, s in enumerate(slots) if s["stage"] == "layer 1"][needs["a"]]        # a's first FIRE
        beh[i]["a"] = (True, {2: 1})                                                       # a FIRE with a write: w
        synthesise(self.d / "w", member, needs, ports, "skew", beh)
        x = R.record_of(self.d / "w", "complete")
        want = expected_words(member, needs, ports)
        self.assertNotEqual(x["words"], want)
        self.assertEqual(x["words"]["a2"][needs["a"]], "w")
        self.assertEqual([p for p in want if x["words"][p] != want[p]], ["a2"])

    def test_double_write_and_silence(self):
        member, ports = "F4", {"a": 1, "b": 2}
        needs = NEEDS[member]
        plan, slots, beh = behaviour(member, needs, ports, None)
        l1 = [k for k, s in enumerate(slots) if s["stage"] == "layer 1"]
        beh[l1[0]]["b"] = (False, {2: 2})                                                  # m
        beh[l1[-1]]["a"] = (False, {})                                                     # o
        synthesise(self.d / "m", member, needs, ports, None, beh)
        x = R.record_of(self.d / "m", "complete")
        self.assertEqual(x["words"]["b2"][0], "m")
        self.assertEqual(x["words"]["a1"][-1], "o")

    def test_wrong_output(self):
        member, ports = "F2", {}
        needs = NEEDS[member]
        plan, slots, beh = behaviour(member, needs, ports, "skew")
        i = next(k for k, s in enumerate(slots) if s["stage"] == "test" and s["pattern"] == "AB")
        beh[i]["c"] = (False, {})
        synthesise(self.d / "o", member, needs, ports, "skew", beh)
        x = R.record_of(self.d / "o", "complete")
        self.assertEqual(x["tests"]["AB"], dict(a=True, b=False, c=False))
        self.assertNotEqual(x["tests"]["AB"], truth(member, {"A", "B"}))
        self.assertEqual([k for k, v in x["tests"].items() if v != truth(member, set(k) - {"-"})], ["AB"])

    def test_skew_firing(self):
        for member, ports, key, cell in (("F2", {}, "AC", "b"), ("F3", {"a": 1}, "BC", "b"), ("X2", {}, "AB", "a")):
            plan, slots, beh = behaviour(member, NEEDS[member], ports, "skew")
            i = next(k for k, s in enumerate(slots) if s["stage"] == "skew control" and s["pattern"] == key)
            beh[i][cell] = (True, {})
            synthesise(self.d / f"s-{member}", member, NEEDS[member], ports, "skew", beh)
            x = R.record_of(self.d / f"s-{member}", "complete")
            self.assertTrue(x["skew"][key][cell])
            self.assertEqual([(k, c) for k, v in x["skew"].items() for c, f in v.items() if f], [(key, cell)])

    def test_g(self):
        member, ports = "X1", {"a": 2}
        needs = NEEDS[member]
        plan, slots, beh = behaviour(member, needs, ports, "skew")
        i = next(k for k, s in enumerate(slots) if s["stage"] == "test" and s["pattern"] == "A")
        beh[i]["a"] = (True, {2: 1})                                                       # a gated read that writes
        synthesise(self.d / "g", member, needs, ports, "skew", beh)
        x = R.record_of(self.d / "g", "complete")
        self.assertEqual(x["G"], [dict(slot=i, cell="a", port="2", writes=1, writes_prime=1)])
        synthesise(self.d / "mv", member, needs, ports, "skew", move=(i, "a", 1, 0.05))
        x = R.record_of(self.d / "mv", "complete")
        self.assertEqual([(g["slot"], g["cell"], g["port"]) for g in x["G"]], [(i, "a", "1")])
        self.assertAlmostEqual(x["G"][0]["move_mV"], -0.05, places=6)
        synthesise(self.d / "mvn", member, needs, ports, None, move=(i, "a", 1, 0.05), noise="injected")
        self.assertEqual(R.record_of(self.d / "mvn", "complete")["G"], [])                 # the move bound is for runs without noise


class Counts(Base):
    def test_not_reached_or_not_complete(self):
        synthesise(self.d / "r", "F4", NEEDS["F4"], {"a": 1, "b": 1}, "skew", reached=False)
        x = R.record_of(self.d / "r", "complete")
        self.assertFalse(x["counts"])
        self.assertEqual(x["words"], expected_words("F4", NEEDS["F4"], {"a": 1, "b": 1}))     # read and reported, counting nothing
        synthesise(self.d / "t", "F4", NEEDS["F4"], {"a": 1, "b": 1}, "skew")
        for st in ("timeout", "failed", "running", None):
            self.assertFalse(R.record_of(self.d / "t", st)["counts"])
        self.assertTrue(R.record_of(self.d / "t", "complete")["counts"])

    def test_missing_files(self):
        self.assertEqual(R.record_of(self.d / "none", "complete")["counts"], False)
        synthesise(self.d / "x", "X2", NEEDS["X2"], {}, "skew", reached=False)
        (self.d / "x" / "evidence" / "trace.raw").unlink()
        x = R.record_of(self.d / "x", "complete")
        self.assertFalse(x["counts"])
        self.assertIn("unread", x)
        synthesise(self.d / "y", "X2", NEEDS["X2"], {}, "skew")
        (self.d / "y" / "evidence" / "trace.raw").unlink()
        with self.assertRaisesRegex(AssertionError, "a counted run cannot be read"):
            R.record_of(self.d / "y", "complete")

    def test_plan_mismatch_refused(self):
        synthesise(self.d / "p", "F2", NEEDS["F2"], {}, "skew")
        rec = json.loads((self.d / "p" / "record.json").read_text())
        rec["needs"] = [2, 3, 1, 3]
        (self.d / "p" / "record.json").write_text(json.dumps(rec))
        with self.assertRaisesRegex(AssertionError, "plan is not the plan"):
            R.record_of(self.d / "p", "complete")

    def test_collect(self):
        runs = self.d / "RUNS"
        synthesise(runs / "8505-Q", "F4", NEEDS["F4"], {"a": 2, "b": 1}, "skew")
        synthesise(runs / "8505-N1", "F4", NEEDS["F4"], {"a": 2, "b": 1}, None, noise="injected", reached=False)
        (runs / "Q").mkdir()
        (runs / "Q" / "STATE.json").write_text(json.dumps(dict(runs={"8505-Q": dict(status="complete")})))
        (runs / "N1").mkdir()
        (runs / "N1" / "STATE.json").write_text(json.dumps(dict(runs={"8505-N1": dict(status="complete")})))
        out = R.collect(["8505-Q", "8505-N1", "8505-N2"], runs, with_rows=True)
        self.assertEqual([out[k]["counts"] for k in ("8505-Q", "8505-N1", "8505-N2")], [True, False, False])
        self.assertEqual(out["8505-N2"]["unread"], "missing")
        self.assertIn("rows", out["8505-Q"])
        self.assertEqual(set(out["8505-Q"]["rows"][0]["reads"]), {"a", "b"})
        json.dumps(out)


CELL_FIELDS = ("fire", "latency", "start_s", "gated", "late_fires", "ports")
PORT_FIELDS = ("writes", "writes_prime", "u_before_mV", "move_mV", "rises")
C_FIELDS = ("arrivals", "skew_units", "q_peak", "fire_date_s")


class Comparisons(Base):
    """with_rows: rows, result, words_prime and observation, the fields M1's comparisons read."""
    TV = HERE.parent.parent / "function-family" / "topup-verdict" / "PREDICTIONS.json"

    def test_four_fields(self):
        tv = json.loads(self.TV.read_text())
        obs = next(x for x in tv["instances"] if x["seed"] == 8306)["members"]["F2"]["observation"]
        pred = self.d / "PREDICTED.json"
        pred.write_text(json.dumps(dict(instances=[dict(seed=8506, members=dict(F2=dict(member="F2", seed=8506, observation=obs)))])))
        f = self.d / "f2"
        synthesise(f, "F2", NEEDS["F2"], {}, "skew", seed=8506)
        x = R.record_of(f, "complete", with_rows=True, predicted=pred)
        self.assertEqual(list(x), ["counts", "words", "tests", "skew", "G", "rows", "result", "words_prime", "observation", "observation_predicted"])
        self.assertEqual(x["observation_predicted"], obs)
        self.assertNotEqual(x["observation"], obs)                                            # the run's own, not the prediction
        self.assertEqual(set(x["observation"]), set(obs))
        self.assertEqual(x["result"], json.loads((f / "evidence" / "result.json").read_text()))
        self.assertEqual(x["words_prime"], expected_words("F2", NEEDS["F2"], {}))            # every synthetic write lasts 3 us: a write'
        self.assertEqual({r["stage"] for r in x["rows"]}, {"layer 1", "layer 2", "test", "skew control"})
        n_c = 0
        for r in x["rows"]:
            for c, v in r["reads"].items():
                for k in CELL_FIELDS:
                    self.assertIn(k, v, (c, k))
                for p, pv in v["ports"].items():
                    self.assertIn(p, ("1", "2"))
                    for k in PORT_FIELDS:
                        self.assertIn(k, pv)
                    for rise in pv["rises"]:
                        self.assertEqual(set(rise), {"rise_s", "width_s"})
                if c == "c":
                    n_c += 1
                    for k in C_FIELDS:
                        self.assertIn(k, v)
                    for a in v["arrivals"]:
                        self.assertLessEqual({"port", "date_s", "fire_date_s"}, set(a))
        self.assertGreater(n_c, 0)
        json.dumps(x)

    def test_missing_observation_is_left_out(self):
        f = self.d / "x1"
        synthesise(f, "X1", NEEDS["X1"], {"a": 1}, "skew", seed=8501)
        x = R.record_of(f, "complete", with_rows=True)
        self.assertNotIn("observation", x)
        pred = self.d / "P.json"
        pred.write_text(json.dumps(dict(instances=[dict(seed=8504, members={})])))
        self.assertNotIn("observation", R.record_of(f, "complete", with_rows=True, predicted=pred))
        self.assertNotIn("rows", R.record_of(f, "complete"))

    def test_words_prime_differs_on_a_short_write(self):
        member, ports = "X2", {}
        plan, slots, beh = behaviour(member, NEEDS[member], ports, "skew")
        f = self.d / "short"
        synthesise(f, member, NEEDS[member], ports, "skew", beh)
        raw = f / "evidence" / "trace.raw"
        blob = raw.read_bytes()
        head, _, body = blob.partition(b"Binary:\n")
        import measure
        tr = measure.Trace(raw)
        names = ["time"] + SIGNALS
        data = np.frombuffer(body, dtype="<f8").reshape(len(tr.t), len(names)).copy()
        j = names.index("v(xa.x1.si)")
        first = int(np.searchsorted(data[:, 0], net.snap(at(slots[0]["date"])) + 40e-6 - 1e-12))   # the first write of a1: its 0.9 V sample
        data[first - 1, j] = 0.0
        data[first, j] = 1.0                                                                 # one sample at 1.0 V between zeros:
        data[first + 1:first + 5, j] = 0.0                                                   # above 0.9 V for about 0.2 us
        raw.write_bytes(head + b"Binary:\n" + data.astype("<f8").tobytes())
        x = R.record_of(f, "complete", with_rows=True)
        self.assertEqual(x["words"]["a1"][0], "s")
        self.assertEqual(x["words_prime"]["a1"][0], "o")
        self.assertEqual(x["words_prime"]["a2"], x["words"]["a2"])


class FakeT:
    """A synthetic table for family_predict.observation: every Z 0, every latency 1/2 unit (the synthetic FIREs' delay),
    no slot latencies."""

    def __getitem__(self, key):
        return dict(Z=0, latency=0.5, slot_latencies=None)


def predicted_observation(member, ports, needs):
    import predicted as P
    L1 = N.layer1(member)
    Q1 = max(needs[c] for c in L1) + 2
    Q2 = max(needs[f"c{fp.LINE_PORT[c]}"] for c in L1) + 2
    return fp.observation(member, ports, FakeT(), needs, Q1, Q2, P)


REAL_7802 = os.environ.get("REAL_7802")             # a folder holding campaign 6's 7802-quiet run (evidence/...-c1-Q-a), optional


class RunObservation(Base):
    """observation = the RUN's observation, as campaign 5's analyze.run_observation builds it for F1."""

    def test_f1_equals_campaign5_on_synthetic_runs(self):
        A = R.c5_analyze()
        for needs, control in ((NEEDS["F1"], "skew"), (dict(a=3, b=1, c1=2, c2=4), None)):
            f = self.d / f"f1-{control}"
            synthesise(f, "F1", needs, {}, control)
            rows, _ = R.rows_of(f, "F1", needs, {}, control)
            po = predicted_observation("F1", {}, needs)
            self.assertEqual(R.js(R.run_observation("F1", {}, rows, f, po)), R.js(A.run_observation(rows, dict(observation=po), f)))

    @unittest.skipUnless(REAL_7802, "REAL_7802 not set")
    def test_f1_equals_campaign5_on_the_real_7802_quiet(self):
        A = R.c5_analyze()
        f = Path(REAL_7802)
        rec = json.loads((f / "record.json").read_text())
        pred = json.loads((Path(REPO) / "research" / "learned-dnf-circuit-campaign-6" / "stages" / "c1" / "PREDICTED.json").read_text())
        x = next(i for i in pred["instances"] if i["seed"] == rec["seed"])
        needs = dict(zip(("a", "b", "c1", "c2"), rec["needs"]))
        rows, _ = R.rows_of(f, "F1", needs, {}, rec["control"])
        mine = R.run_observation("F1", {}, rows, f, x["observation"])
        theirs = A.run_observation(rows, x, f)
        self.assertEqual(R.js(mine), R.js(theirs))
        self.assertNotEqual(R.js(mine), R.js(x["observation"]))

    def close(self, a, b, what):
        from fractions import Fraction as Fr
        self.assertLessEqual(abs(Fr(a) - Fr(b)), Fr(dnf.SNAP), what)

    def entry(self, r, p, what):
        """One read: the start, the arrivals (which inputs, at the start) and the emissions agree within SNAP."""
        self.close(r["start"], p["start"], what + " start")
        self.assertEqual([a is None for a in r["arrivals"]], [a is None for a in p["arrivals"]], what + " arrivals")
        for a, b in zip(r["arrivals"], p["arrivals"]):
            if a is not None:
                self.close(a, b, what + " arrival")
        self.assertEqual(len(r["emissions"]), len(p["emissions"]), what + " emissions")
        for a, b in zip(r["emissions"], p["emissions"]):
            self.close(a, b, what + " emission")

    def test_zero_error_runs_match_the_prediction(self):
        """On each member's synthetic zero-error run (every unary-port choice), the run's observation agrees with the
        prediction's where it should: the same rows and keys, the same inputs arriving, the same FIREs, every date
        within dnf.SNAP (the runs' pulses are snapped, about 0.005 unit late; the FIREs 1/2 unit after their read,
        as the synthetic table's latency). The values are not compared: the run's are its q peaks, the prediction's
        the calibration's. The scores are the prediction's but on the submask the run observed."""
        n = 0
        for member in STEP1 + ("F1",):
            for ports in port_choices(member):
                needs = NEEDS[member]
                f = self.d / f"z-{member}-{n}"
                synthesise(f, member, needs, ports, "skew")
                rows, _ = R.rows_of(f, member, needs, ports, "skew")
                po = predicted_observation(member, ports, needs)
                ro = R.run_observation(member, ports, rows, f, po)
                self.assertEqual(set(ro), set(po))
                for part in ("firstTrain", "teach"):
                    self.assertEqual(len(ro[part]), len(po[part]), (member, part))
                    for i, (rr, pr) in enumerate(zip(ro[part], po[part])):
                        self.assertEqual(len(rr), len(pr))
                        for j, (r, p) in enumerate(zip(rr, pr)):
                            self.entry(r, p, f"{member} {part}[{i}][{j}]")
                self.assertEqual(len(ro["secondTrain"]), len(po["secondTrain"]))
                for i, (r, p) in enumerate(zip(ro["secondTrain"], po["secondTrain"])):
                    self.entry(r, p, f"{member} secondTrain[{i}]")
                self.assertEqual(list(ro["firstTest"]), list(po["firstTest"]))
                for k in po["firstTest"]:
                    for j, (r, p) in enumerate(zip(ro["firstTest"][k], po["firstTest"][k])):
                        self.entry(r, p, f"{member} firstTest[{k}][{j}]")
                    self.entry(ro["secondTest"][k], po["secondTest"][k], f"{member} secondTest[{k}]")
                    mask = "".join(str(fp.LINE_PORT[c]) for c, a in zip(N.layer1(member), po["secondTest"][k]["arrivals"]) if a is not None) or "-"
                    self.assertEqual(set(ro["scores"][k]), set(po["scores"][k]))
                    self.assertEqual({m: v for m, v in ro["scores"][k].items() if m != mask}, {m: v for m, v in po["scores"][k].items() if m != mask})
                    self.assertEqual(ro["scores"][k][mask], ro["secondTest"][k]["value"])
                n += 1
        self.assertEqual(n, 11)

    def test_a_wrong_fire_shows_in_the_observation(self):
        member, ports = "F3", {"a": 2}
        needs = NEEDS[member]
        plan, slots, beh = behaviour(member, needs, ports, "skew")
        i = next(k for k, s in enumerate(slots) if s["stage"] == "test" and s["pattern"] == "BC")
        beh[i]["c"] = (False, {})
        synthesise(self.d / "wf", member, needs, ports, "skew", beh)
        rows, _ = R.rows_of(self.d / "wf", member, needs, ports, "skew")
        po = predicted_observation(member, ports, needs)
        ro = R.run_observation(member, ports, rows, self.d / "wf", po)
        self.assertEqual(ro["secondTest"]["BC"]["emissions"], [])
        self.assertTrue(po["secondTest"]["BC"]["emissions"])


class PredictedShapes(Base):
    """The prediction record in family_predict's shape and in the campaign's (campaign_predict.record)."""

    def test_both_shapes(self):
        obs = predicted_observation("F4", {"a": 2, "b": 1}, NEEDS["F4"])
        fam = self.d / "fam.json"
        fam.write_text(json.dumps(dict(instances=[dict(seed=8505, members=dict(F4=dict(member="F4", seed=8505, observation=obs)))])))
        camp = self.d / "camp.json"
        camp.write_text(json.dumps(dict(instances=[dict(seed=8503, member="F3", observation=None),
                                                   dict(seed=8505, member="F4", eligible=False, observation=obs)])))
        for path in (fam, camp):
            self.assertEqual(R.observation_of(path, 8505, "F4"), obs)
            self.assertIsNone(R.observation_of(path, 8505, "X1"))
            self.assertIsNone(R.observation_of(path, 8599, "F4"))
            f = self.d / f"run-{path.stem}"
            synthesise(f, "F4", NEEDS["F4"], {"a": 2, "b": 1}, "skew", seed=8505)
            x = R.record_of(f, "complete", with_rows=True, predicted=path)
            self.assertEqual(x["observation_predicted"], obs)
            self.assertEqual(set(x["observation"]), set(obs))
        rehearsal = self.d / "rn.json"                     # the campaign's shape lists one entry per (seed, member): several per seed
        rehearsal.write_text(json.dumps(dict(instances=[dict(seed=8303, member="X1", observation=dict(k=1)), dict(seed=8303, member="F2", observation=dict(k=2))])))
        self.assertEqual(R.observation_of(rehearsal, 8303, "F2"), dict(k=2))
        bad = self.d / "bad.json"
        bad.write_text(json.dumps(dict(instances=[dict(seed=8505, member="F4"), dict(seed=8505, member="F4")])))
        with self.assertRaisesRegex(AssertionError, "listed twice"):
            R.observation_of(bad, 8505, "F4")


class SkewKeys(unittest.TestCase):
    def test_keys_match_the_runner(self):
        for member in STEP1 + ("F1",):
            for ports in port_choices(member):
                plan, slots = N.network(member, NEEDS[member], ports, "skew")
                keys = [s["pattern"] for s in slots if s["stage"] == "skew control"]
                self.assertEqual(keys, R.skew_keys(member))
                self.assertEqual(keys, ["".join(sorted(t)) for t in fp.MEMBERS[member]["terms"].values() if len(t) == 2])
                tests = [s["pattern"] for s in slots if s["stage"] == "test"]
                self.assertTrue(all(k == "".join(sorted(k)) for k in tests if k != "-"))
        self.assertEqual(R.skew_keys("F3"), ["BC"])
        self.assertEqual(R.skew_keys("F2"), ["AB", "AC"])
        self.assertEqual(R.skew_keys("X1"), [])
        self.assertEqual(R.skew_keys("F4"), [])

    def test_ports(self):
        self.assertEqual(R.ports_of("X1", {"a": 2}), ["a2", "c1"])
        self.assertEqual(R.ports_of("X2", {}), ["a1", "a2", "c1"])
        self.assertEqual(R.ports_of("F4", {"a": 2, "b": 1}), ["a2", "b1", "c1", "c2"])
        self.assertEqual(R.ports_of("F2", {}), ["a1", "a2", "b1", "b2", "c1", "c2"])
        self.assertEqual(R.ports_of("F3", {"a": 1}), ["a1", "b1", "b2", "c1", "c2"])
        self.assertEqual(R.ports_of("F1", {}), ["a1", "a2", "b1", "b2", "c1", "c2"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
