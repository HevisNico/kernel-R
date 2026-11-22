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


def synthesise(folder, member, needs, ports, control, beh=None, reached=True, noise="none", move=None):
    """A run folder: record.json, evidence/result.json (plan and delivered occurrences) and evidence/trace.raw, from
    the behaviour (or the zero-error one). move: (slot, cell, port, mV) steps the stored voltage during that read."""
    plan, slots, zero = behaviour(member, needs, ports, control)
    beh = zero if beh is None else beh
    horizon = at(plan["horizon"]) + 50e-6
    t = np.arange(0.0, horizon, 1e-6)
    v = {n: np.zeros_like(t) for n in SIGNALS}
    for c in "abc":
        v[f"v(x{c}.vq)"][:] = 1.2
    pulse = lambda name, t0, width: v[name].__setitem__((t >= t0) & (t <= t0 + width), 1.8)
    occ = []
    for date, c, p, amp in plan["sources"]:
        occ.append(dict(id=len(occ), cell=c, port=p, amp=amp, origin="source", calendar_date=date, date_s=at(date), delivered=True))
    for i, (s, b) in enumerate(zip(slots, beh)):
        lo = at(s["date"])
        fires = {}
        for c in N.layer1(member):
            if c not in b:
                continue
            mine = [at(d) for d, cc, _, _ in plan["sources"] if cc == c and at(s["date"]) - 1e-9 <= at(d) < at(s["date"] + dnf.SLOT) - 1e-9]
            start = min(mine)
            f, wr = b[c]
            if f:
                fires[c] = start + 10e-6
                pulse(f"v(x{c}.p)", fires[c], 3e-6)
            for p, n in wr.items():
                for k in range(n):
                    pulse(f"v(x{c}.x{p}.si)", start + 40e-6 + 10e-6 * k, 3e-6)
        if "c" in b or (s["routed"] and fires):
            arr = []
            for src, fd in fires.items():
                e = next(e for e in plan["edges"] if e["source"] == src and e["gate"][0] == s["date"] + min(o for n, o in s["inputs"].items() if n in fp.wiring(member, ports)[src]))
                occ.append(dict(id=len(occ), cell="c", port=e["port"], amp=e["amp"], origin=e["name"], fire_date_s=fd, date_s=fd + c4.WIRE * TU, delivered=True))
                arr.append(fd + c4.WIRE * TU)
            if arr and "c" in b:
                f, wr = b["c"]
                if f:
                    pulse("v(xc.p)", max(arr) + 10e-6, 3e-6)
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
    result = dict(plan=json.loads(json.dumps(plan)), occurrences=occ, horizon_s=at(plan["horizon"]))
    (ev / "result.json").write_text(json.dumps(result))
    rec = dict(id="synthetic", kind="network", member=member, unary_ports=ports, needs=list(N.check_needs(member, needs).values()),
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
