"""Tests of batch2x.py. No simulation is run: where a frozen function would start the simulator, a stand-in records
what it was given and stops.   python -B test_batch2x.py REPO [OLD_BATCH_EVIDENCE_DIR]"""
from fractions import Fraction as F
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import batch2x
import dosedev
import dosedev2

REPO = Path(sys.argv.pop(1)).resolve()
OLD = Path(sys.argv.pop(1)).resolve() if len(sys.argv) > 1 and not sys.argv[1].startswith("-") else None
dosedev2.repo_paths(REPO)
import batch6       # noqa: E402
import c4           # noqa: E402
import net          # noqa: E402
import plans4       # noqa: E402
import predict6     # noqa: E402
import session4     # noqa: E402

NGSPICE, PDK = Path("/usr/bin/ngspice"), Path("/home/user/campaign/pdk")
FROZEN_DECK, FROZEN_REWRITE, FROZEN_GUARD = net.deck, dosedev.rewrite, batch6.guard_seed
D = ("0.0027076660145592193", "0.0027076660805780903")


class Stop(Exception):
    pass


class Captured:
    def __init__(self):
        self.calls = []

    def __call__(self, *a, **k):
        self.calls.append((a, k))
        raise Stop()


def lines_changed(a, b):
    assert len(a.splitlines()) == len(b.splitlines())
    return [(x, y) for x, y in zip(a.splitlines(), b.splitlines()) if x != y]


class Guard(unittest.TestCase):
    def test_this_batch_only(self):
        self.assertEqual(batch2x.SEEDS, tuple(range(8301, 8311)))
        for s in batch2x.SEEDS:
            self.assertEqual(batch2x.guard_seed(str(s)), s)
        for bad in ("none", "7701", "7710", "7801", "8300", "8311", "0"):
            with self.assertRaises(AssertionError, msg=bad):
                batch2x.guard_seed(bad)
        self.assertFalse(set(batch2x.SEEDS) & set(batch6.SEEDS))

    def test_the_frozen_guard_is_replaced_for_the_block_only(self):
        with batch2x.seeds():
            self.assertEqual(batch6.guard_seed("8301"), 8301)
            with self.assertRaises(AssertionError):
                batch6.guard_seed("7701")
        self.assertIs(batch6.guard_seed, FROZEN_GUARD)
        with self.assertRaises(Stop):
            with batch2x.seeds():
                raise Stop()
        self.assertIs(batch6.guard_seed, FROZEN_GUARD)
        with self.assertRaises(AssertionError):
            batch6.guard_seed("8301")                        # the frozen guard still refuses this batch's seeds


class FrozenPaths(unittest.TestCase):
    """What each frozen function hands to the simulator for a seed of this batch."""

    def setUp(self):
        self.play, self.session = session4.play, net.Session
        self.tmp = tempfile.TemporaryDirectory()
        self.out = Path(self.tmp.name)

    def tearDown(self):
        session4.play, net.Session = self.play, self.session
        self.tmp.cleanup()
        self.assertIs(net.deck, FROZEN_DECK)
        self.assertIs(dosedev.rewrite, FROZEN_REWRITE)
        self.assertIs(batch6.guard_seed, FROZEN_GUARD)

    def two_lines(self, frozen, text):
        diff = lines_changed(frozen, text)
        self.assertEqual(len(diff), 2)
        self.assertEqual(sorted(x.replace("vhi=0.6", "vhi=0.7").replace("reltol=1e-4", "reltol=1e-5") for x, _ in diff), sorted(y for _, y in diff))
        self.assertIn("vhi=0.7", text)
        self.assertIn("reltol=1e-5", text)

    def test_the_two_decks(self):
        frozen = FROZEN_DECK(cells=c4.CELLS, section=c4.SECTION)
        self.assertNotEqual(c4.SECTION, "tt")
        for guard in ("on", "off"):
            cap = Captured()
            session4.play = cap
            with self.assertRaises(Stop):
                batch2x.cal(REPO, self.out / f"cal-{guard}", 8301, guard, NGSPICE, PDK)
            (a, k), = cap.calls
            self.assertEqual(k, dict(seed=8301, guard_off=guard == "off"))
            self.assertEqual(a[1], plans4.calibration()[0])
            self.two_lines(frozen, a[2])

    def test_every_scan_kind(self):
        frozen = FROZEN_DECK(cells=c4.CELLS, section=c4.SECTION, leak_per_port=True)
        for n, argv in enumerate((["a", "pair", "1/2", *D], ["b", "pair", "1/2", *D], ["c", "line1", "1/2", *D], ["c", "line2", "1/2", *D],
                                  ["c", "bothfire", *D], ["a", "onesided", "8", "8", *D], ["b", "onesided", "4097/512", "4097/512", *D])):
            cap = Captured()
            net.Session = cap
            with self.assertRaises(Stop):
                batch2x.scan(REPO, self.out / f"s{n}", 8302, [*argv, str(NGSPICE), str(PDK)])
            (a, k), = cap.calls
            self.assertEqual(k.get("seed"), 8302, argv)
            self.two_lines(frozen, a[1])

    def test_refusals(self):
        session4.play = net.Session = Captured()
        for seed in (7701, 7801, "none", 8311):
            with self.assertRaises(AssertionError, msg=str(seed)):
                batch2x.cal(REPO, self.out / f"x{seed}", seed, "on", NGSPICE, PDK)
            with self.assertRaises(AssertionError, msg=str(seed)):
                batch2x.scan(REPO, self.out / f"y{seed}", seed, ["a", "pair", "1/2", *D, str(NGSPICE), str(PDK)])
        with self.assertRaises(AssertionError):
            batch2x.cal(REPO, self.out / "g", 8301, "half", NGSPICE, PDK)
        with self.assertRaises(AssertionError):
            batch2x.scan(REPO, self.out / "r", 8301, ["a", "reach", "8", *D, str(NGSPICE), str(PDK)])
        with self.assertRaises(AssertionError):
            batch2x.cal(REPO, REPO / "research" / "x", 8301, "on", NGSPICE, PDK)
        with self.assertRaises(AssertionError):
            batch2x.scan(REPO, REPO / "x", 8301, ["a", "pair", "1/2", *D, str(NGSPICE), str(PDK)])
        self.assertEqual(session4.play.calls, [])


class Plan(unittest.TestCase):
    def test_limits(self):
        self.assertEqual({k: batch2x.limit_s(k) for k in batch2x.BATCH6_MEAN_S},
                         {"cal-on": 3380, "cal-off": 2330, "pair": 1390, "line": 1310, "bothfire": 120, "onesided": 880})
        for k in batch2x.BATCH6_MEAN_S:
            self.assertGreaterEqual(batch2x.limit_s(k), 2 * batch2x.expected_s(k))
            self.assertLess(batch2x.limit_s(k), 2 * batch2x.expected_s(k) + 10)

    def test_the_ninety_runs(self):
        w1, w2, w3 = batch2x.planned(REPO, "/x/runs", NGSPICE, PDK)
        self.assertEqual((len(w1), len(w2), len(w3)), (20, 50, 20))
        ids = [j["id"] for w in (w1, w2, w3) for j in w]
        self.assertEqual(len(set(ids)), 90)
        for s in batch2x.SEEDS:
            mine = sorted(i[5:] for i in ids if i.startswith(f"{s}-"))
            self.assertEqual(mine, sorted(["cal-on", "cal-off", "scan-a-pair", "scan-b-pair", "scan-c-line1", "scan-c-line2", "bothfire-c", "onesided-a", "onesided-b"]))
        for j in w1 + w2 + w3:
            self.assertEqual(j["argv"][0], sys.executable)
            self.assertEqual(j["argv"][1:3], ["-B", str(HERE / "batch2x.py")])
            self.assertIn(j["argv"][3], ("cal", "scan"))
            self.assertEqual(j["argv"][5], f"/x/runs/{j['id']}")
            self.assertEqual(j["argv"][-2:], [str(NGSPICE), str(PDK)])
            self.assertEqual(j["limit_s"], batch2x.limit_s(j["kind"]))
        self.assertEqual(sorted({j["kind"] for j in w1 + w2 + w3}), sorted(batch2x.BATCH6_MEAN_S))

    def test_an_instance_without_its_deck_or_its_scans_is_left_out(self):
        doses = {8301: {c: D for c in "abc"}, 8303: {c: D for c in "abc"}}
        w2 = batch2x.wave2(REPO, "/x", NGSPICE, PDK, doses)
        self.assertEqual(sorted({j["id"][:4] for j in w2}), ["8301", "8303"])
        self.assertEqual(len(w2), 10)
        a = next(j for j in w2 if j["id"] == "8301-scan-c-line2")["argv"]
        self.assertEqual(a[6:11], ["8301", "c", "line2", "1/2", D[0]])
        b = next(j for j in w2 if j["id"] == "8303-bothfire-c")["argv"]
        self.assertEqual(b[6:11], ["8303", "c", "bothfire", *D])
        w3 = batch2x.wave3(REPO, "/x", NGSPICE, PDK, doses, {8303: dict(a="4097/512", b="4103/512")})
        self.assertEqual([j["id"] for j in w3], ["8303-onesided-a", "8303-onesided-b"])
        self.assertEqual(w3[1]["argv"][6:13], ["8303", "b", "onesided", "4103/512", "4103/512", *D])

    def test_the_bound_is_the_frozen_rule(self):
        S, h = dict(a=F(855, 512), b=F(861, 512)), dict(a=F(1, 512), b=F(1, 512))
        self.assertEqual(dosedev2.bound(F(8), S, h), predict6.layer1_bounds(S, h))


class Smoke(unittest.TestCase):
    """The smoke is the nominal cell: seed None, section tt, the same two lines rewritten."""

    def setUp(self):
        self.play, self.session = session4.play, net.Session
        self.tmp = tempfile.TemporaryDirectory()
        self.out = Path(self.tmp.name)

    def tearDown(self):
        session4.play, net.Session = self.play, self.session
        self.tmp.cleanup()
        self.assertIs(net.deck, FROZEN_DECK)
        self.assertIs(dosedev.rewrite, FROZEN_REWRITE)
        self.assertIs(batch6.guard_seed, FROZEN_GUARD)

    def test_decks(self):
        frozen = FROZEN_DECK(cells=c4.CELLS, section="tt")
        for guard in ("on", "off"):
            cap = Captured()
            session4.play = cap
            with self.assertRaises(Stop):
                batch2x.smoke_cal(REPO, self.out / guard, guard, NGSPICE, PDK)
            (a, k), = cap.calls
            self.assertEqual(k, dict(seed=None, guard_off=guard == "off"))
            self.assertEqual(len(lines_changed(frozen, a[2])), 2)
            self.assertIn("reltol=1e-5", a[2])

    def test_both_lines_and_one_sided(self):
        frozen = FROZEN_DECK(cells=c4.CELLS, section="tt", leak_per_port=True)
        for n, argv in enumerate((["c", "bothfire", *D], ["a", "onesided", batch2x.SMOKE_BOUND, batch2x.SMOKE_BOUND, *D])):
            cap = Captured()
            net.Session = cap
            with self.assertRaises(Stop):
                batch2x.smoke_scan(REPO, self.out / f"s{n}", [*argv, str(NGSPICE), str(PDK)])
            (a, k), = cap.calls
            self.assertEqual(k.get("seed"), None)
            self.assertEqual(len(lines_changed(frozen, a[1])), 2)
        with self.assertRaises(AssertionError):
            batch2x.smoke_scan(REPO, self.out / "p", ["a", "pair", "1/2", *D, str(NGSPICE), str(PDK)])

    def test_the_bound_and_the_jobs(self):
        S, h = dict(a=F(857, 512), b=F(857, 512)), dict(a=F(1, 512), b=F(1, 512))
        self.assertEqual(predict6.layer1_bounds(S, h), dict(a=F(batch2x.SMOKE_BOUND), b=F(batch2x.SMOKE_BOUND)))
        decks = batch2x.smoke_jobs(REPO, "/x/s", NGSPICE, PDK)
        self.assertEqual([(j["id"], j["limit_s"]) for j in decks], [("none-smoke-cal-on", 1520), ("none-smoke-cal-off", 1140)])
        rest = batch2x.smoke_jobs(REPO, "/x/s", NGSPICE, PDK, dict(a=D, b=D, c=D))
        self.assertEqual([(j["id"], j["limit_s"]) for j in rest], [("none-smoke-bothfire-c", 100), ("none-smoke-onesided-a", 460)])
        self.assertEqual(rest[1]["argv"][6:12], ["a", "onesided", "4097/512", "4097/512", *D])


class Waves(unittest.TestCase):
    """Each wave is started once, in order. No simulation: the refusals come before any run."""

    def test_order(self):
        with tempfile.TemporaryDirectory() as t:
            runs = Path(t) / "runs"
            with self.assertRaises(AssertionError):
                batch2x.w2(REPO, runs, NGSPICE, PDK)             # no wave 1
            with self.assertRaises(AssertionError):
                batch2x.w3(REPO, runs, NGSPICE, PDK)             # no wave 2
            (runs / "W1").mkdir(parents=True)
            with self.assertRaises(AssertionError):
                batch2x.w1(REPO, runs, NGSPICE, PDK)             # the folder exists: wave 1 is not started twice
            state = dict(runs={f"{s}-cal-{g}": dict(status="running") for s in batch2x.SEEDS for g in ("on", "off")})
            (runs / "W1" / "STATE.json").write_text(json.dumps(state))
            with self.assertRaises(AssertionError):
                batch2x.w2(REPO, runs, NGSPICE, PDK)             # wave 1 still running
            (runs / "JOBS_W2.json").write_text("{}")
            (runs / "W2").mkdir()
            (runs / "W2" / "STATE.json").write_text(json.dumps(dict(runs={"8301-scan-a-pair": dict(status="running")})))
            with self.assertRaises(AssertionError):
                batch2x.w3(REPO, runs, NGSPICE, PDK)             # wave 2 still running
            with self.assertRaises(AssertionError):
                batch2x.w2(REPO, runs, NGSPICE, PDK)             # wave 2 is not started twice

    def test_wave_2_with_no_usable_deck_starts_nothing(self):
        with tempfile.TemporaryDirectory() as t:
            runs = Path(t) / "runs"
            (runs / "W1").mkdir(parents=True)
            state = dict(runs={f"{s}-cal-{g}": dict(status="failed (exit 1)") for s in batch2x.SEEDS for g in ("on", "off")})
            (runs / "W1" / "STATE.json").write_text(json.dumps(state))
            self.assertEqual(batch2x.w2(REPO, runs, NGSPICE, PDK), {})
            left = json.loads((runs / "NOT_STARTED_W2.json").read_text())
            self.assertEqual(len(left), 70)
            self.assertEqual(json.loads((runs / "DOSES.json").read_text()), {})
            self.assertEqual(batch2x.w3(REPO, runs, NGSPICE, PDK), {})


@unittest.skipIf(OLD is None, "no folder of campaign 6's development batch given")
class DosesOnAMismatchedCell(unittest.TestCase):
    """doses_of on the decks of campaign 6's own batch gives the doses that batch's scans were started with."""

    def test_two_instances(self):
        for m, seed in (("a", 7701), ("b", 7706)):
            got, why = batch2x.doses_of(REPO, OLD / m / f"{seed}-cal-on", OLD / m / f"{seed}-cal-off")
            self.assertIsNone(why)
            for cell, kind in (("a", "pair"), ("b", "pair"), ("c", "line1"), ("c", "line2")):
                used = json.loads((OLD / m / f"{seed}-scan-{cell}-{kind}" / "record.json").read_text())["D_V"]
                self.assertEqual(list(got[cell]), [used["1"], used["2"]], (seed, cell, kind))


if __name__ == "__main__":
    unittest.main(verbosity=2)
