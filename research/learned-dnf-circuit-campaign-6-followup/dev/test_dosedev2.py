"""Tests of dosedev2.py. No simulation is run: where a frozen function would start the simulator, a stand-in records
what it was given and stops.   python -B test_dosedev2.py REPO"""
from fractions import Fraction as F
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dosedev2

REPO = Path(sys.argv.pop(1)).resolve()
dosedev2.repo_paths(REPO)
import batch6       # noqa: E402
import c4           # noqa: E402
import net          # noqa: E402
import plans4       # noqa: E402
import predict6     # noqa: E402
import scan6        # noqa: E402
import session4     # noqa: E402

NGSPICE, PDK = Path("/usr/bin/ngspice"), Path("/home/user/campaign/pdk")
FROZEN_DECK = net.deck
D1 = ("0.0013494418602283745", "0.001349441878424715")
TWICE = dict(vhi="0.7")


class Stop(Exception):
    pass


def lines_changed(a, b):
    assert len(a.splitlines()) == len(b.splitlines())
    return [(x, y) for x, y in zip(a.splitlines(), b.splitlines()) if x != y]


class Captured:
    """Stands in for session4.play or net.Session: keeps its arguments and stops the run before any simulator."""
    def __init__(self):
        self.calls = []

    def __call__(self, *a, **k):
        self.calls.append((a, k))
        raise Stop()


class Window(unittest.TestCase):
    ARGS = (dict(cells=c4.CELLS, section="tt"), dict(cells=c4.CELLS, section="tt", leak_per_port=True), dict(cells=c4.CELLS, section="tt", noise=True))

    def test_no_parameter_gives_the_frozen_text_for_every_deck_used(self):
        for k in self.ARGS:
            seen = []
            with dosedev2.window({}, seen):
                text = net.deck(**k)
            self.assertEqual(text.encode(), FROZEN_DECK(**k).encode(), k)
            self.assertEqual(seen[0]["frozen_sha256"], seen[0]["as_run_sha256"])
        self.assertIs(net.deck, FROZEN_DECK)                 # restored

    def test_vhi_changes_one_line_of_every_deck_used(self):
        for k in self.ARGS:
            with dosedev2.window(TWICE):
                text = net.deck(**k)
            diff = lines_changed(FROZEN_DECK(**k), text)
            self.assertEqual(len(diff), 1, k)
            self.assertEqual(diff[0][0].replace("vhi=0.6", "vhi=0.7"), diff[0][1])

    def test_restored_after_an_error(self):
        with self.assertRaises(Stop):
            with dosedev2.window(TWICE):
                raise Stop()
        self.assertIs(net.deck, FROZEN_DECK)

    def test_only_the_window(self):
        for bad in (["cs0=600f"], ["idis=12.3n"], ["cf0=15p"], ["vhi=0.7", "cs0=600f"]):
            with self.assertRaises(AssertionError, msg=str(bad)):
                dosedev2.parse(bad)
        self.assertEqual(dosedev2.parse(["vhi=0.7"]), TWICE)


class FrozenPaths(unittest.TestCase):
    """What each frozen function hands to the simulator, with and without the window."""

    def setUp(self):
        self.play, self.session = session4.play, net.Session
        self.tmp = tempfile.TemporaryDirectory()
        self.out = Path(self.tmp.name)

    def tearDown(self):
        session4.play, net.Session = self.play, self.session
        self.tmp.cleanup()

    def cal_off_text(self, params):
        cap = Captured()
        session4.play = cap
        with self.assertRaises(Stop):
            with dosedev2.window(params):
                batch6.cal(self.out / "cal", None, "off", NGSPICE, PDK)
        (a, k), = cap.calls
        self.assertEqual(k, dict(seed=None, guard_off=True))
        self.assertEqual(a[1], plans4.calibration()[0])
        return a[2]

    def test_guard_off_deck(self):
        frozen = FROZEN_DECK(cells=c4.CELLS, section="tt")
        self.assertEqual(self.cal_off_text({}).encode(), frozen.encode())
        self.assertEqual(len(lines_changed(frozen, self.cal_off_text(TWICE))), 1)

    def scan_text(self, argv, params):
        cap = Captured()
        net.Session = cap
        with self.assertRaises(Stop):
            with dosedev2.window(params):
                scan6.main([str(self.out / "scan"), "none", *argv, str(NGSPICE), str(PDK)])
        (a, k), = cap.calls
        self.assertEqual(k.get("seed"), None)
        return a[1]

    def test_every_scan_kind(self):
        frozen = FROZEN_DECK(cells=c4.CELLS, section="tt", leak_per_port=True)
        for argv in (["a", "pair", "1/2", *D1], ["b", "pair", "1/2", *D1], ["c", "line1", "1/2", *D1], ["c", "line2", "1/2", *D1],
                     ["c", "bothfire", *D1], ["a", "onesided", "8", "8", *D1], ["b", "onesided", "4", "4", *D1]):
            self.assertEqual(self.scan_text(argv, {}).encode(), frozen.encode(), argv)
            self.assertEqual(len(lines_changed(frozen, self.scan_text(argv, TWICE))), 1, argv)

    def seeds(self):
        f = self.out / "NOISE_SEEDS_DEV.txt"
        f.write_text("# test\n5100001 1x\n5200001 2x\n")
        return f

    def network_call(self, noise, seed, params, rid="r"):
        cap = Captured()
        session4.play = cap
        with self.assertRaises(Stop):
            dosedev2.network(REPO, self.out / rid, rid, [4, 4, 4, 4], "skew" if noise == "none" else None, noise, seed, self.seeds_file, NGSPICE, PDK, params)
        (a, k), = cap.calls
        return a, k

    def test_network_runs(self):
        self.seeds_file = self.seeds()
        quiet, noisy = FROZEN_DECK(cells=c4.CELLS, section="tt"), FROZEN_DECK(cells=c4.CELLS, section="tt", noise=True)
        a, k = self.network_call("none", 0, {})
        self.assertEqual(a[2].encode(), quiet.encode())
        self.assertEqual(a[1], plans4.network((4, 4, 4, 4), "skew")[0])
        self.assertEqual(k, dict(seed=None, guard_off=False, noise_id=None, shim=None))
        a, k = self.network_call("none", 0, TWICE)
        self.assertEqual(len(lines_changed(quiet, a[2])), 1)
        a, k = self.network_call("injected", 5100001, {}, "n1")
        self.assertEqual(a[2].encode(), noisy.encode())
        self.assertEqual(a[1], plans4.network((4, 4, 4, 4), None)[0])
        self.assertEqual((k["seed"], k["guard_off"], k["noise_id"]), (None, False, 5100001))
        self.assertTrue(str(k["shim"]).endswith("fakepid.so"))
        a, k = self.network_call("injected", 5200001, TWICE, "n2")
        self.assertEqual(len(lines_changed(noisy, a[2])), 1)
        self.assertEqual(k["noise_id"], 5200001)

    def refused(self, *a, **k):
        with self.assertRaises(AssertionError):
            dosedev2.network(REPO, *a, **k)

    def test_noise_seed_refusals(self):
        self.seeds_file = f = self.seeds()
        session4.play = Captured()
        self.refused(self.out / "x1", "x1", [4, 4, 4, 4], None, "injected", 78021, f, NGSPICE, PDK, {})          # a campaign seed
        self.refused(self.out / "x2", "x2", [4, 4, 4, 4], None, "injected", 5200001, f, NGSPICE, PDK, {})        # a 2x seed on the 1x deck
        self.refused(self.out / "x3", "x3", [4, 4, 4, 4], None, "injected", 5100001, f, NGSPICE, PDK, TWICE)     # a 1x seed on the 2x deck
        self.refused(self.out / "x4", "x4", [4, 4, 4, 4], "skew", "none", 5100001, f, NGSPICE, PDK, {})          # a seed on a quiet run
        self.refused(self.out / "x5", "x5", [4, 4, 4, 4], None, "injected", 5100001, f, NGSPICE, PDK, dict(vhi="0.8"))   # not 1x or 2x
        self.refused(self.out / "x6", "x6", [4, 4, 4, 4], "untrained", "none", 0, f, NGSPICE, PDK, {})
        with self.assertRaises(Stop):
            dosedev2.network(REPO, self.out / "y1", "y1", [4, 4, 4, 4], None, "injected", 5100001, f, NGSPICE, PDK, {})
        self.refused(self.out / "y2", "y2", [4, 4, 4, 4], None, "injected", 5100001, f, NGSPICE, PDK, {})        # used once already
        self.assertEqual((f.with_name("NOISE_SEEDS_USED") / "5100001").read_text().strip(), "y1")

    def test_inside_the_repository_is_refused(self):
        self.seeds_file = self.seeds()
        with self.assertRaises(AssertionError):
            dosedev2.network(REPO, REPO / "research" / "x", "x", [4, 4, 4, 4], "skew", "none", 0, self.seeds_file, NGSPICE, PDK, {})
        with self.assertRaises(AssertionError):
            dosedev2.caloff(REPO, REPO / "x", NGSPICE, PDK, {})


class Bound(unittest.TestCase):
    def test_eight_is_the_frozen_rule(self):
        for sa, sb in ((F(783, 256), F(841, 256)), (F(585, 256), F(949, 256)), (F(1155, 256), F(633, 256)), (F(43, 25), F(179, 100)), (F(1, 2), F(15, 2))):
            S, h = dict(a=sa, b=sb), dict(a=F(1, 256), b=F(1, 256))
            self.assertEqual(dosedev2.bound(F(8), S, h), predict6.layer1_bounds(S, h))

    def test_another_value(self):
        S, h = dict(a=F(7, 4), b=F(9, 5)), dict(a=F(1, 256), b=F(1, 256))
        self.assertEqual(dosedev2.bound(F(4), S, h), dict(a=F(7, 4) + F(9, 4) + F(1, 256), b=F(9, 5) + F(9, 4) + F(1, 256)))


class Seeds(unittest.TestCase):
    USED = [(1, 707), (201, 9920), (706002, 706082), (900000, 900002), (75011, 75123), (90951, 90953), (76011, 76123), (76911, 76933),
            (90961, 90961), (78011, 78053), (77011, 77011), (77061, 77061)]

    def test_the_declared_file(self):
        d = dosedev2.declared_seeds(HERE / "NOISE_SEEDS_DEV.txt")
        self.assertEqual(len(d), 16)
        self.assertEqual(sorted(d.values()), ["1x"] * 8 + ["2x"] * 8)
        for seed in d:
            self.assertGreater(seed, 4194304)
            self.assertLess(seed, 2 ** 31)
            self.assertFalse(any(lo <= seed <= hi for lo, hi in self.USED), seed)


class Many(unittest.TestCase):
    def test_waves_limits_and_statuses(self):
        with tempfile.TemporaryDirectory() as t:
            jobs = dict(folder=str(Path(t) / "runs"), waves=[
                [dict(id=f"ok{i}", argv=["sh", "-c", f"sleep 1; date +%s.%N > {t}/ok{i}"], limit_s=20) for i in range(5)]
                + [dict(id="bad", argv=["sh", "-c", "exit 3"], limit_s=20), dict(id="long", argv=["sleep", "30"], limit_s=1)],
                [dict(id="second", argv=["sh", "-c", f"ls {t}/ok4 && date +%s.%N > {t}/second"], limit_s=20)]])
            (Path(t) / "JOBS.json").write_text(json.dumps(jobs))
            dosedev2.many(Path(t) / "JOBS.json")
            state = json.loads((Path(t) / "runs" / "STATE.json").read_text())["runs"]
            self.assertEqual({k: v["status"] for k, v in state.items()},
                             dict(**{f"ok{i}": "complete" for i in range(5)}, bad="failed (exit 3)", long="cut at its limit", second="complete"))
            self.assertGreater(float((Path(t) / "second").read_text()), max(float((Path(t) / f"ok{i}").read_text()) for i in range(5)))


if __name__ == "__main__":
    unittest.main(verbosity=2)
