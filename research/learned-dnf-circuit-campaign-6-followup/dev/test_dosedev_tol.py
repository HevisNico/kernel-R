"""Tests of dosedev_tol.py. No simulation is run: where the frozen scan would start the simulator, a stand-in records
what it was given and stops.   python -B test_dosedev_tol.py REPO"""
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dosedev
import dosedev2
import dosedev_tol

REPO = Path(sys.argv.pop(1)).resolve()
dosedev2.repo_paths(REPO)
import c4           # noqa: E402
import net          # noqa: E402

NGSPICE, PDK = Path("/usr/bin/ngspice"), Path("/home/user/campaign/pdk")
FROZEN_DECK = net.deck
FROZEN_REWRITE = dosedev.rewrite
SCAN_DECK = dict(cells=c4.CELLS, section="tt", leak_per_port=True)        # the deck every scan uses (test_dosedev2.py)
D2 = ("0.0027076660145592193", "0.0027076660805780903")


class Stop(Exception):
    pass


def lines_changed(a, b):
    assert len(a.splitlines()) == len(b.splitlines())
    return [(x, y) for x, y in zip(a.splitlines(), b.splitlines()) if x != y]


class Rewrite(unittest.TestCase):
    def test_without_reltol_it_is_dosedev_rewrite(self):
        frozen = FROZEN_DECK(**SCAN_DECK)
        for params in ({}, dict(vhi="0.7"), dict(vhi="0.7", vlo="0.5")):
            self.assertEqual(dosedev_tol.rewrite(frozen, params), FROZEN_REWRITE(frozen, params))
        self.assertEqual(dosedev_tol.rewrite(frozen, {})[0].encode(), frozen.encode())

    def test_reltol_changes_one_value_on_the_option_line(self):
        for deck_args in (SCAN_DECK, dict(cells=c4.CELLS, section="tt"), dict(cells=c4.CELLS, section="tt", noise=True)):
            frozen = FROZEN_DECK(**deck_args)
            text, changed = dosedev_tol.rewrite(frozen, dict(reltol="1e-5"))
            diff = lines_changed(frozen, text)
            self.assertEqual(len(diff), 1)
            self.assertTrue(diff[0][0].startswith(".option "))
            self.assertEqual(diff[0][0].replace("reltol=1e-4", "reltol=1e-5"), diff[0][1])
            self.assertEqual(changed, dict(reltol=dict(old="1e-4", new="1e-5")))

    def test_window_and_reltol_change_two_lines(self):
        frozen = FROZEN_DECK(**SCAN_DECK)
        text, changed = dosedev_tol.rewrite(frozen, dict(vhi="0.7", reltol="1e-5"))
        diff = lines_changed(frozen, text)
        self.assertEqual(len(diff), 2)
        self.assertEqual(sorted(changed), ["reltol", "vhi"])
        only_window = FROZEN_REWRITE(frozen, dict(vhi="0.7"))[0]
        self.assertEqual(len(lines_changed(only_window, text)), 1)

    def test_same_value_gives_the_frozen_text(self):
        frozen = FROZEN_DECK(**SCAN_DECK)
        self.assertEqual(dosedev_tol.rewrite(frozen, dict(reltol="1e-4"))[0].encode(), frozen.encode())

    def test_a_deck_without_one_reltol_is_refused(self):
        frozen = FROZEN_DECK(**SCAN_DECK)
        with self.assertRaises(AssertionError):
            dosedev_tol.rewrite(frozen.replace("reltol=1e-4 ", ""), dict(reltol="1e-5"))
        with self.assertRaises(AssertionError):
            dosedev_tol.rewrite(frozen + ".option reltol=1e-4\n", dict(reltol="1e-5"))
        with self.assertRaises(AssertionError):
            dosedev_tol.rewrite(frozen + "* reltol=1e-4\n", dict(reltol="1e-5"))


class Parse(unittest.TestCase):
    def test_accepted(self):
        self.assertEqual(dosedev_tol.parse(["vhi=0.7", "reltol=1e-5"]), dict(vhi="0.7", reltol="1e-5"))
        self.assertEqual(dosedev_tol.parse(["reltol=1e-5"]), dict(reltol="1e-5"))
        self.assertEqual(dosedev_tol.parse([]), {})

    def test_refused(self):
        for bad in (["reltol=small"], ["reltol=0.00001"], ["reltol=1e-5", "reltol=1e-6"], ["abstol=1e-14"], ["cs0=600f"], ["reltol=1e5"], ["reltol="]):
            with self.assertRaises(AssertionError, msg=str(bad)):
                dosedev_tol.parse(bad)

    def test_dosedev2_still_refuses_it(self):
        with self.assertRaises(AssertionError):
            dosedev2.parse(["reltol=1e-5"])


class Scan(unittest.TestCase):
    """What the frozen scan hands to the simulator through dosedev_tol.scan."""

    def setUp(self):
        self.session = net.Session
        self.tmp = tempfile.TemporaryDirectory()
        self.out = Path(self.tmp.name)

    def tearDown(self):
        net.Session = self.session
        self.tmp.cleanup()

    def text(self, name, argv, pairs):
        calls = []

        def captured(*a, **k):
            calls.append((a, k))
            raise Stop()
        net.Session = captured
        with self.assertRaises(Stop):
            dosedev_tol.scan(REPO, self.out / name, [*argv, str(NGSPICE), str(PDK)], pairs)
        (a, k), = calls
        self.assertEqual(k.get("seed"), None)
        return a[1]

    def test_the_three_scans_of_the_plan(self):
        frozen = FROZEN_DECK(**SCAN_DECK)
        for name, argv, pairs, n in (("a2", ["a", "pair", "1/2", *D2], ["vhi=0.7", "reltol=1e-5"], 2),
                                     ("b2", ["b", "pair", "1/2", *D2], ["vhi=0.7", "reltol=1e-5"], 2),
                                     ("a1", ["a", "pair", "1/2", "0.0013494418602283745", "0.001349441878424715"], ["reltol=1e-5"], 1)):
            text = self.text(name, argv, pairs)
            diff = lines_changed(frozen, text)
            self.assertEqual(len(diff), n, name)
            self.assertIn("reltol=1e-5", text)
            self.assertNotIn("reltol=1e-4", text)
            self.assertEqual("vhi=0.7" in text, n == 2)

    def test_without_reltol_it_is_dosedev2_scan(self):
        frozen = FROZEN_DECK(**SCAN_DECK)
        self.assertEqual(self.text("f", ["a", "pair", "1/2", *D2], []).encode(), frozen.encode())
        self.assertEqual(len(lines_changed(frozen, self.text("w", ["a", "pair", "1/2", *D2], ["vhi=0.7"]))), 1)

    def test_restored_after_the_call_and_after_an_error(self):
        self.text("r", ["a", "pair", "1/2", *D2], ["reltol=1e-5"])
        self.assertIs(dosedev.rewrite, FROZEN_REWRITE)
        self.assertIs(net.deck, FROZEN_DECK)
        with self.assertRaises(Stop):
            with dosedev_tol.tolerance():
                raise Stop()
        self.assertIs(dosedev.rewrite, FROZEN_REWRITE)

    def test_only_scans(self):
        for kind in ("bothfire", "onesided"):
            with self.assertRaises(AssertionError):
                dosedev_tol.scan(REPO, self.out / kind, ["a", kind, "8", "8", *D2, str(NGSPICE), str(PDK)], ["reltol=1e-5"])

    def test_inside_the_repository_is_refused(self):
        with self.assertRaises(AssertionError):
            dosedev_tol.scan(REPO, REPO / "x", ["a", "pair", "1/2", *D2, str(NGSPICE), str(PDK)], ["reltol=1e-5"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
