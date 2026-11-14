"""The execution rules of ../AMENDMENT_2.md, on two throw-away checkouts. No simulation.

  python3 -B -m unittest test_execute        (from research/sky130-layout/phase1)

A bare repository stands for GitHub and two clones for machines A and B. The runs and the
preflight are replaced by functions that write a file, or that die as a container does.
"""
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import execute


def sh(*args, cwd=None):
    subprocess.run(args, cwd=cwd, check=True, capture_output=True)


class Died(BaseException):
    """The container is gone: nothing after the start of the run is written."""


class TwoMachines(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        t = Path(self.tmp.name)
        sh("git", "init", "-q", "--bare", "-b", "work", str(t / "origin.git"))
        seed = t / "seed"
        sh("git", "clone", "-q", str(t / "origin.git"), str(seed))
        root = seed / "research" / "sky130-layout"
        (root / "phase1").mkdir(parents=True)
        for p in execute.PINNED:
            (root / p).write_text(p + "\n")
        for c in (["config", "user.name", "t"], ["config", "user.email", "t@t"], ["checkout", "-q", "-b", "work"],
                  ["add", "."], ["commit", "-q", "-m", "seed"], ["push", "-q", "origin", "work"]):
            sh("git", *c, cwd=seed)
        self.t = t
        self.ran = []

    def tearDown(self):
        self.tmp.cleanup()

    def clone(self, name):
        d = self.t / name
        sh("git", "clone", "-q", "-b", "work", str(self.t / "origin.git"), str(d))
        sh("git", "config", "user.name", "t", cwd=d)
        sh("git", "config", "user.email", "t@t", cwd=d)
        return d / "research" / "sky130-layout"

    def runner(self, root, die_on=()):
        def run(name):
            if name in die_on:
                raise Died(name)
            self.ran.append(name)
            (root / "phase1" / "results_j" / f"{name}.csv").write_text("pulse\n")
            return name
        return run

    def go(self, machine, root, die_on=(), identical=True):
        execute.launch(machine, root=root, run_one=self.runner(root, die_on),
                       preflight=lambda: dict(identical=identical), go=True)

    def log(self):
        return subprocess.run(["git", "-C", str(self.t / "origin.git"), "log", "--format=%s", "work"],
                              capture_output=True, text=True).stdout.splitlines()[::-1]

    def test_nothing_without_go(self):
        with self.assertRaises(SystemExit):
            execute.launch("A", root=self.clone("a"), run_one=None, preflight=None, go=False)
        self.assertEqual(self.log(), ["seed"])

    def test_b_waits_for_the_marker_of_a(self):
        with self.assertRaises(SystemExit):
            self.go("B", self.clone("b"))
        self.assertEqual(self.ran, [])

    def test_marker_then_started_then_results(self):
        a = self.clone("a")
        self.go("A", a)
        log = self.log()
        self.assertTrue(log[1].startswith("Stage J: attempt marker"))
        self.assertLess(log.index("Stage J, machine A: started j1 j4 j5"), log.index("Stage J, machine A: results of j1 j4 j5"))
        b = self.clone("b")
        self.go("B", b)
        self.assertEqual(sorted(self.ran), ["j1", "j2", "j3", "j4", "j5", "j6"])
        marker = json.loads((b / "phase1" / "RUN_ATTEMPT_J.json").read_text())
        self.assertEqual(marker["attempt"], 1)
        self.assertEqual(marker["created_by_machine"], "A")

    def test_a_started_run_is_lost_and_never_run_again(self):
        a = self.clone("a")
        with self.assertRaises(Died):
            self.go("A", a, die_on=("j1", "j4", "j5"))
        self.assertEqual(self.ran, [])
        a2 = self.clone("a_after_restart")                     # a new container: a fresh checkout
        self.go("A", a2)
        self.assertEqual(self.ran, [])                         # nothing is run again
        for name in ("j1", "j4", "j5"):
            self.assertTrue((a2 / "phase1" / "results_j" / f"{name}.lost").exists())
        self.go("A", self.clone("a_third"))                    # and a third launch changes nothing
        self.assertEqual(self.ran, [])

    def test_a_run_never_started_may_proceed(self):
        a = self.clone("a")
        saved = execute.SLICE
        execute.SLICE = 1                                      # one run at a time: j1 ends, j4 dies, j5 never starts
        try:
            with self.assertRaises(Died):
                self.go("A", a, die_on=("j4",))
            a2 = self.clone("a_after_restart")
            self.go("A", a2)
        finally:
            execute.SLICE = saved
        self.assertEqual(self.ran, ["j1", "j5"])
        self.assertTrue((a2 / "phase1" / "results_j" / "j4.lost").exists())
        self.assertFalse((a2 / "phase1" / "results_j" / "j1.lost").exists())

    def test_a_machine_that_does_not_reproduce_the_nominal_run_runs_nothing(self):
        a = self.clone("a")
        with self.assertRaises(SystemExit):
            self.go("A", a, identical=False)
        self.assertEqual(self.ran, [])
        self.assertIn("Stage J: preflight of machine A", self.log())

    def test_a_changed_input_stops_the_launch(self):
        a = self.clone("a")
        self.go("A", a)
        b = self.clone("b")
        (b / "AMENDMENT_2.md").write_text("changed\n")
        sh("git", "commit", "-q", "-am", "edit", cwd=b)
        before = list(self.ran)
        with self.assertRaises(RuntimeError):
            self.go("B", b)
        self.assertEqual(self.ran, before)


if __name__ == "__main__":
    unittest.main()
