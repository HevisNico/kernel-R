"""Tests of the plan, the launcher and the analysis of stage P. No simulation.

  python3 -B -m unittest test_p_stage         (from research/sky130-layout/phase1)

The analysis is tried on the committed results of the schematic: with the constants of the
campaign, the scripts of the campaigns run in the mirror must give again, for the eight cells of
stage P, the committed need, gap and status 3 of each port.
"""
import json
import shutil
import tempfile
import unittest
from pathlib import Path

import p_analyze
import p_execute
import p_plan

CIRCUIT = p_analyze.CIRCUIT


def schematic_results(folder):
    """The committed results of the schematic, under the names of the runs of stage P."""
    cert, unc = CIRCUIT / "certification" / "results", CIRCUIT / "certification-unconditional" / "results"
    for q in p_plan.queues().values():
        for r in q:
            if r["analysis"] != "primary" or r["tool"] == "circuit":
                continue
            src = (cert if r["tool"] == "cert" else unc) / r["stage"]
            name = r["name"]
            if not (src / f"{name}.json").exists():
                continue                                # the campaigns have no nom_read and no calibration scan of 5002
            shutil.copy(src / f"{name}.json", folder / f"{name}.json")
            if r["mode"] == "ramp":
                level = json.loads((src / f"{name}.json").read_text())["static_level"]
                (folder / f"{name}.csv").write_text("static_level\n%.12g\n" % level)
            else:
                for ext in ("csv", "charge.csv", "early.csv"):
                    if (src / f"{name}.{ext}").exists():
                        shutil.copy(src / f"{name}.{ext}", folder / f"{name}.{ext}")
    for name, ref in (("nom_cell", "nom"), ("nom_refresh", "refresh_lk11"), ("nom_cell125", "pvt_tt_125")):
        shutil.copy(CIRCUIT / "results" / f"{ref}.csv", folder / f"{name}.csv")


class Plan(unittest.TestCase):
    def test_queues(self):
        q = p_plan.queues()
        names = [r["name"] for m in q for r in q[m]]
        self.assertEqual(len(names), len(set(names)))
        self.assertEqual((len(q["A"]), len(q["B"])), (37, 35))
        for m in q:
            primary = [r for r in q[m] if r["analysis"] == "primary"]
            self.assertTrue(all(r["analysis"] == "secondary" for r in q[m][len(primary):]))     # secondary runs come last
        cells = {m: [r["seed"] for r in q[m] if r["name"].endswith("_train") and r["noise"]] for m in q}
        self.assertEqual(cells, p_plan.CELLS)
        self.assertEqual(sorted(cells["A"] + cells["B"]), sorted(p_plan.LARGE + p_plan.SMALL))
        for m in q:                                         # each machine: two cells of large room, two of small
            self.assertEqual(sum(s in p_plan.LARGE for s in cells[m]), 2)
        self.assertEqual(len({r["noise_id"] for m in q for r in q[m] if r.get("noise_id")}), 8)

    def test_units_are_whole_and_in_order(self):
        for m, q in p_plan.queues().items():
            names = [r["name"] for r in q]
            for seed in p_plan.CELLS[m]:
                unit = [f"t{seed}_ramp", f"t{seed}_read", f"u{seed}_leak", f"u{seed}_train", f"t{seed}_train"]
                k = names.index(unit[0])
                self.assertEqual(names[k:k + 5], unit)

    def test_launcher(self):
        ex = p_execute.execute
        before = (ex.STAGE, ex.SPLIT, ex.PINNED)
        try:
            p_execute.configure()
            self.assertEqual(ex.STAGE, "P")
            self.assertEqual(ex.SPLIT, p_execute.QUEUES)
            root = p_execute.HERE.parent
            self.assertTrue(all((root / p).exists() for p in p_execute.PINNED))
            self.assertEqual(set(ex.marker_content(root, "A")["sha256"]), set(p_execute.PINNED))
            with self.assertRaises(SystemExit):
                ex.launch("B", go=False)
        finally:
            ex.STAGE, ex.SPLIT, ex.PINNED = before


class Analysis(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp())
        (cls.tmp / "results").mkdir()
        schematic_results(cls.tmp / "results")
        cls.data = p_analyze.Data(cls.tmp / "results")
        cls.ref = p_analyze.schematic_reference()
        cls.P = p_analyze.pipeline(cls.data, cls.tmp / "mirror", "campaign")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_scripts_ran(self):
        self.assertEqual({k: v[0] for k, v in self.P["log"].items()}, dict(predict=0, certify=0, uncond=0, amend1=0))

    def test_committed_values_come_back(self):
        for cell in p_analyze.CELLS:
            for port in (1, 2):
                key = (cell, port)
                self.assertEqual(self.P["predictions"][key]["m"], self.ref["predictions"][key]["m"], key)
                self.assertAlmostEqual(float(self.P["predictions"][key]["gap"]), float(self.ref["predictions"][key]["gap"]), 12)
                self.assertEqual(self.P["ports"][key]["count"], self.ref["ports"][key]["count"], key)
                self.assertEqual(self.P["amended"][key]["status3"], self.ref["amended"][key]["status3"], key)
                # the room differs a little: the allowance eps of cert_analyze.certify is the largest over the
                # noisy test runs it is given, 8 here and 100 in the campaign
                if self.ref["amended"][key]["room3"]:
                    self.assertAlmostEqual(float(self.P["amended"][key]["room3"]), float(self.ref["amended"][key]["room3"]), delta=0.001)

    def test_verdicts_on_the_schematic(self):
        V, X = p_analyze.verdicts(self.data, self.P, self.ref)
        v = {k: s for k, t, s, m in V}
        self.assertEqual(len(V), 13)
        self.assertEqual(len(X["ports"]), 16)
        for k in ("L1", "L2", "L3", "L4", "L6", "L7", "L9", "L11", "L12"):     # the schematic against itself
            self.assertEqual(v[k], p_analyze.HOLDS, k)
        self.assertEqual(v["L13"], p_analyze.NA)            # no schematic refresh at 125 °C is committed
        self.assertEqual(v["L5"], p_analyze.NA)             # runs are missing: the guard cannot be judged
        large = [self.P["amended"][k]["status3"] for k in p_analyze.LARGE]
        self.assertTrue(all(s.startswith("certified") for s in large))

    def test_report_is_written(self):
        V = p_analyze.report(self.tmp / "results", self.tmp / "REPORT.md", self.tmp / "work")
        text = (self.tmp / "REPORT.md").read_text()
        self.assertEqual(len(V), 13)
        self.assertIn("The campaign is truncated", text)
        self.assertNotIn(p_analyze.SENTENCE, text)          # L13 is not evaluable on these results
        self.assertEqual(sum(l.startswith("| `t6") and "(machine" not in l for l in text.splitlines()), 16)

    def test_rule_a1_runs(self):
        a1 = self.P["a1"]
        self.assertEqual(len(a1), 16)
        self.assertTrue(any(r["eligible"] for r in a1.values()))
        self.assertFalse(any(r["contradicted"] for r in a1.values()))


if __name__ == "__main__":
    unittest.main()
