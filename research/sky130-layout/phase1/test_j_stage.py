"""The analysis of stage J, run on committed results of the schematic.

  python3 -B -m unittest test_j_stage        (from research/sky130-layout/phase1)

No simulation. The verdict functions are given the campaign's own runs in the place of the runs
of stage J: `nom` for J1, `pvt_tt_125` for J2, `refresh_none` for J3, `refresh_lk11` for J4, and
`refresh_none` again for J5 and J6. The schematic at 27 C must satisfy JA to JF; the schematic at
125 C, which has no junction area, must fail JG, JH and JI.
"""
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import j_stage


class Schematic(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        sys.path.insert(0, str(j_stage.CIRCUIT))
        import analyze
        cls.analyze = analyze
        stand_in = dict(j1="nom", j2="pvt_tt_125", j3="refresh_none", j4="refresh_lk11", j5="refresh_none", j6="refresh_none")
        cls.runs = {k: analyze.read_run(j_stage.CIRCUIT / "results" / f"{v}.csv")[0] for k, v in stand_in.items()}
        saved = j_stage.RESULTS
        j_stage.RESULTS = HERE / "no_such_folder"            # no .restfire file is looked up in results_j
        cls.V = {k: (s, m) for k, t, s, m in j_stage.verdicts(cls.runs, {k: None for k in cls.runs}, analyze)}
        j_stage.RESULTS = saved

    def test_schematic_at_27(self):
        for key in ("JA", "JB", "JC", "JD", "JE", "JF", "JJ", "JL", "JM"):
            self.assertEqual(self.V[key][0], j_stage.HOLDS, (key, self.V[key][1]))

    def test_schematic_at_125_has_no_drift(self):
        for key in ("JG", "JH", "JI"):
            self.assertEqual(self.V[key][0], j_stage.FAILS, (key, self.V[key][1]))
        self.assertIn("7 silent pulses", self.V["JH"][1])

    def test_no_relapse_fails_a_refresh_prediction(self):
        self.assertEqual(self.V["JK"][0], j_stage.FAILS)

    def test_a_missing_run_is_not_evaluable(self):
        runs = dict(self.runs, j2=None)
        saved = j_stage.RESULTS
        j_stage.RESULTS = HERE / "no_such_folder"
        V = {k: s for k, t, s, m in j_stage.verdicts(runs, {k: "run failed" for k in runs}, self.analyze)}
        j_stage.RESULTS = saved
        for key in ("JG", "JH", "JI", "JJ", "JM"):
            self.assertEqual(V[key], j_stage.NA)
        self.assertEqual(V["JA"], j_stage.HOLDS)


if __name__ == "__main__":
    unittest.main()
