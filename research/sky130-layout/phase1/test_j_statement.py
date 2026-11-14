"""The four cases of the statement of stage J. No simulation.

  python3 -B -m unittest test_j_statement
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import j_statement as s


class Statement(unittest.TestCase):
    def test_cases(self):
        self.assertIs(s.statement(dict(JK="holds", JL="holds")), s.ARTIFACT)
        self.assertIs(s.statement(dict(JK="fails", JL="holds")), s.NOT_CARRIED)
        self.assertIs(s.statement(dict(JK="fails", JL="fails")), s.NOT_CARRIED)
        self.assertIs(s.statement(dict(JK="holds", JL="fails")), s.NOT_THE_AREAS)
        self.assertIs(s.statement(dict(JK="not evaluable", JL="holds")), s.NOT_EVALUABLE)
        self.assertIs(s.statement(dict(JK="holds", JL="not evaluable")), s.NOT_EVALUABLE)

    def test_artifact_is_claimed_in_one_case_only(self):
        for text in (s.NOT_CARRIED, s.NOT_THE_AREAS, s.NOT_EVALUABLE):
            self.assertNotIn("was an artifact", text)
        self.assertIn("was an artifact of netlists without junction areas", s.ARTIFACT)


if __name__ == "__main__":
    unittest.main()
