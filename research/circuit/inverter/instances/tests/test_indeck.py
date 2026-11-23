"""The in-deck runs change only the listed lines of the network's deck: python -B -m unittest tests/test_indeck.py

research/layered-networks at 8af2cba is exported read-only (git archive); its instrument.deck_text at the C5 overlay
builds the XOR3 deck. For every run of every inverter, the test checks:
  1. the deck's inverter is the configured cell (check_design), and a changed help mirror is refused;
  2. the changed lines are exactly that inverter's five drives, its help reference when help is off, and the two
     forcing lines of the static run before .end; everything else is the network's text, in order.
"""
import difflib, json, subprocess, sys, tempfile, unittest
from pathlib import Path

PKG = Path(__file__).resolve().parents[1]
REPO = PKG.parents[3]
sys.path.insert(0, str(PKG))
from invinst import driver, indeck

COMMIT = "8af2cba"


def xor3_deck():
    tmp = Path(tempfile.mkdtemp())
    tar = subprocess.run(["git", "-C", str(REPO), "archive", COMMIT, "research"], capture_output=True,
                         check=True)
    subprocess.run(["tar", "-x", "-C", str(tmp)], input=tar.stdout, check=True)
    code = ("import sys\nsys.path.insert(0,'.')\nimport lcal2, instrument, spec\n"
            "cfg,_ = lcal2.config('config_inverter_c5.json')\n"
            "sys.stdout.write(instrument.deck_text(spec.load('specs/xor3.json'), cfg))\n")
    p = subprocess.run([sys.executable, "-B", "-c", code], cwd=tmp / "research" / "layered-networks",
                       capture_output=True, text=True, check=True)
    return p.stdout


class InDeck(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.text = xor3_deck()
        cls.cfg = driver.load_config()

    def test_design(self):
        c = self.cfg["cell"]
        for inv in ("n0", "n1"):
            indeck.check_design(self.text, inv, c)
        with self.assertRaises(ValueError):
            indeck.check_design(self.text, "n0", dict(c, help_mirror=dict(w=2, l=4)))

    def test_only_listed_lines_change(self):
        c = self.cfg["cell"]
        for inv in ("n0", "n1"):
            for name, r in self.cfg["runs"].items():
                new = indeck.run_deck(self.text, inv, c, r)
                a, b = self.text.splitlines(), new.splitlines()
                gone, added = [], []
                for op in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
                    if op[0] != "equal":
                        gone += a[op[1]:op[2]]
                        added += b[op[3]:op[4]]
                want = [f"vk{k}{inv} " for k in "hijrb"] + ([] if r["help"] else [f"i.x{inv}.ihref "])
                self.assertEqual(sorted(l.split()[0] + " " for l in gone), sorted(want), (inv, name))
                extra = [l for l in added if not any(l.startswith(w) for w in want)]
                self.assertEqual(extra, [f"vforce{inv} vfn{inv} 0 pwl(" + extra[0].split("pwl(")[1],
                                         f"rforce{inv} vfn{inv} x{inv}.vq 1"] if r.get("ramp") else [], (inv, name))
                self.assertEqual(b[-1], ".end")
                self.assertEqual(len(b), len(a) + (2 if r.get("ramp") else 0))


if __name__ == "__main__":
    unittest.main()
