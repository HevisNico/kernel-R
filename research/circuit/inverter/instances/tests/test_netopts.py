"""The inverter's directives equal the layered network's: python -B -m unittest tests/test_netopts.py

research/layered-networks at a308eec is exported read-only into a temporary folder (git archive). Its own deck builder,
instrument.deck_text at the calibration.json design point, builds the deck of every spec that has inverters. The test
checks:
  1. config_netopts.json holds exactly that deck's .lib, .param and .option lines, in order;
  2. netdeck.netlist gives the same directive lines, in the same order, for every run of the instance;
  3. netdeck.netlist changes nothing else: its other lines are cell.netlist's, in order;
  4. the network's inverter devices carry zero junction areas, the PDK default that netdeck leaves implicit.
"""
import json, subprocess, sys, tempfile, unittest
from pathlib import Path

PKG = Path(__file__).resolve().parents[1]
REPO = PKG.parents[3]
sys.path.insert(0, str(PKG))
from invinst import cell, driver, netdeck

COMMIT = "a308eec"
NETOPTS = json.loads((PKG / "config_netopts.json").read_text())


def network_decks():
    tmp = Path(tempfile.mkdtemp())
    tar = subprocess.run(["git", "-C", str(REPO), "archive", COMMIT, "research"], capture_output=True, check=True)
    subprocess.run(["tar", "-x", "-C", str(tmp)], input=tar.stdout, check=True)
    ln = tmp / "research" / "layered-networks"
    code = ("import json,sys\nsys.path.insert(0,'.')\nimport instrument, spec, deck\n"
            "cfg=json.load(open('config.json'))\nout={}\n"
            "for n in ('not1','andor3','xor3'):\n s=spec.load('specs/'+n+'.json')\n"
            " if deck.names(s)[1]: out[n]=instrument.deck_text(s,cfg)\nprint(json.dumps(out))\n")
    p = subprocess.run([sys.executable, "-B", "-c", code], cwd=ln, capture_output=True, text=True, check=True)
    return json.loads(p.stdout)


class NetOpts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.decks = network_decks()
        cls.cfg = driver.load_config()

    def test_config_is_the_network_directives(self):
        self.assertTrue(self.decks)
        want = [NETOPTS["section_line_mismatch"]] + NETOPTS["params"] + NETOPTS["options"]
        for name, text in self.decks.items():
            self.assertEqual(netdeck.directives(text), want, name)

    def test_inverter_deck_directives_identical(self):
        theirs = netdeck.directives(next(iter(self.decks.values())))
        c = self.cfg["cell"]
        for r in self.cfg["runs"].values():
            mine = netdeck.netlist(c, NETOPTS, r["present"], help_on=r["help"], reset=r["reset"], ramp=r.get("ramp"))
            self.assertEqual(netdeck.directives(mine), theirs)

    def test_only_directives_change(self):
        c = self.cfg["cell"]
        for r in self.cfg["runs"].values():
            kw = dict(help_on=r["help"], reset=r["reset"], ramp=r.get("ramp"))
            a = [l for l in cell.netlist(c, r["present"], section="tt_mm", **kw).splitlines()
                 if not l.startswith(netdeck.DIRECTIVES)]
            b = [l for l in netdeck.netlist(c, NETOPTS, r["present"], **kw).splitlines()
                 if not l.startswith(netdeck.DIRECTIVES)]
            self.assertEqual(a, b)

    def test_network_inverters_have_zero_areas(self):
        for name, text in self.decks.items():
            inv = [l for l in text.splitlines() if l.split() and l.split()[0].startswith("xn")
                   and "sky130_fd_pr__" in l]
            self.assertTrue(inv, name)
            for l in inv:
                self.assertIn("ad=0 as=0 pd=0 ps=0", l, (name, l))


if __name__ == "__main__":
    unittest.main()
