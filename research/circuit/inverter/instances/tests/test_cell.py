"""The package's deck is the pushed cell's, byte for byte, at section tt (research/circuit/inverter/inverter.py)."""
import itertools, sys, unittest
from pathlib import Path

PKG = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PKG))
sys.path.insert(0, str(PKG.parent))
from invinst import cell, driver
import inverter as pushed


class Cell(unittest.TestCase):
    def test_identical_to_pushed_cell(self):
        c = driver.load_config()["cell"]
        for present, help_on, reset in itertools.product((False, True), repeat=3):
            self.assertEqual(cell.netlist(c, present, help_on=help_on, reset=reset),
                             pushed.netlist(present, help_on=help_on, reset=reset))

    def test_section_and_ramp_only_additions(self):
        c = driver.load_config()["cell"]
        ramp = driver.load_config()["runs"]["R5_static"]["ramp"]
        a = cell.netlist(c, False, help_on=False, reset=False).splitlines()
        b = cell.netlist(c, False, help_on=False, reset=False, section="tt_mm", ramp=ramp).splitlines()
        diff = [l for l in b if l not in a]
        self.assertEqual(len(diff), 3)
        self.assertTrue(diff[0].endswith(" tt_mm") and diff[1].startswith("vforce ") and diff[2] == "rforce vfn vq 1")


if __name__ == "__main__":
    unittest.main()
