"""The inverter's deck at the layered network's simulator directives (config_netopts.json).

The circuit is cell.netlist's, unchanged (cell.py stays as pushed). Only the directive lines change: the deck's own
`.lib`, `.param` and `.option` lines are removed, and the network's are put in their place, in the network's order:
`.lib` and the `.param` lines after the title, the `.option` lines (scale, reltol 1e-5 ..., gmin, temp) before
`.end`. Inverter devices keep no junction area: the network gives them zero areas, which is the PDK subcircuits'
own default. tests/test_netopts.py checks the directives against research/layered-networks at a308eec.
"""
from . import cell

DIRECTIVES = (".lib", ".param", ".option")


def netlist(c, netopts, present, help_on=True, reset=True, inhib_on=True, nominal=False, ramp=None):
    if c["level_x"] != 0.9:
        raise ValueError("the network's .param line fixes vfire at vr0 - 0.9*vunit")
    base = cell.netlist(c, present, help_on=help_on, reset=reset, inhib_on=inhib_on, section="tt", ramp=ramp)
    lines = base.splitlines()
    assert lines[0].startswith("*") and lines[-1] == ".end"
    body = [l for l in lines[1:-1] if not l.startswith(DIRECTIVES)]
    lib = netopts["section_line_mismatch"]
    if nominal:
        lib = lib.rsplit(" ", 1)[0] + " " + netopts["nominal_section"]
    out = [lines[0], lib] + netopts["params"] + body + netopts["options"] + [".end"]
    return "\n".join(out) + "\n"


def directives(text):
    return [l.strip() for l in text.splitlines() if l.startswith(DIRECTIVES)]
