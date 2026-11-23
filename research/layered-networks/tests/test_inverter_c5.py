"""The layered deck's inverter (lcal2.py's config with config_inverter_c5.json) is the C5 cell of the inverter-instances
package at the network's directives (research/inverter-instances c5c06e00, invinst/netdeck.py with
config_netopts.json). No simulation.

The package is exported from git at c5c06e00 into a temporary folder and imported from there.

What must be equal, line for line:
  1. every device and element line of the inverter (main charge and leak, comparator and latch, help mirror and its
     switch, inhibitory mirror and its switch, reset gate, the bias source), after the network's subcircuit form;
  2. the help reference current (H0 unit / tu) and the inhibitory current (J0 unit / tu);
  3. the deck's directives: the `.lib` line, the six `.param` lines and the four `.option` lines;
  4. the inverter devices' junction areas: zero, as the PDK default the package leaves implicit.
Stated differences, by construction, each asserted in its exact form:
  - the stimulus: the package drives khelp, kinb, krst, krstb and the inhibitory reference by its own pulse sources;
    the network drives them from the router per slot (subcircuit ports khelp, kinb, krst, krstb, and the reference
    `bjref jg 0 i = J*v(kj)` with kj set to 1 for the input window, against `ijref jg 0 pulse(0 J ...)`);
  - the supply and reference sources (vdd, vr0, vfire, vreopen) and `.include blocks.spice` are the network's shared
    ones;
  - the transient's maximum step (5 ns / 20 ns in the package, 200 ns in the network), which is not a deck line.
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(HERE))
import instrument  # noqa: E402
import lcal2  # noqa: E402
import spec as specmod  # noqa: E402

COMMIT = "c5c06e00"
PKG = "research/circuit/inverter/instances"


def package(tmp):
    root = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=HERE, capture_output=True, text=True,
                          check=True).stdout.strip()
    tar = subprocess.run(["git", "archive", COMMIT, PKG], cwd=root, capture_output=True, check=True).stdout
    subprocess.run(["tar", "-x", "-C", tmp], input=tar, check=True)
    return Path(tmp) / PKG


def body(lines):
    """Element lines without comments and blank lines, whitespace normalised."""
    return [" ".join(l.split()) for l in lines if l.strip() and not l.startswith("*")]


DRIVE = ("vkhelp ", "vkinb ", "vkrst ", "vkrstb ", "ijref ", "vdd ", "vr0 ", "vfire ", "vreopen ", ".include ")


def main():
    cfg, _ = lcal2.config()
    s = specmod.load(HERE / "specs" / "xor3.json")
    with tempfile.TemporaryDirectory() as tmp:
        pkg = package(tmp)
        sys.path.insert(0, str(pkg))
        from invinst import netdeck
        c5 = json.loads((pkg / "design_sweep" / "C5_hm2x16.json").read_text())["cell"]
        netopts = json.loads((pkg / "config_netopts.json").read_text())
        theirs = netdeck.netlist(c5, netopts, present=True).splitlines()
    # the design values: config_inverter_c5.json equals C5 in every field the network uses
    for k in ("tau", "h", "hl", "H0", "J0", "D", "reset_len", "help_mirror", "inhib_mirror", "switch_n", "switch_p",
              "reset_n", "reset_p"):
        assert cfg["inverter"][k] == c5[k], k
    # 1, 2: the subcircuit body against the cell's lines
    h = instrument.deck_text_1x(s, cfg).splitlines()
    i = h.index(".subckt rinv vdd vr0 vfire vreopen khelp kinb kj krst krstb")
    j = h.index(".ends", i)
    ours = body(h[i + 1:j])
    cell = [l for l in body(theirs) if not l.startswith(DRIVE + (".lib", ".param", ".option", ".end"))]
    J = c5["J0"] * c5["cq_F"] * c5["vunit_V"] / c5["tu_s"]
    ours_cmp = [l for l in ours if not l.startswith("bjref ")]
    assert ours_cmp == cell, "\n".join(f"{a!r} | {b!r}" for a, b in zip(ours_cmp + [""] * 99, cell) if a != b)
    assert [l for l in ours if l.startswith("bjref ")] == [f"bjref jg 0 i = {J:.12g}*v(kj)"]
    ijref = [l for l in body(theirs) if l.startswith("ijref ")]
    assert len(ijref) == 1 and ijref[0].startswith(f"ijref jg 0 pulse(0 {J:.12g} "), ijref
    # 3: the directives of the run's deck (flattened, at the design point) against config_netopts.json
    t = instrument.deck_text(s, cfg).splitlines()
    lib = [l for l in t if l.startswith(".lib")]
    par = [l for l in t if l.startswith(".param")]
    opt = [l for l in t if l.startswith(".option")]
    assert lib == [netopts["section_line_mismatch"]], lib
    assert par == netopts["params"], (par, netopts["params"])
    assert opt == netopts["options"], (opt, netopts["options"])
    # 4: the inverter devices in the flattened deck carry zero areas
    invs = [l for l in t if l.lower().startswith(("xn0.", "xn1.")) and "sky130_fd_pr__" in l]
    assert invs and all(("ad=0 " in l or l.endswith("ad=0")) and "as=0" in l and "pd=0" in l and "ps=0" in l
                        for l in invs), invs[:3]
    print(f"ok: inverter subcircuit = C5 cell at {COMMIT} ({len(cell)} element lines), help I {c5['H0']} unit/tu, "
          f"inhib I {J:.4g} A; directives = config_netopts.json ({len(par)} .param, {len(opt)} .option); "
          f"{len(invs)} inverter devices at zero areas")


if __name__ == "__main__":
    main()
