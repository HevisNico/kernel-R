"""One inverter cell at transistor level (SKY130, ngspice 42): netlist, runs and contract measures.

Development work, not a preregistered campaign. The main charge, its leak, the FIRE comparator and the
protection latch are those of the frozen cell (research/circuit/cell.spice at ecfcd1c1, lines 129-154, noise
sources held at zero). The learning ports are removed. Added: a gated help sink (NMOS mirror), an inhibitory
input (PMOS mirror through a PMOS admission switch onto the main capacitor) and a reset switch to vr0.
Ammeters (0 V sources) sit in series with the help path and the inhibitory path at the main capacitor.

Sign conventions, in units of the cell's charge coordinate x = (vr0 - vq) / vunit (one unit = cq*vunit = 2.5 pC):
  help H(t)       = current through vah, out of the main capacitor: raises x (toward FIRE);
  inhibitory J(t) = current through vaj, into the main capacitor: lowers x.
"""
import hashlib, json, math, subprocess, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
TU = 20e-6
CQ, VUNIT, VR0 = 5e-12, 0.5, 1.25
UNIT = CQ * VUNIT                    # coulombs per unit of x
T0 = 10e-6                           # slot start, after 10 us of settling
LEVEL = 0.9                          # x at vfire

DESIGN = dict(                       # every design choice, in time units and units of x unless stated
    tau=0.25,                        # inhibitory admission window [0, tau]
    h=0.30, hl=0.30,                 # help window [h, h + hl]
    H0=4.5,                          # nominal help current, units per time unit (0.5625 uA)
    J0=3.0,                          # nominal inhibitory input current while present, units per time unit (0.375 uA)
    D=1.0,                           # slot length; reset of the main capacitor to vr0 on [D, D + 0.1]
    reset_len=0.1,
    help_mirror=dict(w=2, l=4), inhib_mirror=dict(w=4, l=4),
    switch_n=dict(w=1, l=0.15), switch_p=dict(w=2, l=0.15),
    reset_n=dict(w=1, l=0.15), reset_p=dict(w=2, l=0.15),   # iteration 2: a transmission gate (iteration 1 had the NMOS alone)
)


def netlist(present, help_on=True, reset=True, inhib_on=True, d=DESIGN):
    tu = TU
    s = lambda x: f"{T0 + x * tu:.12g}"
    ih = d["H0"] * UNIT / tu if help_on else 0.0
    ij = d["J0"] * UNIT / tu if (present and inhib_on) else 0.0
    edge = 1e-9
    hm, im, sn, sp = d["help_mirror"], d["inhib_mirror"], d["switch_n"], d["switch_p"]
    rn, rp = d["reset_n"], d["reset_p"]
    reset_line = (f"vkrst krst 0 pulse(0 1.8 {s(d['D'])} {edge} {edge} {d['reset_len'] * tu - edge:.12g} 1)\n"
                  f"vkrstb krstb 0 pulse(1.8 0 {s(d['D'])} {edge} {edge} {d['reset_len'] * tu - edge:.12g} 1)"
                  if reset else "vkrst krst 0 dc 0\nvkrstb krstb 0 dc 1.8")
    return f"""* inverter cell: help sink, inhibitory PMOS input, reset (development, not preregistered)
.lib "pdk/models/sky130.lib.spice" tt
.param vddv=1.8 tu=20u cq=5p vunit=0.5 vr0=1.25
.param vfire={{vr0 - 0.9*vunit}} vreopen={{vr0 - 0.1*vunit}}
.param rleak={{2*tu/cq}}
.option scale=1e-6
.option reltol=1e-4 abstol=1e-13 vntol=1e-7 chgtol=1e-17
.option gmin=1e-16
.include blocks.spice
vdd vdd 0 {{vddv}}
vr0 vr0 0 {{vr0}}
vfire vfire 0 {{vfire}}
vreopen vreopen 0 {{vreopen}}
ibm ibm 0 10u
* main charge: q = 0.1 at vr0, q = 1 at vfire, leak toward rest (frozen cell)
cq vq 0 {{cq}}
rleak vq vr0 {{rleak}}
* FIRE comparator with a switched reference and the protection latch (frozen cell, noise sources at zero)
vnzm nzm 0 dc 0
rnzm nzm 0 1k
bvrm vrefmn0 0 v = v(vrefm) + v(nzm)
rvrm vrefmn0 vrefmn 1k
cvrm vrefmn 0 20f
xcmpm vrefmn vq cmpm ibm vdd 0 comp wc=16 lc=4
xicm cmpm cmpmb vdd 0 inv
xnsp cmpm  pbdel sbp vdd 0 nand2
xnrp cmpmb pdel  rbp vdd 0 nand2
xlp sbp rbp p pb vdd 0 srlatch
rdp p pd1 100k
cdp pd1 0 2p
xip1 pd1 pbdel vdd 0 inv
xip2 pbdel pdel vdd 0 inv
xmm1n vrefm pb vfire   0   sky130_fd_pr__nfet_01v8 w=1 l=0.15
xmm1p vrefm p  vfire   vdd sky130_fd_pr__pfet_01v8 w=2 l=0.15
xmm2n vrefm p  vreopen 0   sky130_fd_pr__nfet_01v8 w=1 l=0.15
xmm2p vrefm pb vreopen vdd sky130_fd_pr__pfet_01v8 w=2 l=0.15
* help: NMOS mirror sinking from the main capacitor, gated by khelp on [h, h + hl]
ihref vdd hg dc {ih:.12g}
xmh1 hg hg 0 0 sky130_fd_pr__nfet_01v8 w={hm['w']} l={hm['l']}
xmh2 hd hg 0 0 sky130_fd_pr__nfet_01v8 w={hm['w']} l={hm['l']}
xsh hs khelp hd 0 sky130_fd_pr__nfet_01v8 w={sn['w']} l={sn['l']}
vah vq hs dc 0
vkhelp khelp 0 pulse(0 1.8 {s(d['h'])} {edge} {edge} {d['hl'] * tu - edge:.12g} 1)
* inhibitory input: PMOS mirror from vdd, its reference driven by the input pulse on [0, tau],
* admitted through a PMOS switch (gate kinb low) on [0, tau]
xmj1 jg jg vdd vdd sky130_fd_pr__pfet_01v8 w={im['w']} l={im['l']}
xmj2 jd jg vdd vdd sky130_fd_pr__pfet_01v8 w={im['w']} l={im['l']}
ijref jg 0 pulse(0 {ij:.12g} {s(0)} {edge} {edge} {d['tau'] * tu - edge:.12g} 1)
xsj jd kinb js vdd sky130_fd_pr__pfet_01v8 w={sp['w']} l={sp['l']}
vaj js vq dc 0
vkinb kinb 0 pulse(1.8 0 {s(0)} {edge} {edge} {d['tau'] * tu - edge:.12g} 1)
* reset of the main capacitor to vr0 after the slot: a transmission gate
xsrn vq krst vr0 0 sky130_fd_pr__nfet_01v8 w={rn['w']} l={rn['l']}
xsrp vq krstb vr0 vdd sky130_fd_pr__pfet_01v8 w={rp['w']} l={rp['l']}
{reset_line}
.option temp=27
.end
"""


def run(name, text, tstop, maxstep):
    folder = HERE / "runs" / name
    folder.mkdir(parents=True, exist_ok=True)
    pdk = folder / "pdk"
    if not pdk.exists():
        pdk.symlink_to(HERE / "pdk", target_is_directory=True)
    (folder / "blocks.spice").write_text((HERE / "blocks.spice").read_text())
    (folder / ".spiceinit").write_text((HERE / "spiceinit.txt").read_text())
    control = f"""
.control
set wr_singlescale
set wr_vecnames
option numdgt=12
tran 1n {tstop:.12g} 0 {maxstep}
wrdata trace.txt v(vq) i(vah) i(vaj) v(p) v(khelp) v(kinb) v(krst)
quit
.endc
"""
    deck = text.replace("\n.end\n", control + ".end\n")
    (folder / "input.spice").write_text(deck)
    out = subprocess.run(["ngspice", "-b", "input.spice"], cwd=folder, capture_output=True, text=True, timeout=3600)
    (folder / "ngspice.log").write_text(out.stdout + out.stderr)
    if out.returncode or not (folder / "trace.txt").exists():
        raise RuntimeError(out.stdout[-3000:] + out.stderr[-3000:])
    data = np.loadtxt(folder / "trace.txt", skiprows=1)
    return folder, data


def integral(t, y, a, b):
    """Trapezoidal integral of y over [a, b], with the end points interpolated."""
    grid = np.concatenate(([a], t[(t > a) & (t < b)], [b]))
    vals = np.interp(grid, t, y)
    return float(np.trapezoid(vals, grid))


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
