"""The inverter cell's deck, from the package config.

The circuit is the inverter cell of research/circuit/inverter (iteration 2): the main charge, its leak, the FIRE
comparator and the protection latch of the frozen cell (research/circuit/cell.spice at ecfcd1c1, lines 129-154,
noise sources at zero), a gated help sink (NMOS mirror), an inhibitory input (PMOS mirror through a PMOS admission
switch) and a transmission-gate reset to vr0. tests/test_cell.py checks that, at the section `tt` and with the same
design, this text is byte-identical to the pushed cell's (research/circuit/inverter/inverter.py at 062a2862).

Two additions, both outside the cell: the model section (`tt_mm` for an instance), and, for the static run only, an
ideal source driving the main node through 1 ohm.
"""
UNIT_NAMES = ("tau", "h", "hl", "H0", "J0", "D", "reset_len")


def unit_coulombs(c):
    return c["cq_F"] * c["vunit_V"]


def netlist(c, present, help_on=True, reset=True, inhib_on=True, section="tt", ramp=None):
    tu, t0, unit = c["tu_s"], c["settle_s"], unit_coulombs(c)
    s = lambda x: f"{t0 + x * tu:.12g}"
    ih = c["H0"] * unit / tu if help_on else 0.0
    ij = c["J0"] * unit / tu if (present and inhib_on) else 0.0
    edge = c["edge_s"]
    hm, im, sn, sp = c["help_mirror"], c["inhib_mirror"], c["switch_n"], c["switch_p"]
    rn, rp = c["reset_n"], c["reset_p"]
    reset_line = (f"vkrst krst 0 pulse(0 1.8 {s(c['D'])} {edge} {edge} {c['reset_len'] * tu - edge:.12g} 1)\n"
                  f"vkrstb krstb 0 pulse(1.8 0 {s(c['D'])} {edge} {edge} {c['reset_len'] * tu - edge:.12g} 1)"
                  if reset else "vkrst krst 0 dc 0\nvkrstb krstb 0 dc 1.8")
    force = ""
    if ramp is not None:
        pwl = (f"0 {c['vr0_V']} {s(0)} {c['vr0_V']} {s(ramp['lead_tu'])} {ramp['v_hi']} "
               f"{s(ramp['lead_tu'] + ramp['ramp_tu'])} {ramp['v_lo']}")
        force = f"vforce vfn 0 pwl({pwl})\nrforce vfn vq 1\n"
    return f"""* inverter cell: help sink, inhibitory PMOS input, reset (development, not preregistered)
.lib "pdk/models/sky130.lib.spice" {section}
.param vddv={c['vdd_V']:g} tu={tu * 1e6:g}u cq={c['cq_F'] * 1e12:g}p vunit={c['vunit_V']:g} vr0={c['vr0_V']:g}
.param vfire={{vr0 - {c['level_x']:g}*vunit}} vreopen={{vr0 - 0.1*vunit}}
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
vkhelp khelp 0 pulse(0 1.8 {s(c['h'])} {edge} {edge} {c['hl'] * tu - edge:.12g} 1)
* inhibitory input: PMOS mirror from vdd, its reference driven by the input pulse on [0, tau],
* admitted through a PMOS switch (gate kinb low) on [0, tau]
xmj1 jg jg vdd vdd sky130_fd_pr__pfet_01v8 w={im['w']} l={im['l']}
xmj2 jd jg vdd vdd sky130_fd_pr__pfet_01v8 w={im['w']} l={im['l']}
ijref jg 0 pulse(0 {ij:.12g} {s(0)} {edge} {edge} {c['tau'] * tu - edge:.12g} 1)
xsj jd kinb js vdd sky130_fd_pr__pfet_01v8 w={sp['w']} l={sp['l']}
vaj js vq dc 0
vkinb kinb 0 pulse(1.8 0 {s(0)} {edge} {edge} {c['tau'] * tu - edge:.12g} 1)
* reset of the main capacitor to vr0 after the slot: a transmission gate
xsrn vq krst vr0 0 sky130_fd_pr__nfet_01v8 w={rn['w']} l={rn['l']}
xsrp vq krstb vr0 vdd sky130_fd_pr__pfet_01v8 w={rp['w']} l={rp['l']}
{reset_line}
{force}.option temp={c['temp_C']}
.end
"""
