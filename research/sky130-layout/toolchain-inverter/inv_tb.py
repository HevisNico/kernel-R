"""Schematic against extracted inverter, same bench, same models (simulation, typical corner, 27 C)."""
import re, subprocess, sys
BLOCKS = sys.argv[1]                       # research/circuit/blocks.spice
def deck(dut_include, dut_line):
    return f"""* inverter bench
.lib "pdk/models/sky130.lib.spice" tt
.option scale=1e-6
.include {BLOCKS}
{dut_include}
vdd vdd 0 1.8
vdut vddd 0 1.8
vin in 0 pulse(0 1.8 1n 50p 50p 2n 4n)
xdrv in a vdd 0 inv
{dut_line}
xload y z vdd 0 inv
.control
tran 1p 9n
meas tran tphl trig v(a) val=0.9 rise=1 targ v(y) val=0.9 fall=1
meas tran tplh trig v(a) val=0.9 fall=1 targ v(y) val=0.9 rise=1
meas tran qdd integ i(vdut) from=5n to=9n
echo RES $&tphl $&tplh $&qdd
quit
.endc
.end
"""
cases = [("schematic", "", "xdut a y vddd 0 inv"),
         ("extracted_c", ".include inv_pex_c.spice", "xdut a y vddd 0 inv_pex"),
         ("extracted_rc", ".include inv_pex_rc.spice", "xdut a y vddd 0 inv_pex")]
print("case,tphl_ps,tplh_ps,energy_per_cycle_fJ")
for name, inc, line in cases:
    open(f"tb_{name}.spice", "w").write(deck(inc, line))
    out = subprocess.run(["ngspice", "-b", f"tb_{name}.spice"], capture_output=True, text=True)
    res = [l for l in out.stdout.splitlines() if l.startswith("RES ")]
    if not res:
        print(name, "FAILED"); print(out.stdout[-2000:], out.stderr[-2000:]); continue
    tphl, tplh, q = map(float, res[0].split()[1:])
    print(f"{name},{tphl * 1e12:.3f},{tplh * 1e12:.3f},{-q * 1.8 * 1e15:.4f}")
