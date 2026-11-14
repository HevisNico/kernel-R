"""Does a mismatch seed give the same devices after parasitics are added? (simulation, exploratory)

Three diode-connected devices carry 1 uA; their gate voltages show their mismatch sample.
  A  reference deck
  B  A with source/drain areas on the instances and parasitic R and C appended after the devices
  C  A with the device lines in another order (what a raw extracted netlist does)
  D  A with one device split in two parallel fingers placed first (what finger extraction does)
"""
import subprocess
DEV = {"x1": "x1 g1 g1 0 0 sky130_fd_pr__nfet_01v8 w=40 l=2.5",
       "x2": "x2 g2 g2 0 0 sky130_fd_pr__nfet_01v8 w=4 l=2",
       "x3": "x3 vdd g3 g3 vdd sky130_fd_pr__pfet_01v8_lvt w=16 l=1"}
AREAS = " ad=0.29 as=0.29 pd=2.58 ps=2.58"
PARA = ["cp1 g1 0 5f", "cp2 g2 g1 1f", "rp1 g3 g3x 50", "cp3 g3x 0 2f"]
def deck(lines, seed):
    return "\n".join(["* mismatch identity", '.lib "pdk/models/sky130.lib.spice" tt_mm', ".option scale=1e-6",
                      "vdd vdd 0 1.8", "i1 vdd g1 1u", "i2 vdd g2 1u", "i3 g3 0 1u"] + lines +
                     [".control", f"setseed {seed}", "reset", "op", "set numdgt=10",
                      "echo RES $&v(g1) $&v(g2) $&v(g3)", "quit", ".endc", ".end"]) + "\n"
cases = {"A": [DEV["x1"], DEV["x2"], DEV["x3"]],
         "B": [DEV["x1"] + AREAS, DEV["x2"] + AREAS, DEV["x3"] + AREAS] + PARA,
         "C": [DEV["x3"], DEV["x1"], DEV["x2"]],
         "D": ["x1a g1 g1 0 0 sky130_fd_pr__nfet_01v8 w=20 l=2.5", "x1b g1 g1 0 0 sky130_fd_pr__nfet_01v8 w=20 l=2.5",
               DEV["x2"], DEV["x3"]]}
print("seed,case,v_g1,v_g2,v_g3")
for seed in (6002, 6065):
    for name, lines in cases.items():
        open(f"mm_{name}.spice", "w").write(deck(lines, seed))
        out = subprocess.run(["ngspice", "-b", f"mm_{name}.spice"], capture_output=True, text=True).stdout
        res = [l for l in out.splitlines() if l.startswith("RES ")]
        print(f"{seed},{name}," + (",".join(res[0].split()[1:]) if res else "FAILED"))
