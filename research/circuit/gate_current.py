"""The charge that the integrator really receives in each period. Part of the complement.

  gate_current.py NAME SECTION [seed=S] [nz=1] [temp=T]

P10 checks the steering command: on a firing pulse the switch to the integrator is never turned
on. This run measures the current itself. An ammeter (a source of 0 V) is put between the
steering switch and the summing node of each integrator, and its current is integrated over
each whole period, from the time points of the solver. Nothing else is changed in the netlist.

Writes results_gate/NAME.csv, one row per pulse: the pulse, the port that receives it (0: both),
whether the cell fired, the charge received by each integrator in fC, and the change of each
stored voltage in mV. A charge Q on the feedback capacitor of 30 pF moves the stored voltage by Q / 30 pF.
"""
import json, os, subprocess, sys

TU, TPER, T0, K = 20e-6, 440e-6, 4.1e-6, 10
name, section = sys.argv[1], sys.argv[2]
opt = dict(seed=None, nz="0", temp=None)
opt.update(e.split("=") for e in sys.argv[3:])
text = open("cell.spice").read()
switch = "xmsi x si sum 0 sky130_fd_pr__nfet_01v8 w=1 l=0.15"
assert text.count(switch) == 1
text = text.replace(switch, switch.replace(" sum 0 ", " sumi 0 ") + "\nvamm sumi sum 0")
if opt["nz"] == "1":
    z = json.load(open("noise.json"))["params"]
    for node, white, flicker in (("nzc", z["vncw"], z["vncf"]), ("nzo", z["vnow"], z["vnof"]), ("nzi", z["inmw"], 0.0), ("nzm", z["vnmw"], z["vnmf"])):
        old = f"vnz{node[2]} {node} 0 dc 0"
        assert old in text
        text = text.replace(old, f"{old} trnoise({white:.6g} {z['tnz']:.6g} {1 if flicker else 0} {flicker:.6g})")
n = 2 * K + 2
lines = [f"* {name}", f'.lib "pdk/models/sky130.lib.spice" {section}'] + text.splitlines()[1:-1] + [f".param kp={K}"]
if opt["temp"]:
    lines.append(f".option temp={opt['temp']}")
lines.append(".save v(vmem1) v(vmem2) v(p) i(v.x1.vamm) i(v.x2.vamm)")
os.makedirs("work", exist_ok=True); os.makedirs("results_gate", exist_ok=True)
path, data = f"work/gate_{name}.spice", f"work/gate_{name}.txt"
ctl = [".control"] + ([f"setseed {opt['seed']}", "reset"] if opt["seed"] else []) + [
    f"tran 1u {n * TPER:.9g} 0 200n", "set wr_singlescale", "set numdgt=12", f"wrdata {data} v(p) v(vmem1) v(vmem2) i(v.x1.vamm) i(v.x2.vamm)", "quit", ".endc", ".end"]
open(path, "w").write("\n".join(lines + ctl) + "\n")
p = subprocess.run(["ngspice", "-b", path], capture_output=True, text=True)
log = p.stdout + p.stderr
pts = [[float(x) for x in l.split()] for l in open(data)] if os.path.exists(data) else []
if not pts or pts[-1][0] < n * TPER * 0.999 or "aborted" in log or "too small" in log:
    open(f"results_gate/{name}.failed", "w").write(log[-3000:])
    print(name, "FAILED")
    sys.exit(1)

def integral(col, a, b):
    """Trapezoid over the time points of the solver between a and b: the rule of the solver itself.
    The current of the ammeter alternates in sign from one point to the next, a known effect of
    trapezoidal integration. Its trapezoid sum is the charge. The integ command of the simulator
    gives other values on such a current and is not used."""
    s = span = 0.0
    for u, v in zip(pts, pts[1:]):
        if u[0] >= a and v[0] <= b:
            s += (v[0] - u[0]) * (u[col] + v[col]) / 2
            span += v[0] - u[0]
    return s, span

rows, prev = [], None
for k in range(n):
    a0, b = k * TPER + (2.6e-6 if k == 0 else 0.05e-6), (k + 1) * TPER - 2e-6
    fired = any(u[1] < 0.9 <= v[1] for u, v in zip(pts, pts[1:]) if a0 <= u[0] and v[0] <= b)
    v = [s / span for s, span in (integral(c, b - 40e-6, b) for c in (2, 3))]
    if k > 0:
        port = 1 if k <= K else (2 if k <= 2 * K else 0)
        rows.append((k - 1, port, int(fired), 1e15 * integral(4, k * TPER, (k + 1) * TPER)[0], 1e15 * integral(5, k * TPER, (k + 1) * TPER)[0],
                     1e3 * (prev[0] - v[0]), 1e3 * (prev[1] - v[1])))
    prev = v
os.remove(data)
with open(f"results_gate/{name}.csv", "w") as fh:
    fh.write("pulse,port,fired,charge1_fC,charge2_fC,step1_mV,step2_mV\n")
    for r in rows:
        fh.write("%d,%d,%d,%.5f,%.5f,%.5f,%.5f\n" % r)
print(name, "pulses", len(rows), "of", n - 1)
