"""Run the cell and write one row per pulse.

  run.py cell NAME SECTION [kp=10] [options]
      one period at rest, K pulses on port 1, K pulses on port 2, then one pulse on both ports.
  run.py refresh NAME SECTION N [options]
      one period at rest, then N pulses on port 1; port 2 stays at rest.

options: seed=S   sample of mismatch (needs a section that ends in _mm). It does not set the noise
                  sample: a noisy run draws a new one each time (DESIGN.md)
         nz=1     noise sources on (levels from noise.json)
         temp=T   temperature in Celsius
         rel=1    print each time from the start of its pulse, not from the start of the run.
                  Six significant digits are printed, so a time from the start of the run loses
                  resolution as the run goes on. The campaign was run without this option.
         dir=D    folder of the results (default: results)
         any other name=value is a parameter of cell.spice (for example rlk=1e11)

Every run uses the same solver options, set in cell.spice, and the same largest step.
A run that the simulator aborts writes no result: it writes results/NAME.failed.
"""
import json, subprocess, sys

TU, TPER, T0 = 20e-6, 440e-6, 4.1e-6      # time unit, period, start of the pulse in a period
TMAX = "200n"                              # largest time step
mode, name, section = sys.argv[1], sys.argv[2], sys.argv[3]
rest = sys.argv[4:]
N = int(rest.pop(0)) if mode == "refresh" else None
opt = dict(seed=None, temp=None, kp="10", nz="0", rel="0", dir="results")
params = []
for e in rest:
    k, v = e.split("=")
    if k in opt: opt[k] = v
    else: params.append(e)
K, REL, RES = int(opt["kp"]), opt["rel"] == "1", opt["dir"]
text = open("cell.spice").read()
if mode == "refresh":
    x1 = [l for l in text.splitlines() if l.startswith("x1 ")][0]
    x2 = [l for l in text.splitlines() if l.startswith("x2 ")][0]
    text = text.replace(x1, x1.split(" ta=")[0] + f" ta={TPER:.9g} tb={(N + 1) * TPER:.9g} tj=1")
    text = text.replace(x2, x2.split(" ta=")[0] + " ta=1 tb=1 tj=1")
    n = N + 1
else:
    n = 2 * K + 2
# period 0 is at rest: it gives the reference read of the stored voltages, and it must not fire
if opt["nz"] == "1":
    z = json.load(open("noise.json"))["params"]
    tn = z["tnz"]
    for node, white, flicker in (("nzc", z["vncw"], z["vncf"]), ("nzo", z["vnow"], z["vnof"]),
                                 ("nzi", z["inmw"], 0.0), ("nzm", z["vnmw"], z["vnmf"])):
        old = f"vnz{node[2]} {node} 0 dc 0"
        assert old in text
        text = text.replace(old, f"{old} trnoise({white:.6g} {tn:.6g} {1 if flicker else 0} {flicker:.6g})")
lines = [f"* {name}", f'.lib "pdk/models/sky130.lib.spice" {section}'] + text.splitlines()[1:-1]
lines.append(".param " + " ".join(params + [f"kp={K}"]))
if opt["temp"]:
    lines.append(f".option temp={opt['temp']}")
lines.append(".save v(vq) v(vmem1) v(vmem2) v(p) v(x1.a) v(x1.b) v(x1.si) v(x2.a) v(x2.b) v(x2.si)")
ctl = [".control"]
if opt["seed"]:
    ctl += [f"setseed {opt['seed']}", "reset"]
ctl += [f"tran 1u {n * TPER:.9g} 0 {TMAX}"]
for k in range(n):
    base = k * TPER + T0
    a0 = k * TPER + (2.6e-6 if k == 0 else 0.05e-6)     # the protection is watched over the whole period
    a, b = base - 0.5e-6, (k + 1) * TPER - 2e-6
    ctl += ["let tf = -1", "let tf2 = -1", "let tr = -1", "let ta1 = -1", "let tb1 = -1", "let ts1 = -1",
            "let ta2 = -1", "let tb2 = -1", "let ts2 = -1",
            f"meas tran tf when v(p)=0.9 rise=1 from={a0:.9g} to={b:.9g}",
            f"meas tran tf2 when v(p)=0.9 rise=2 from={a0:.9g} to={b:.9g}",
            f"meas tran tr when v(p)=0.9 fall=1 from={base + 25e-6:.9g} to={b:.9g}",
            f"meas tran ta1 when v(x1.a)=0.9 rise=1 from={a:.9g} to={b:.9g}",
            f"meas tran tb1 when v(x1.b)=0.9 rise=1 from={a:.9g} to={b:.9g}",
            f"meas tran ts1 when v(x1.si)=0.9 rise=1 from={a:.9g} to={b:.9g}",
            f"meas tran ta2 when v(x2.a)=0.9 rise=1 from={a:.9g} to={b:.9g}",
            f"meas tran tb2 when v(x2.b)=0.9 rise=1 from={a:.9g} to={b:.9g}",
            f"meas tran ts2 when v(x2.si)=0.9 rise=1 from={a:.9g} to={b:.9g}",
            f"meas tran v1 avg v(vmem1) from={b - 40e-6:.9g} to={b:.9g}",
            f"meas tran v2 avg v(vmem2) from={b - 40e-6:.9g} to={b:.9g}",
            f"meas tran vqm min v(vq) from={a:.9g} to={b:.9g}",
            ] + ([f"let {x} = {x} - {base:.9g}" for x in ("tf", "tr", "ta1", "tb1", "ts1", "ta2", "tb2", "ts2", "tf2")] if REL else []) + [
            f"echo RES {k} $&tf $&tr $&ta1 $&tb1 $&ts1 $&ta2 $&tb2 $&ts2 $&v1 $&v2 $&vqm $&tf2"]
ctl += ["quit", ".endc", ".end"]
path = f"work/{name}.spice" if RES == "results" else f"work/{RES}_{name}.spice"     # two replays of a run never share a file
open(path, "w").write("\n".join(lines + ctl) + "\n")
p = subprocess.run(["ngspice", "-b", path], capture_output=True, text=True)
log = p.stdout + p.stderr
rows, v0 = [], None
for l in p.stdout.splitlines():
    if l.startswith("RES0 "):
        v0 = [float(x) for x in l.split()[1:3]]
    elif l.startswith("RES "):
        f = l.split()[1:]
        k = int(f[0]); base = k * TPER + T0
        if REL:        # a time that was not measured is -1 minus the start of the pulse
            seen = lambda x: float(x) > -0.5
            u = lambda x: float(x) / TU if seen(x) else -1
        else:
            seen = lambda x: float(x) > 0
            u = lambda x: (float(x) - base) / TU if seen(x) else -1
        if k == 0:
            v0 = [float(f[9]), float(f[10])]
            rest_fire = seen(f[1])
            continue
        port = 1 if mode == "refresh" or k <= K else (2 if k <= 2 * K else 0)
        rows.append([k - 1, port, int(seen(f[1])), u(f[1]), u(f[2]), u(f[3]), u(f[4]), int(seen(f[5])),
                     u(f[6]), u(f[7]), int(seen(f[8])), float(f[9]), float(f[10]), float(f[11]), int(seen(f[12]))])
if len(rows) < n - 1 or v0 is None or "aborted" in log or "too small" in log:
    open(f"{RES}/{name}.failed", "w").write(log[-3000:])
    print(name, "FAILED", len(rows), "of", n - 1)
    sys.exit(1)
with open(f"{RES}/{name}.csv", "w") as fh:
    fh.write("pulse,port,fired,fire_latency,reopen,entry1,exit1,steered1,entry2,exit2,steered2,vmem1,vmem2,vq_min,second_rise,step1_mV,step2_mV\n")
    prev = v0
    for r in rows:
        s1, s2 = 1e3 * (prev[0] - r[11]), 1e3 * (prev[1] - r[12])
        fh.write("%d,%d,%d,%.5f,%.4f,%.4f,%.4f,%d,%.4f,%.4f,%d,%.7f,%.7f,%.5f,%d,%.5f,%.5f\n" % (*r, s1, s2))
        prev = [r[11], r[12]]
if rest_fire:      # a protection with no pulse: kept with the results and reported by the analysis
    open(f"{RES}/{name}.restfire", "w").write("the protection rose in the period at rest\n")
print(name, "pulses", len(rows), "of", n - 1)
