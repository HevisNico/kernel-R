"""The campaign. Predictions are in PREDICTION.md, committed before this ran.

Every run uses the same netlist, the same solver options and the same largest step.
Seeds: noise 101-120 and 201-202, cells 2001-2100, refresh cells 3001-3008. None was run before.
"""
import os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

jobs = []
# refresh, one port (the longest runs first)
jobs.append(("refresh_lk12", "refresh", "tt", ["560", "rlk=1e12"]))
jobs.append(("refresh_none", "refresh", "tt", ["150"]))
jobs.append(("refresh_lk11", "refresh", "tt", ["150", "rlk=1e11"]))
jobs.append(("refresh_none_nz", "refresh", "tt", ["150", "nz=1", "seed=202"]))
jobs.append(("refresh_lk11_nz", "refresh", "tt", ["150", "rlk=1e11", "nz=1", "seed=201"]))
for s in range(3001, 3009):
    jobs.append((f"refresh_mm_{s}", "refresh", "tt_mm", ["100", "rlk=1e11", "nz=1", f"seed={s}"]))
# nominal cell without noise, and a long run for the firing pulses after the stop
jobs.append(("nom", "cell", "tt", []))
jobs.append(("nom_long", "cell", "tt", ["kp=26"]))
# corners and temperature, without noise
for sec in ("ss", "ff", "sf", "fs"):
    jobs.append((f"pvt_{sec}_27", "cell", sec, []))
jobs.append(("pvt_tt_m40", "cell", "tt", ["temp=-40"]))
jobs.append(("pvt_tt_125", "cell", "tt", ["temp=125"]))
# noise on the nominal cell
for s in range(101, 121):
    jobs.append((f"nz_{s}", "cell", "tt", ["nz=1", f"seed={s}"]))
# mismatch and noise together
for s in range(2001, 2101):
    jobs.append((f"mc_{s}", "cell", "tt_mm", ["nz=1", f"seed={s}"]))

LIMIT_S = 90 * 60          # no run should come near this; a run that does is stopped and listed

def run(j):
    name, mode, sec, opts = j
    if os.path.exists(f"results/{name}.csv") or os.path.exists(f"results/{name}.failed"):
        return f"{name} already there"
    try:
        p = subprocess.run([sys.executable, "-I", "run.py", mode, name, sec] + opts, capture_output=True, text=True, timeout=LIMIT_S)
        out = (p.stdout.strip().splitlines() or [name + " NO OUTPUT"])[-1]
    except subprocess.TimeoutExpired:
        subprocess.run(["pkill", "-f", f"ngspice -b work/{name}.spice"])
        open(f"results/{name}.failed", "w").write("stopped at the time limit\n")
        out = f"{name} FAILED time limit"
    print(out, flush=True)
    return out

if __name__ == "__main__":
    with ThreadPoolExecutor(os.cpu_count() or 4) as ex:
        out = list(ex.map(run, jobs))
    print(len(out), "runs,", sum("FAILED" in o or "NO OUTPUT" in o for o in out), "failed")
