"""Complement to the campaign, run after it. Not part of the predictions.

1. The 20 noise runs and the four mismatch runs that were being computed when the campaign was
   stopped and resumed (cells 2061 to 2064) are run again with the same seeds and the same
   netlist, with every time printed from the start of its pulse (option rel=1 of run.py).
   Results in results_rel/.
2. The nominal run is run again without the option. Result in results_check/. It must be
   identical to the result of the campaign: the option changes nothing when it is off.

3. With the argument "repeats": the two noisy refresh runs of one port are run four more times
   each, in results_rep1/ to results_rep4/. The campaign has one run of each, so their numbers
   had no interval. A corner run without noise is also run again, in results_check/.
4. With the argument "noise": the 20 noise runs are run two more times, in results_rel2/ and
   results_rel3/. The sigma of the joint read differed by a factor of two between the campaign
   and the first replay, so more samples were needed.

compare.py reads these results.
"""
import os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from campaign import jobs

AGAIN = [f"nz_{s}" for s in range(101, 121)] + [f"mc_{s}" for s in range(2061, 2065)]
plan = [(n, m, s, o + ["rel=1", "dir=results_rel"]) for n, m, s, o in jobs if n in AGAIN]
plan += [(n, m, s, o + ["dir=results_check"]) for n, m, s, o in jobs if n == "nom"]

REPEATED = ["refresh_none_nz", "refresh_lk11_nz"]
repeats = [(n, m, s, o + ["rel=1", f"dir=results_rep{i}"]) for i in range(1, 5) for n, m, s, o in jobs if n in REPEATED]
repeats += [(n, m, s, o + ["dir=results_check"]) for n, m, s, o in jobs if n == "pvt_tt_m40"]
more_noise = [(n, m, s, o + ["rel=1", f"dir=results_rel{i}"]) for i in (2, 3) for n, m, s, o in jobs if n.startswith("nz_")]


def run(j):
    name, mode, sec, opts = j
    p = subprocess.run([sys.executable, "-I", "run.py", mode, name, sec] + opts, capture_output=True, text=True)
    out = (p.stdout.strip().splitlines() or [name + " NO OUTPUT"])[-1]
    print(out, flush=True)
    return out

if __name__ == "__main__":
    todo = {"repeats": repeats, "noise": more_noise}.get((sys.argv[1:] or [""])[0], plan)
    for d in ["results_rel", "results_rel2", "results_rel3", "results_check"] + [f"results_rep{i}" for i in range(1, 5)]:
        os.makedirs(d, exist_ok=True)
    with ThreadPoolExecutor(os.cpu_count() or 4) as ex:
        out = list(ex.map(run, todo))
    print(len(out), "runs,", sum("FAILED" in o or "NO OUTPUT" in o for o in out), "failed")
