"""Validation: the list of runs of PROTOCOL.md, run four at a time; a run whose result exists is not run again.

  vplan.py list          print the runs
  vplan.py run WORK [FILTER]   run them (those whose name contains FILTER, or machine=1|2), results in WORK/<name>.json
                               or WORK/<name>/
"""
import re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
PY = "/home/user/owner-prep/venv312/bin/python"
DEV = ("7101", "7102", "7103")


def runs():
    R = []
    # V8
    for i in DEV:
        R += [("seeding", f"v8_{i}_r3", i, "3"), ("seeding", f"v8_{i}_r4", i, "4"), ("seeding", f"v8_{i}_r3again", i, "3"),
              ("seeding", f"v8_{i}_quiet", i, "quiet")]
    # V3/V4 hold
    R += [("frozen", f"v3_nominal_hold_r{r}", "nominal", "hold", "a", "1", "0.08", str(r), "model") for r in range(1, 33)]
    for i in DEV:
        R += [("frozen", f"v3_{i}_hold_r{r}", i, "hold", "all", "-", "0.08", str(r), "model") for r in range(5, 13)]
    # V3 window, fire, pulse
    outs = {"nominal": [("window", "a", "1"), ("fire", "a", "-"), ("pulse", "a", "1")]}
    for i in DEV:
        outs[i] = [("window", "a", "1"), ("window", "b", "2"), ("fire", "a", "-"), ("fire", "b", "-"), ("pulse", "a", "1"),
                   ("pulse", "b", "2")]
    for i, first in (("nominal", 33),) + tuple((i, 13) for i in DEV):
        r = first
        for st, c, p in outs[i]:
            for _ in range(8):
                R.append(("frozen", f"v3_{i}_{st}_{c}{p.strip('-')}_r{r}", i, st, c, p, "0.02", str(r), "model"))
                r += 1
    # V6
    for i, first in (("nominal", 57),) + tuple((i, 61) for i in DEV):
        R.append(("preset", f"v6_{i}_zero", i, "zero"))
        R += [("preset", f"v6_{i}_r{r}", i, str(r)) for r in range(first, first + 32)]
    # V7 and section 3
    for i in DEV:
        R += [("train", f"tr_{i}_quiet1", i, "quiet"), ("train", f"tr_{i}_quiet2", i, "quiet"), ("train", f"tr_{i}_zero", i, "zero")]
        R += [("train", f"tr_{i}_r{r}", i, str(r)) for r in range(93, 98)]
    # V5: the injected model
    R += [("frozen", f"v5_nominal_hold_inj{k}", "nominal", "hold", "a", "1", "0.08", "-", "injected") for k in range(32)]
    for i in DEV:
        R += [("frozen", f"v5_{i}_hold_inj{k}", i, "hold", "all", "-", "0.08", "-", "injected") for k in range(8)]
        R += [("train", f"tr_{i}_inj{k}", i, "injected") for k in range(5)]
    return R


def machine(name):
    """The share of each machine (the owner's two machines): 2 runs V5 (the injected model), and V3 at window, fire
    and pulse of the nominal cell and 7103; 1 runs the rest."""
    if name.startswith("v5_") or (name.startswith("tr_") and "_inj" in name):
        return 2
    if re.match(r"v3_(nominal|7103)_(window|fire|pulse)_", name):
        return 2
    return 1


def command(work, r):
    kind, name = r[0], r[1]
    out = Path(work) / (name if kind == "train" else f"{name}.json")
    return out, [PY, "-B", str(HERE / "vrun.py"), kind, str(out)] + list(r[2:])


def run(work, filt=""):
    """FILT: a substring of the run names, or `machine=1` / `machine=2`."""
    Path(work).mkdir(parents=True, exist_ok=True)
    if filt.startswith("machine="):
        todo = [r for r in runs() if machine(r[1]) == int(filt.split("=")[1])]
    else:
        todo = [r for r in runs() if filt in r[1]]
    log = open(Path(work) / "plan.log", "a")

    def one(r):
        out, cmd = command(work, r)
        done = (out / "meta.json") if r[0] == "train" else out
        if done.exists():
            return
        t0 = time.time()
        p = subprocess.run(cmd, capture_output=True, text=True)
        msg = f"{r[1]} exit {p.returncode} {time.time() - t0:.0f} s"
        if p.returncode:
            msg += "\n" + p.stderr[-2000:]
        print(msg, file=log, flush=True)
    with ThreadPoolExecutor(4) as ex:
        list(ex.map(one, todo))
    print("done", filt, file=log, flush=True)


if __name__ == "__main__":
    if sys.argv[1] == "list":
        for r in runs():
            print(" ".join(r))
        print(len(runs()), "runs")
    else:
        run(sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else "")
