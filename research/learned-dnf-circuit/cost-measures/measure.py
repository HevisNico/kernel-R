"""Wall times on the nominal cell for campaign 4's measured cost model (COST_MODEL_DECISION.md, item 2).

  measure.py OUT.json WORK NGSPICE PDK NS_SRC

Exploratory, no claim, and NOT campaign implementation: it runs existing code only, on the nominal cell (section
`tt`, no mismatch seed), and touches no seed of campaign 4 (7501 onward) or any other mismatch seed.
  calibration  `../calibrate.py` (phase 0 of this folder), one cell, amplitude 0.49, 8 stages, two decks guard on
               and two guard off, four at a time
  untrained    the noise study's `cost3.py _run ... quiet` (NS_SRC: a checkout of commit c2cb677) on the untrained
               control calendar (`dnf_untrained.py`), three cells, four copies at a time; cost3's emulation: every
               input at amplitude 1 and no read-only gate, as in its need-4 run of 814 s
Per run: the wall time of the process and the peak resident memory of its simulator (wait4, children included).
"""
import json, os, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
PY = sys.executable


def timed(cmd, log):
    t0 = time.time()
    with open(log, "w") as f:
        p = subprocess.Popen(cmd, stdout=f, stderr=subprocess.STDOUT)
        _, status, ru = os.wait4(p.pid, 0)
    return dict(cmd=[str(c) for c in cmd], status=os.waitstatus_to_exitcode(status), wall_s=time.time() - t0,
                peak_rss_MB=ru.ru_maxrss / 1024)


def batch(jobs):
    with ThreadPoolExecutor(4) as ex:
        return list(ex.map(lambda j: timed(*j), jobs))


def main():
    out, work, ngspice, pdk, ns = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], sys.argv[4], Path(sys.argv[5])
    work.mkdir(parents=True, exist_ok=False)
    head = lambda d: subprocess.check_output(["git", "-C", str(d), "rev-parse", "HEAD"], text=True).strip()
    res = dict(what="wall times on the nominal cell for campaign 4's measured cost model; exploratory, no claim, not "
                    "campaign implementation; no mismatch seed simulated", code=dict(this=head(HERE), noise_study=head(ns)),
               python=sys.version.split()[0], machine=dict(processors=os.cpu_count()), runs={})
    cal = [([PY, "-B", HERE.parent / "calibrate.py", work / f"cal-{i}-{g}", ngspice, pdk, "0.49", g, "tt", "none"],
            work / f"cal-{i}-{g}.log") for i, g in enumerate(("on", "off", "on", "off"))]
    res["runs"]["calibration"] = batch(cal)
    out.write_text(json.dumps(res, indent=1) + "\n")
    cost3 = ns / "research/network-noise-study/phase0/cost3.py"
    unt = [([PY, "-B", cost3, "_run", work / f"untrained-{i}", "quiet", ngspice, pdk, "4", HERE / "dnf_untrained.py"],
            work / f"untrained-{i}.log") for i in range(4)]
    res["runs"]["untrained"] = batch(unt)
    out.write_text(json.dumps(res, indent=1) + "\n")


if __name__ == "__main__":
    main()
