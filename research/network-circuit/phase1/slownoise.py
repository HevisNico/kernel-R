"""Where the offset of a noisy run comes from: per run and port, the offset of the FIRE latency against the train
without noise, next to what the noise sources did in that run. Phase 1, exploratory. See NOISE.md.

  slownoise.py DATA CONSTANTS.json MEASURES.json NOISE_RUNS.json

DATA holds the folders of the runs named in MEASURES.json, with their waveforms. For each noisy train and each
port whose word is that of the train without noise:

  offset_mV            run offset of constants.py: (FIRE latency without noise - mean FIRE latency of the run) / slope
  preset_u_mV          stored voltage before the first pulse, minus the same without noise
  nzo_run_mV           mean over the reads of the run of the noise source of the integrator amplifier of the port
  nzo_preset_mV        mean of that source from 0.2 to 2.0 us, while the preset is applied
  nzm_run_mV           the same mean for the source of the FIRE comparator of the cell
  nzc_run_mV           the same mean for the source of the window comparator of the port
  gate_before_mV       stored node, mean of the 45 us before the first pulse, minus the same without noise

and, over all of them, least-squares fits of the offset on some of these, the sum of squares before and after.
"""
import json
from pathlib import Path
import statistics as st
import sys

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import measure


def main():
    data = Path(sys.argv[1])
    C = json.loads(Path(sys.argv[2]).read_text())["instances"]
    M = json.loads(Path(sys.argv[3]).read_text())["instances"]
    rows = []
    for seed, I in M.items():
        quiet = measure.Trace(data / I["quiet_train"]["run"] / "trace.raw")
        for train in I["noisy_trains"]:
            result = json.loads((data / train["run"] / "result.json").read_text())
            tr = measure.Trace(data / train["run"] / "trace.raw")
            for name, p in C[seed]["ports"].items():
                entry = next(x for x in p["noisy_trains"] if x["run"] == train["run"])
                if not entry["same_word_as_without_noise"]:
                    continue
                c, q = name[0], name[1]
                occ = [o for o in result["occurrences"] if f"{o['cell']}{o['port']}" == name]
                fires = [o for o in occ if o["fire"]]
                t0, t1 = fires[0]["date_s"], fires[-1]["date_s"] + 20e-6
                mean = lambda v, a, b: tr.mean(v, a, b) * 1e3
                node = f"v(x{c}.vmem{q})"
                rows.append(dict(instance=int(seed), run=train["run"], port=name, fires=len(fires), offset_mV=entry["offset_mV"], within_sd_mV=entry["within_sd_mV"],
                                 preset_u_mV=occ[0][f"u{q}_before_V"] * 1e3 - I["quiet_train"]["ports"][name][0]["u_before_mV"],
                                 nzo_run_mV=mean(f"v(x{c}.x{q}.nzo)", t0, t1), nzo_preset_mV=mean(f"v(x{c}.x{q}.nzo)", 0.2e-6, 2.0e-6),
                                 nzm_run_mV=mean(f"v(x{c}.nzm)", t0, t1), nzc_run_mV=mean(f"v(x{c}.x{q}.nzc)", t0, t1),
                                 gate_before_mV=mean(node, 50e-6, 95e-6) - quiet.mean(node, 50e-6, 95e-6) * 1e3))
    y = np.array([r["offset_mV"] for r in rows])
    fits = []
    for cols in (["preset_u_mV"], ["nzo_run_mV"], ["nzm_run_mV"], ["preset_u_mV", "nzo_run_mV"], ["preset_u_mV", "nzo_run_mV", "nzm_run_mV"],
                 ["preset_u_mV", "nzo_run_mV", "nzm_run_mV", "nzc_run_mV"], ["gate_before_mV"]):
        X = np.array([[r[c] for c in cols] for r in rows])
        coef = np.linalg.lstsq(X, y, rcond=None)[0]
        fits.append(dict(terms=cols, coefficients=[float(x) for x in coef], rms_left_mV=float(np.sqrt(np.mean((y - X @ coef) ** 2)))))
    groups = {}
    for r in rows:
        groups.setdefault((r["instance"], r["port"]), []).append(r["offset_mV"])
    squares = sum(sum((x - st.mean(g)) ** 2 for x in g) for g in groups.values())
    dof = sum(len(g) - 1 for g in groups.values())
    pairs = {}
    for r in rows:
        pairs.setdefault((r["run"], r["port"][0]), {})[r["port"][1]] = r["offset_mV"]
    both = np.array([(v["1"], v["2"]) for v in pairs.values() if len(v) == 2])
    kind = lambda long: [r for r in rows if r["run"].startswith("train-") == long]
    rms = lambda sel, key: float(np.sqrt(np.mean([r[key] ** 2 for r in sel])))
    summary = dict(port_runs=len(rows), rms_offset_mV=rms(rows, "offset_mV"), mean_offset_mV=float(y.mean()), sd_between_runs_of_one_port_mV=(squares / dof) ** 0.5,
                   degrees_of_freedom=dof, rms_within_run_mV=float(np.sqrt(np.mean([r["within_sd_mV"] ** 2 for r in rows]))),
                   sd_preset_u_mV=float(np.std([r["preset_u_mV"] for r in rows])), sd_nzo_run_mV=float(np.std([r["nzo_run_mV"] for r in rows])),
                   sd_nzm_run_mV=float(np.std([r["nzm_run_mV"] for r in rows])),
                   correlation_of_the_two_ports_of_a_cell=float(np.corrcoef(both[:, 0], both[:, 1])[0, 1]), cell_runs_with_both_ports=len(both),
                   rms_offset_trains_of_26_reads_mV=rms(kind(True), "offset_mV"), port_runs_of_26_reads=len(kind(True)),
                   rms_offset_trains_of_10_reads_mV=rms(kind(False), "offset_mV"), port_runs_of_10_reads=len(kind(False)), fits=fits)
    Path(sys.argv[4]).write_text(json.dumps(dict(what="run offsets of the noisy trains and the noise sources of each run; see slownoise.py", summary=summary, rows=rows), indent=1) + "\n")
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
