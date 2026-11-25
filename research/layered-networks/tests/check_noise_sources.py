"""The inverters' injected noise sources, read from a noisy controls4 trace (OUT/trace.raw) against research/circuit
noise.json and the gate's K3 sigmas (noise3.budget_sigmas). No simulation.

  check_noise_sources.py OUT

- vnzm level: rms and the white-part estimate of xn<j>.nzm over the run, against vnmw (white, per 0.4 us sample) and
  total_input_uV (white and flicker), read at the sources' sample instants k tnz. The white part is estimated from
  successive samples (half the variance of their differences), which the slow flicker part barely enters.
- mirror shot sources: rms of nzh<x> and nzj<x> against inmw.
- mirror shot charge: over every disjoint window of length D in the run (a large sample), and per slot, the integral of (nzh + nzj) over the window [T, T + D tu], in x (divided by cq vunit),
  its sd over the slots against sigma_q = sqrt(2) inmw sqrt(D tu tnz) / (cq vunit).
"""
import json
import math
from pathlib import Path
import sys

import numpy as np

HERE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(HERE))
import noise3  # noqa: E402


def read_raw(path):
    data = Path(path).read_bytes()
    i = data.find(b"Binary:\n")
    head = data[:i].decode(errors="replace").splitlines()
    nv = int(next(l for l in head if l.startswith("No. Variables:")).split(":")[1])
    npt = int(next(l for l in head if l.startswith("No. Points:")).split(":")[1])
    k = head.index("Variables:")
    names = [head[k + 1 + j].split()[1] for j in range(nv)]
    arr = np.frombuffer(data[i + 8:i + 8 + 8 * nv * npt], dtype="<f8").reshape(npt, nv)
    return {n: arr[:, j] for j, n in enumerate(names)}


def main(out):
    out = Path(out)
    rec = json.loads((out / "noisy_record.json").read_text())
    cfg = noise3._cfg("config_inverter_c5.json")
    v = read_raw(out / "trace.raw")
    t = v["time"]
    P, sig = noise3.P, noise3.budget_sigmas(cfg)
    D_s = cfg["inverter"]["D"] * cfg["stimulus"]["tu_s"]
    res = {}
    keys = {k.lower(): k for k in v}
    for j in range(len(rec["slots"][0].get("inv", []))):
        x = f"n{j}"
        nzm = v[keys[f"v(x{x}.nzm)"]] if f"v(x{x}.nzm)" in keys else v[keys[f"x{x}.nzm"]]
        get = lambda n: v[keys[f"v({n})"]] if f"v({n})" in keys else v[keys[n]]
        nzh, nzj = get(f"nzh{x}"), get(f"nzj{x}")
        # samples on the 0.4 us grid of the sources
        grid = np.arange(0.0, t[-1], P["tnz"])          # the sources' own sample instants (k tnz)
        sm = np.interp(grid, t, nzm)
        white = math.sqrt(np.var(np.diff(sm)) / 2)
        sh, sj = np.interp(grid, t, nzh), np.interp(grid, t, nzj)
        q = []
        for sl in rec["slots"]:
            if not sl.get("inv"):
                continue
            T = sl["T"] * 1e-9
            m = (t >= T) & (t <= T + D_s)
            if m.sum() > 2:
                q.append(np.trapezoid((nzh + nzj)[m], t[m]) / (5e-12 * 0.5))
        # every disjoint window of length D over the run (the sources are stationary): a large sample of the
        # charge that one window integrates
        nwin = int((t[-1] - t[0]) // D_s)
        allq = []
        for w in range(nwin):
            a, b = t[0] + w * D_s, t[0] + (w + 1) * D_s
            m = (t >= a) & (t <= b)
            if m.sum() > 2:
                allq.append(np.trapezoid((nzh + nzj)[m], t[m]) / (5e-12 * 0.5))
        res[x] = dict(all_windows_charge_x=dict(n=len(allq), sd=float(np.std(allq))), nzm_rms_uV=float(np.sqrt(np.mean(sm ** 2)) * 1e6), nzm_white_uV=white * 1e6,
                      model_vnmw_uV=P["vnmw"] * 1e6, model_total_uV=noise3.SIGMA_CMP_V * 1e6,
                      nzh_rms_nA=float(np.sqrt(np.mean(sh ** 2)) * 1e9), nzj_rms_nA=float(np.sqrt(np.mean(sj ** 2)) * 1e9),
                      model_inmw_nA=P["inmw"] * 1e9,
                      window_charge_x=dict(n=len(q), sd=float(np.std(q)) if len(q) > 1 else None,
                                           rms=float(np.sqrt(np.mean(np.square(q)))) if q else None),
                      model_sigma_q_x=sig["eta_x"], K3_eta_x=3 * sig["eta_x"])
    print(json.dumps(res, indent=1))
    return res


if __name__ == "__main__":
    main(sys.argv[1])
