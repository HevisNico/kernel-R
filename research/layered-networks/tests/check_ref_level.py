"""The comparator noise level read where the comparator sees it: a noisy controls5 run made with save_ref=1, whose
trace holds each inverter's comparator reference before the noise (xn<j>.vrefm) and at the comparator input
(xn<j>.vrefmn, after bvrm, rvrm and cvrm). No simulation.

  check_ref_level.py OUT

Per inverter, e = vrefmn - vrefm is what the comparator input carries beyond its reference. It is the injected
vnzm (xn<j>.nzm) plus two deterministic parts of the circuit, which a noiseless run has too:
- a lag while vrefm ramps: the input node is loaded by the comparator's input device, so vrefmn trails vrefm by
  tau x dvrefm/dt; tau is fitted here by least squares, away from the trips;
- the comparator's kickback at each trip, up to a few hundred mV for a few ns.
Reported, at the source's sample instants k tnz outside +-200 ns of every FIRE latch date (the quiet grid):
- rms and white part of e and of nzm (half the variance of successive differences), against vnmw and total_input_uV
  (noise.json) and noise4_budget.json's measured level; in uV and in x (divided by vunit);
- the residual r = e - nzm + tau dvrefm/dt: percentiles and max;
- per trip: r 50 ns before the latch date, and the kickback peak |e - nzm| within +-200 ns.
Exit 0 iff the reference vectors are present, rms(e) on the quiet grid is within 1 % of rms(nzm) on the same grid,
and max |r| on the quiet grid is below 100 uV (less than a third of the comparator's sigma).
"""
import json
import math
from pathlib import Path
import sys

import numpy as np

HERE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "tests"))
import noise3  # noqa: E402
from check_noise_sources import read_raw  # noqa: E402

QUIET_S = 200e-9


def main(out):
    out = Path(out)
    rec = json.loads((out / "noisy_record.json").read_text())
    v = read_raw(out / "trace.raw")
    keys = {k.lower(): k for k in v}
    get = lambda n: v[keys[f"v({n})"]] if f"v({n})" in keys else v[keys[n]]
    t, P, vunit = v["time"], noise3.P, 0.5
    budget = json.loads((HERE / "noise4_budget.json").read_text())["sigma_delta"]["comparator_total_rms_uV"]
    grid = np.arange(0.0, t[-1], P["tnz"])
    res, ok = dict(saved_ref=rec.get("saved_ref")), bool(rec.get("saved_ref"))
    for j in range(len(rec["slots"][0].get("inv", []))):
        x = f"n{j}"
        try:
            vm, vmn, nzm = get(f"x{x}.vrefm"), get(f"x{x}.vrefmn"), get(f"x{x}.nzm")
        except KeyError as err:
            print(f"missing vector {err}")
            return False
        e, slope = vmn - vm, np.gradient(vm, t)
        lat = np.array([sl["inv"][j]["latch"] * 1e-9 for sl in rec["slots"]
                        if j < len(sl.get("inv", [])) and sl["inv"][j].get("latch") is not None])
        dist = lambda tt: np.min(np.abs(tt[:, None] - lat[None, :]), axis=1) if len(lat) else np.full(len(tt), np.inf)
        far = dist(t) > QUIET_S
        m = far & (np.abs(slope) > 0)
        tau = float(-np.sum((e - nzm)[m] * slope[m]) / np.sum(slope[m] ** 2)) if m.any() else 0.0
        r = e - nzm + tau * slope
        q = dist(grid) > QUIET_S
        eg, ng, rg = (np.interp(grid, t, y)[q] for y in (e, nzm, r))
        rms = lambda y: float(np.sqrt(np.mean(y ** 2)))
        white = lambda y: math.sqrt(np.var(np.diff(y)) / 2)
        trips = []
        for L in lat:
            w = np.abs(t - L) <= QUIET_S
            trips.append(dict(latch_ns=round(L * 1e9), r_50ns_before_uV=float(np.interp(L - 50e-9, t, r)) * 1e6,
                              kickback_peak_mV=float(np.max(np.abs((e - nzm)[w]))) * 1e3))
        res[x] = dict(quiet_grid=dict(n=int(q.sum()), of=len(grid), excluded_ns_around_each_latch=QUIET_S * 1e9),
                      e_rms_uV=rms(eg) * 1e6, nzm_rms_uV=rms(ng) * 1e6, e_white_uV=white(eg) * 1e6,
                      nzm_white_uV=white(ng) * 1e6, e_rms_x=rms(eg) / vunit,
                      e_over_nzm=rms(eg) / rms(ng), e_over_noise_json=rms(eg) / noise3.SIGMA_CMP_V,
                      e_over_noise4_budget=rms(eg) / (budget * 1e-6),
                      model_vnmw_uV=P["vnmw"] * 1e6, model_total_uV=noise3.SIGMA_CMP_V * 1e6, noise4_budget_uV=budget,
                      lag_tau_ps=tau * 1e12,
                      residual_uV={f"p{p}": float(np.percentile(np.abs(rg), p)) * 1e6 for p in (50, 99, 99.9)}
                      | dict(max=float(np.max(np.abs(rg))) * 1e6),
                      trips=trips)
        ok &= abs(rms(eg) / rms(ng) - 1) < 0.01 and float(np.max(np.abs(rg))) < 100e-6
    print(json.dumps(res, indent=1))
    print("REFERENCE LEVEL READ: the comparator input carries the injected vnzm" if ok else "REFERENCE LEVEL CHECK FAILS")
    return ok


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1]) else 1)
