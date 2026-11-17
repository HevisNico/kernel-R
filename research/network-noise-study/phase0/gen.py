"""Phase 0, feasibility, no claim: what the trnoise generator of ngspice 42 gives, without a circuit.

  gen.py WORK OUT.json NGSPICE DRAWS [ALPHA ...]

For each exponent ALPHA, one deck holds a 1/f^ALPHA source of amplitude NAMP = 1 mV and a white source of
NA = 1 mV, both sampled every NT = 0.4 us, over 40 ms. DRAWS separate simulator processes (the noise is seeded
by the process number, so every process draws anew). The mean periodogram gives, per band,
  c(ALPHA) = f^ALPHA S(f) / NAMP^2   for the 1/f^ALPHA source,
  S(f) / (2 NT NA^2)                 for the white source (1 for an ideal sampled white noise).
It also records the standard deviation of the mean of a whole draw, which is what a run offset sees.
"""
import json, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import numpy as np

NT, TSTOP, NAMP, NA = 0.4e-6, 40e-3, 1e-3, 1e-3
BANDS = [(25, 50), (50, 100), (100, 300), (300, 1e3), (1e3, 1e4), (1e4, 1e5), (1e5, 5e5), (5e5, 1.25e6)]


def deck(alpha):
    return "\n".join([f"* trnoise generator, alpha {alpha}",
                      f"v1 a 0 dc 0 trnoise(0 {NT:g} {alpha:g} {NAMP:g})", "r1 a 0 1k",
                      f"v2 b 0 dc 0 trnoise({NA:g} {NT:g} 0 0)", "r2 b 0 1k",
                      ".control", f"tran {NT:g} {TSTOP:g} 0 {NT:g}", "linearize a b", "wrdata gen.txt a b",
                      "quit", ".endc", ".end", ""])


def one(work, ngspice, alpha, i):
    d = work / f"a{alpha:g}" / f"d{i:03d}"
    d.mkdir(parents=True, exist_ok=False)
    (d / "gen.spice").write_text(deck(alpha))
    subprocess.run([ngspice, "-b", "gen.spice"], cwd=d, capture_output=True, check=True)
    x = np.loadtxt(d / "gen.txt")
    return x[:, 1], x[:, 3]


def main():
    work, out, ngspice, draws = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], int(sys.argv[4])
    alphas = [float(a) for a in sys.argv[5:]] or [1.0]
    res = dict(nt_s=NT, tstop_s=TSTOP, namp_V=NAMP, na_V=NA, draws=draws, ngspice=ngspice, alphas={})
    for alpha in alphas:
        with ThreadPoolExecutor(4) as ex:
            xs = list(ex.map(lambda i: one(work, ngspice, alpha, i), range(draws)))
        n = len(xs[0][0])
        fr = np.fft.rfftfreq(n, NT)
        pf = np.mean([2 * NT / n * abs(np.fft.rfft(a - a.mean())) ** 2 for a, _ in xs], 0)
        pw = np.mean([2 * NT / n * abs(np.fft.rfft(b - b.mean())) ** 2 for _, b in xs], 0)
        rows = []
        for lo, hi in BANDS:
            m = (fr >= lo) & (fr < hi)
            rows.append(dict(band_Hz=[lo, hi], bins=int(m.sum()),
                             c_flicker=float(np.mean(pf[m] * fr[m] ** alpha) / NAMP ** 2),
                             white_ratio=float(np.mean(pw[m]) / (2 * NT * NA ** 2))))
        first = [float(a[1]) for a, _ in xs]
        res["alphas"][f"{alpha:g}"] = dict(
            bands=rows, distinct_first_samples=len(set(first)),
            run_mean_std_over_namp=float(np.std([a.mean() for a, _ in xs], ddof=1) / NAMP),
            rms_over_namp=float(np.mean([a.std() for a, _ in xs]) / NAMP))
        print(alpha, json.dumps(res["alphas"][f"{alpha:g}"]))
    out.write_text(json.dumps(res, indent=1) + "\n")


if __name__ == "__main__":
    main()
