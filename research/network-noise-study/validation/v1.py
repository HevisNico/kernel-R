"""Validation, V1: the generator alone (numpy only), as fixed in VALIDATION_CRITERIA.md.

  v1.py OUT.json

400 seeds of 40 ms per exponent (0.84, 0.88, 1.0), noise seeds 2000 to 2399, A = 1e-12, B = 1e-8 as in phase 0's
`noisegen.py psd`. The mean periodogram of the samples (the sampled sequence, as in phase 0) against A + B/f^ef by
half decade: from 316 Hz up to the Nyquist frequency of the samples (1.25 MHz; the criteria's 1.6 MHz half decade
is cut there), within +-3 %; from 31.6 to 316 Hz within +-12 %. The slow part over instance keys 2000 to 2399: the
variance of one run's value and of the difference between two runs 1 000 s apart, against the integral of B/f^ef
over its band, within +-15 %.
"""
import json, math, sys
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "phase0"))
import noisegen                      # noqa: E402
from noisegen import NT, samples, slow_part, T_CAMPAIGN, RUN_GAP     # noqa: E402

DRAWS, FIRST = 400, 2000
A, B = 1e-12, 1e-8
EDGES = [10 ** 1.5, 10 ** 2, 10 ** 2.5] + [10 ** e for e in np.arange(3.0, 6.01, 0.5)] + [0.5 / NT]
TOL_HI, TOL_LO, TOL_SLOW = 0.03, 0.12, 0.15


def run(out):
    n = int(40e-3 / NT)
    res, ok = {}, True
    for alpha in (0.84, 0.88, 1.0):
        P = None
        for d in range(DRAWS):
            x = samples(FIRST + d, 0, n, A, B, alpha)[1:]
            p = 2 * NT / len(x) * abs(np.fft.rfft(x - x.mean())) ** 2
            P = p if P is None else P + p
        P /= DRAWS
        fr = np.fft.rfftfreq(n, NT)
        rows = []
        for lo, hi in zip(EDGES[:-1], EDGES[1:]):
            m = (fr >= lo) & (fr < hi) if hi < 0.5 / NT else (fr >= lo) & (fr <= hi)
            ratio = float(np.mean(P[m]) / np.mean(A + B / fr[m] ** alpha))
            tol = TOL_LO if hi <= 316.3 else TOL_HI
            rows.append(dict(band_Hz=[float(lo), float(hi)], bins=int(m.sum()), ratio=ratio, tolerance=tol,
                             pass_=abs(ratio - 1) <= tol))
        m_ = 1 << int(math.ceil(math.log2(2 * (n + 1))))
        f_hi = 0.5 / (m_ * NT)
        v1, v2 = [], []
        for d in range(DRAWS):
            y = slow_part(FIRST + d, 0, np.array([0.0, RUN_GAP]), B, alpha, f_hi)
            v1.append(y[0]); v2.append(y[1] - y[0])
        ff = np.logspace(math.log10(1 / T_CAMPAIGN), math.log10(f_hi), 40001)
        r1 = float(np.var(v1) / np.trapezoid(B / ff ** alpha, ff))
        r2 = float(np.var(v2) / np.trapezoid(B / ff ** alpha * 4 * np.sin(np.pi * ff * RUN_GAP) ** 2, ff))
        slow = dict(f_hi_Hz=f_hi, var_ratio=r1, diff_var_ratio=r2, tolerance=TOL_SLOW,
                    pass_=abs(r1 - 1) <= TOL_SLOW and abs(r2 - 1) <= TOL_SLOW)
        a_ok = all(r["pass_"] for r in rows) and slow["pass_"]
        ok &= a_ok
        res[f"{alpha:g}"] = dict(bands=rows, slow=slow, pass_=a_ok)
        print(alpha, a_ok, [round(r["ratio"], 4) for r in rows], round(r1, 4), round(r2, 4), flush=True)
    Path(out).write_text(json.dumps(dict(criterion="V1", draws=DRAWS, first_seed=FIRST, numpy=np.__version__, nt_s=NT,
                                         run_s=40e-3, A=A, B=B, results=res, pass_=bool(ok)), indent=1) + "\n")
    print("V1", ok)


if __name__ == "__main__":
    run(sys.argv[1])
