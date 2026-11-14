"""The noise sources alone, without a circuit, for several run lengths. Phase 1, exploratory. See NOISE.md.

  noisegen.py WORK NOISE_GENERATOR.json NGSPICE DRAWS STOP_S...

Each draw is one simulator process on a deck that holds only the three voltage noise sources of the bench, with the
parameters of `../../circuit/noise.json`: `nzo` (integrator amplifier of a port), `nzm` (FIRE comparator of a cell),
`nzc` (window comparator of a port). Per run length and source, in mV, standard deviations over the draws of:

  run_mean           the mean of the source from 0.1 ms to the end of the run
  preset_sample      its mean from 0.2 to 2.0 us, while the bench applies the preset
  last_minus_first   its mean over the last 20 us window minus the first, windows 360 us apart
and the mean over the draws of
  window_sd          the standard deviation, inside a run, of its means over those 20 us windows
  total_rms          its root mean square over the run
"""
import json
from pathlib import Path
import shutil
import statistics as st
import subprocess
import sys

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import measure

P = json.loads((HERE.parent.parent / "circuit" / "noise.json").read_text())["params"]
SOURCES = dict(nzo=(P["vnow"], P["vnof"]), nzm=(P["vnmw"], P["vnmf"]), nzc=(P["vncw"], P["vncf"]))


def draw(folder, stop, ngspice):
    folder.mkdir(parents=True)
    lines = ["* the noise sources of the bench alone"]
    for n, (white, flicker) in SOURCES.items():
        lines += [f"v{n} {n} 0 dc 0 trnoise({white:.16g} {P['tnz']:.16g} 1 {flicker:.16g})", f"r{n} {n} 0 1k"]
    (folder / "d.cir").write_text("\n".join(lines + [f".tran 0.4u {stop:.12g} 0 0.2u", ".end"]) + "\n")
    subprocess.run([ngspice, "-b", "-r", "o.raw", "d.cir"], cwd=folder, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
    tr = measure.Trace(folder / "o.raw")
    out = {}
    for n in SOURCES:
        v = f"v({n})"
        windows = [tr.mean(v, t, t + 20e-6) * 1e3 for t in np.arange(100e-6, stop - 30e-6, 360e-6)]
        out[n] = dict(run_mean=tr.mean(v, 100e-6, stop) * 1e3, preset_sample=tr.mean(v, 0.2e-6, 2.0e-6) * 1e3, window_sd=st.stdev(windows),
                      last_minus_first=windows[-1] - windows[0], total_rms=float(np.sqrt(np.mean((tr.v[v] * 1e3) ** 2))))
    shutil.rmtree(folder)
    return out


def main():
    work, out, ngspice, draws = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], int(sys.argv[4])
    result = {}
    for stop in map(float, sys.argv[5:]):
        rows = [draw(work / f"{stop:g}-{i}", stop, ngspice) for i in range(draws)]
        result[f"{stop * 1e3:g} ms"] = {n: dict(draws=draws, run_mean_sd=st.stdev(r[n]["run_mean"] for r in rows), preset_sample_sd=st.stdev(r[n]["preset_sample"] for r in rows),
                                                last_minus_first_sd=st.stdev(r[n]["last_minus_first"] for r in rows),
                                                window_sd=st.mean(r[n]["window_sd"] for r in rows), total_rms=st.mean(r[n]["total_rms"] for r in rows)) for n in SOURCES}
    out.write_text(json.dumps(dict(what="the noise sources alone, by run length; see noisegen.py", unit="mV", sources={n: dict(white_V=w, flicker_V=f) for n, (w, f) in SOURCES.items()},
                                   sample_time_s=P["tnz"], by_run_length=result), indent=1) + "\n")


if __name__ == "__main__":
    main()
