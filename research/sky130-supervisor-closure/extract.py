"""Measures on the saved waveform of a session. No simulation is run."""
import hashlib
import json
from pathlib import Path

import numpy as np

from sim import CIRCUIT, SIGNALS, SLOT, T0, TU

COL = {s: i + 1 for i, s in enumerate(SIGNALS)}
NOISE = ["v(nzm)", "v(x1.nzo)", "v(x2.nzo)", "v(x1.nzc)", "v(x2.nzc)"]      # the voltage noise sources
NOISE_SAMPLES = 64


def read_raw(path):
    """Points of a binary raw file of ngspice: real values, one row per time point, time first."""
    blob = Path(path).read_bytes()
    head, _, body = blob.partition(b"Binary:\n")
    lines = head.decode("ascii", "replace").splitlines()
    nvar = int(next(l for l in lines if l.startswith("No. Variables:")).split(":")[1])
    npts = int(next(l for l in lines if l.startswith("No. Points:")).split(":")[1])
    names = [l.split("\t")[2] for l in lines[lines.index("Variables:") + 1:][:nvar]]
    assert any(l.startswith("Flags:") and "real" in l for l in lines) and names[0] == "time", "unexpected raw file"
    assert len(body) == 8 * nvar * npts, "raw file of the wrong size"
    saved = np.frombuffer(body, dtype="<f8").reshape(npts, nvar)
    assert np.isfinite(saved).all() and np.all(np.diff(saved[:, 0]) >= 0)
    assert set(names[1:]) <= set(SIGNALS) and set(SIGNALS) - set(names) <= {"i(v.x1.vdose)", "i(v.x2.vdose)"}, "unexpected vectors"
    d = np.full((npts, len(SIGNALS) + 1), np.nan)      # the write currents exist only on the instrumented deck
    d[:, 0] = saved[:, 0]
    for i, name in enumerate(names[1:], 1):
        d[:, COL[name]] = saved[:, i]
    return d


def noise_fingerprint(d):
    """SHA-256 of the first values drawn by the voltage noise sources, in nanovolts, at their own sample dates.

    The sources draw one value every `tnz` and the simulator stops on each of these dates, so the values do not
    depend on the circuit around the sources: two runs that received the same seed give the same fingerprint,
    whatever they simulate. Without noise every value is zero and the fingerprint is that of zeros."""
    step = json.loads((CIRCUIT / "noise.json").read_text())["params"]["tnz"]
    grid = step * np.arange(1, NOISE_SAMPLES + 1)
    assert d[-1, 0] >= grid[-1], "the waveform ends before the last sample date of the fingerprint"
    values = np.rint(np.column_stack([np.interp(grid, d[:, 0], d[:, COL[x]]) for x in NOISE]) * 1e9).astype("<i8")
    return hashlib.sha256(np.ascontiguousarray(values).tobytes()).hexdigest()


def at(d, signal, t):
    return float(np.interp(t, d[:, 0], d[:, COL[signal]]))


def mean(d, signal, lo, hi):
    """Time-weighted mean over [lo, hi], the two ends interpolated."""
    i0, i1 = np.searchsorted(d[:, 0], [lo, hi], side="right")
    t = np.concatenate(([lo], d[i0:i1, 0], [hi]))
    v = np.concatenate(([at(d, signal, lo)], d[i0:i1, COL[signal]], [at(d, signal, hi)]))
    return float(np.sum(np.diff(t) * (v[:-1] + v[1:]) / 2) / (hi - lo))


def rises(d, signal, lo, hi, level=0.9):
    i0, i1 = np.searchsorted(d[:, 0], [lo, hi])
    i0, i1 = max(i0 - 1, 0), min(i1 + 1, len(d))
    t, v = d[i0:i1, 0], d[i0:i1, COL[signal]]
    idx = np.flatnonzero((v[:-1] < level) & (v[1:] >= level))
    out = [float(t[i] + (t[i + 1] - t[i]) * (level - v[i]) / (v[i + 1] - v[i])) for i in idx]
    return [x for x in out if lo <= x < hi]


def slot_record(d, k):
    """What happened in slot k (from k*SLOT): controls, FIRE, writes and the stored voltages around them."""
    start = k * SLOT
    pulse = start + T0
    mid = start + 10e-6
    r = dict(slot=k, start_s=start, sel=[round(at(d, f"v(sel{p})", mid)) for p in (1, 2)], amp=[round(at(d, f"v(amp{p})", mid)) for p in (1, 2)],
             leak_S=at(d, "v(gl)", mid))
    fires = rises(d, "v(p)", start + 3.5e-6, start + SLOT - 2e-6)
    r.update(fires=len(fires), fire_latency=(fires[0] - pulse) / TU if fires else None,
             vq_before=at(d, "v(vq)", pulse - 1e-9), protection_before=at(d, "v(p)", pulse - 1e-9),
             vq_min=float(np.min(d[(d[:, 0] >= start) & (d[:, 0] < start + SLOT), COL["v(vq)"]])))
    for p in (1, 2):
        r[f"writes{p}"] = len(rises(d, f"v(x{p}.si)", start + 3.5e-6, start + SLOT - 2e-6))
        r[f"v{p}_pre_pulse"] = mean(d, f"v(vmem{p})", start - 40e-6, start - 1e-6) if k else None   # before the slot
        r[f"v{p}_pre_write"] = mean(d, f"v(vmem{p})", pulse + 20e-6, pulse + 30e-6)                  # before the write window
        r[f"v{p}_post_write"] = mean(d, f"v(vmem{p})", pulse + 50e-6, pulse + 60e-6)                 # after it
        r[f"v{p}_obs"] = mean(d, f"v(vmem{p})", start + 160e-6, start + 200e-6)                      # observation window
        r[f"sum{p}_mean"] = mean(d, f"v(x{p}.sum)", start, start + SLOT)
        # the voltage across the storage capacitor, stored node minus summing node: what the observer reads
        for tag, lo, hi in (("pre_pulse", start - 40e-6, start - 1e-6), ("obs", start + 160e-6, start + 200e-6)):
            r[f"u{p}_{tag}"] = (mean(d, f"v(vmem{p})", lo, hi) - mean(d, f"v(x{p}.sum)", lo, hi)) if (k or tag == "obs") else None
    return r
