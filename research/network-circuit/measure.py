"""Measures on the saved waveform of a network session. No simulation is run."""
from pathlib import Path

import numpy as np

from net import CYCLE, TU


class Trace:
    """A binary raw file of ngspice: one array per saved vector, by name."""

    def __init__(self, path):
        blob = Path(path).read_bytes()
        head, _, body = blob.partition(b"Binary:\n")
        lines = head.decode("ascii", "replace").splitlines()
        nvar = int(next(l for l in lines if l.startswith("No. Variables:")).split(":")[1])
        npts = int(next(l for l in lines if l.startswith("No. Points:")).split(":")[1])
        names = [l.split("\t")[2] for l in lines[lines.index("Variables:") + 1:][:nvar]]
        assert any(l.startswith("Flags:") and "real" in l for l in lines) and names[0] == "time" and len(body) == 8 * nvar * npts
        data = np.frombuffer(body, dtype="<f8").reshape(npts, nvar)
        assert np.isfinite(data).all() and np.all(np.diff(data[:, 0]) >= 0)
        self.t = data[:, 0]
        self.v = {name: data[:, i] for i, name in enumerate(names)}

    def at(self, name, t):
        return float(np.interp(t, self.t, self.v[name]))

    def mean(self, name, lo, hi):
        i0, i1 = np.searchsorted(self.t, [lo, hi], side="right")
        t = np.concatenate(([lo], self.t[i0:i1], [hi]))
        v = np.concatenate(([self.at(name, lo)], self.v[name][i0:i1], [self.at(name, hi)]))
        return float(np.sum(np.diff(t) * (v[:-1] + v[1:]) / 2) / (hi - lo))

    def crossings(self, name, lo, hi, level=0.9, rising=True):
        i0, i1 = np.searchsorted(self.t, [lo, hi])
        i0, i1 = max(i0 - 1, 0), min(i1 + 1, len(self.t))
        t, v = self.t[i0:i1], self.v[name][i0:i1]
        idx = np.flatnonzero((v[:-1] < level) & (v[1:] >= level)) if rising else np.flatnonzero((v[:-1] >= level) & (v[1:] < level))
        out = [float(t[i] + (t[i + 1] - t[i]) * (level - v[i]) / (v[i + 1] - v[i])) for i in idx]
        return [x for x in out if lo <= x < hi]

    def u(self, c, p, lo, hi):
        """Voltage across the storage capacitor of port p of cell c: stored node minus summing node, mean over [lo, hi]."""
        return self.mean(f"v(x{c}.vmem{p})", lo, hi) - self.mean(f"v(x{c}.x{p}.sum)", lo, hi)


def pulse_record(tr, c, p, date, ports=(1, 2)):
    """What the waveform shows for a pulse of port p of cell c that starts at `date`: the state of the cell when it
    arrives, FIRE and its latency, the writes, the capacitor voltages before and after, the dates of the cycle."""
    end = date + CYCLE
    fires = tr.crossings(f"v(x{c}.p)", date, date + TU + 2e-6)
    r = dict(cell=c, port=p, date_s=date, protected_at_start=tr.at(f"v(x{c}.p)", date - 1e-9) > 0.9,
             main_charge_at_start=(1.25 - tr.at(f"v(x{c}.vq)", date - 1e-9)) / 0.5 + 0.1,          # 0.1 is rest, 1 is the FIRE level
             fire=bool(fires), fire_date_s=fires[0] if fires else None, latency=(fires[0] - date) / TU if fires else None)
    if fires:
        release = tr.crossings(f"v(x{c}.p)", fires[0], fires[0] + 12 * TU, rising=False)
        r["protected_until_units"] = (release[0] - date) / TU if release else None
    for q in ports:
        rise = tr.crossings(f"v(x{c}.x{q}.si)", date, end)
        fall = tr.crossings(f"v(x{c}.x{q}.si)", date, end, rising=False)
        r[f"writes{q}"] = len(rise)
        r[f"u{q}_before_V"] = tr.u(c, q, date - 30e-6, date - 2e-6)
        r[f"u{q}_after_V"] = tr.u(c, q, end - 30e-6, end - 2e-6)
        if q == p:
            r["error_phase_units"] = [(rise[0] - date) / TU, (fall[0] - date) / TU] if rise and fall else None
    r["step_mV"] = (r[f"u{p}_before_V"] - r[f"u{p}_after_V"]) * 1e3            # positive toward a higher gain
    return r
