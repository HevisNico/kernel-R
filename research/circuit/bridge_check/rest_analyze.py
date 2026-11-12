"""Extract the preregistered rest diagnostic, without fitting any parameter."""
import csv
import gzip
import json
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
TU, PERIOD, OFFSET = 20e-6, 440e-6, 4.1e-6
LOW, HIGH, GUARD = 0.1, 0.1001, 0.000002


def sample(data, when, column):
    j = int(np.searchsorted(data[:, 0], when, side="right"))
    if j == 0 or j == len(data):
        raise ValueError("sample not bracketed by saved solver points")
    a, b = data[j - 1], data[j]
    if b[0] <= a[0]:
        raise ValueError("nonpositive interpolation interval")
    value = a[column] + (b[column] - a[column]) * (when - a[0]) / (b[0] - a[0])
    return float(value), float(a[0]), float(a[column]), float(b[0]), float(b[column])


def flags(q):
    literal = LOW <= q <= HIGH
    if q - GUARD >= LOW and q + GUARD <= HIGH:
        return literal, "inside"
    if q + GUARD < LOW or q - GUARD > HIGH:
        return literal, "outside"
    return literal, "boundary"


def rises(data, column, start, stop):
    hits = np.flatnonzero((data[:-1, column] < 0.9) & (data[1:, column] >= 0.9))
    times = []
    for i in hits:
        a, b = data[i], data[i+1]
        t = a[0] + (b[0] - a[0]) * (0.9 - a[column]) / (b[column] - a[column])
        if start <= t < stop:
            times.append(float(t))
    return times


def extract(path):
    with gzip.open(path, "rt") as fh:
        data = np.loadtxt(fh)
    if data.ndim != 2 or data.shape[1] != 17 or not np.isfinite(data).all():
        raise ValueError("invalid trace shape or nonfinite values")
    if np.any(np.diff(data[:, 0]) < 0) or data[-1, 0] < 22*PERIOD - 1e-10:
        raise ValueError("unordered or truncated trace")
    rows = []
    for k in range(1, 22):
        edge = k*PERIOD + OFFSET
        value, ta, va, tb, vb = sample(data, edge-1e-12, 1)
        q = 0.1 + (1.25-value)/0.5
        literal, flag = flags(q)
        secondary = sample(data, edge-0.5e-6, 1)[0]
        row = dict(pulse=k-1, port=1 if k <= 10 else 2 if k <= 20 else 0,
                   sample_time=edge-1e-12, vq=value, q=q, literal_inside=literal, flag=flag,
                   bracket_t0=ta, bracket_v0=va, bracket_t1=tb, bracket_v1=vb,
                   secondary_q=0.1+(1.25-secondary)/0.5)
        for label, col in (("protection", 2), ("comparator", 3), ("entry1", 9),
                           ("exit1", 10), ("steering1", 11), ("entry2", 14),
                           ("exit2", 15), ("steering2", 16)):
            ts = rises(data, col, k*PERIOD, (k+1)*PERIOD)
            row[label+"_rises"] = len(ts)
            row[label+"_first_latency"] = (ts[0]-edge)/TU if ts else None
        rows.append(row)
    return rows


def main():
    manifest = json.loads((HERE / "manifest.json").read_text())
    all_rows, states = [], []
    for run in manifest["runs"]:
        folder = HERE / "runs" / run["name"]
        try:
            meta = json.loads((folder / "metadata.json").read_text())
            if meta["status"] != "produced_trace":
                raise ValueError(meta["status"])
            rows = extract(folder / "trace.txt.gz")
            for row in rows:
                all_rows.append(dict(run=run["name"], **row))
            states.append(dict(run=run["name"], status="analyzed", samples=len(rows)))
        except (OSError, ValueError, KeyError) as exc:
            states.append(dict(run=run["name"], status="not_evaluable", reason=str(exc)))
    if all_rows:
        with (HERE / "rest_samples.csv").open("w", newline="") as fh:
            writer = csv.DictWriter(fh, fieldnames=all_rows[0], lineterminator="\n")
            writer.writeheader()
            writer.writerows(all_rows)
    (HERE / "rest_status.json").write_text(json.dumps(states, indent=2)+"\n")
    for run in manifest["runs"]:
        rs = [r for r in all_rows if r["run"] == run["name"]]
        print(run["name"], {flag: sum(r["flag"] == flag for r in rs)
                           for flag in ("inside", "boundary", "outside")},
              "q_range", [min(r["q"] for r in rs), max(r["q"] for r in rs)] if rs else None)


if __name__ == "__main__":
    main()
