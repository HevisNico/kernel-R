"""Phase 0: does the presence of the filesource sources (and xtrtol=7) change the circuit's behaviour?

  zerocheck.py OUT.json QUIET_RUN_DIR FSZERO_RUN_DIR

Compares a campaign-4 run with the model's sources present as XSPICE filesource instances at zero amplitude
(`cost3.py dnf ... fszero`) with the same run without any source (`quiet`). It passes when:
  - the occurrences are the same: same list, and for each the same delivered / fire / protection flags and the same
    writes;
  - the FIRE events are the same: the same list, each with the same cell, the same occurrences during which it
    fires and the same routed lines (its date is reported: the two runs do not take the same time steps). A first
    version compared the calendar dates rounded to 1e-9 unit; it was changed to this after the first comparison,
    whose 49 FIRE events were these same events with dates up to 0.1 us apart;
  - every stored voltage read by the router (each occurrence's u*_V fields, and the final stored voltages) agrees
    within TOL_V = 1 uV.
Reported as well, not part of the verdict: the FIRE dates and latencies, and the largest difference of the stored
voltage traces (`v(x<c>.vmem<p>)`, the zero-amplitude run interpolated on the quiet run's time grid; the two runs do
not take the same time steps, so near a write this includes interpolation across the edge).
"""
import json, sys
from pathlib import Path
import numpy as np

TOL_V = 1e-6


def raw_binary(path):
    data = Path(path).read_bytes()
    head, _, body = data.partition(b"Binary:\n")
    lines = head.decode().splitlines()
    nv = int(next(l for l in lines if l.startswith("No. Variables:")).split(":")[1])
    npts = int(next(l for l in lines if l.startswith("No. Points:")).split(":")[1])
    i = lines.index("Variables:")
    names = [lines[i + 1 + k].split()[1] for k in range(nv)]
    a = np.frombuffer(body[:8 * nv * npts], dtype="<f8").reshape(npts, nv)
    return {n: a[:, k] for k, n in enumerate(names)}


def compare(quiet_dir, zero_dir):
    q = json.loads((Path(quiet_dir) / "result.json").read_text())
    z = json.loads((Path(zero_dir) / "result.json").read_text())
    flags = ("cell", "port", "origin", "calendar_date", "id", "delivered", "protected_when_scheduled",
             "protected_at_start", "fire")
    same_occ = len(q["occurrences"]) == len(z["occurrences"])
    occ_diff, dv, dfire, dlat = [], 0.0, 0.0, 0.0
    for a, b in zip(q["occurrences"], z["occurrences"]):
        keys = [k for k in a if k in flags or k.startswith("writes")]
        bad = [k for k in keys if a.get(k) != b.get(k)]
        if bad:
            occ_diff.append(dict(id=a.get("id"), fields=bad))
        for k in a:
            if k.endswith("_V") and isinstance(a[k], (int, float)) and isinstance(b.get(k), (int, float)):
                dv = max(dv, abs(a[k] - b[k]))
        if a.get("fire") and b.get("fire"):
            dfire = max(dfire, abs(a["fire_date_s"] - b["fire_date_s"]))
            dlat = max(dlat, abs(a["latency"] - b["latency"]))
    fq = [(f["cell"], f["during"], f["routed"]) for f in q["fires"]]
    fz = [(f["cell"], f["during"], f["routed"]) for f in z["fires"]]
    dfd = max([abs(a["date_s"] - b["date_s"]) for a, b in zip(q["fires"], z["fires"])] or [0.0])
    final = [abs(x - y) for x, y in zip(np.ravel(q["final_u_V"]), np.ravel(z["final_u_V"]))] if isinstance(q["final_u_V"], list) \
        else [abs(q["final_u_V"][k] - z["final_u_V"][k]) for k in q["final_u_V"]]
    dv = max([dv] + final)
    tq, tz = raw_binary(Path(quiet_dir) / "trace.raw"), raw_binary(Path(zero_dir) / "trace.raw")
    trace = {}
    for n in tq:
        if ".vmem" in n and n in tz:
            d = np.abs(tq[n] - np.interp(tq["time"], tz["time"], tz[n]))
            trace[n] = dict(max=float(d.max()), p999=float(np.percentile(d, 99.9)), median=float(np.median(d)))
    ok = same_occ and not occ_diff and fq == fz and dv <= TOL_V
    return dict(tolerance_V=TOL_V, occurrences=[len(q["occurrences"]), len(z["occurrences"])], occurrence_differences=occ_diff,
                fires=[len(fq), len(fz)], same_fires=fq == fz, max_fire_event_date_diff_s=dfd, max_read_voltage_diff_V=dv, max_fire_date_diff_s=dfire,
                max_latency_diff=dlat, trace_vmem_diff_V=trace, points=[q["points"], z["points"]], passes=ok)


if __name__ == "__main__":
    r = compare(sys.argv[2], sys.argv[3])
    Path(sys.argv[1]).write_text(json.dumps(r, indent=1) + "\n")
    print(json.dumps({k: v for k, v in r.items() if k != "trace_vmem_diff_V"}))
    print("trace max", max(v["max"] for v in r["trace_vmem_diff_V"].values()), "p99.9", max(v["p999"] for v in r["trace_vmem_diff_V"].values()))
