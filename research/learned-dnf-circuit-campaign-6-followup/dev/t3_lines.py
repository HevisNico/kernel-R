"""Development only, POST-HOC and descriptive: why `w` grows on the lines of c at twice the dose. No new run: it reads
the 16 noisy network runs of step D and the two quiet runs of step C with campaign 5's readers.

  t3_lines.py REPO G6_CONFIG.json G6.json OUT.json

For each firing read of c with one line arrived (the reads of the kinds c1 and c2 of g6.py), in each noisy run and in
the quiet run of its dose, at the same slot: the stage of the calendar, the FIRE latency, the stored voltage of the
line's port before the read (u_before_mV), and the peak of the score before the FIRE. Then, per row (run, line):
  within       = stdev of the noisy latencies (campaign 3's `within`, in latency units, as G6)
  within_diff  = stdev of (noisy latency - quiet latency at the same slot): the same with the quiet run's own
                 slot-to-slot differences removed
  du           = noisy stored voltage - quiet stored voltage at the same slot, in mV: its mean over the row (what the
                 run adds to the port) and its stdev within the row
and, pooled over the rows of a dose, the regression of (latency difference - its row mean) on (du - its row mean):
the slope of the latency against the stored voltage as the runs themselves show it at the trained state, the part of
the latency scatter it explains, and what is left.
"""
import json
import math
from pathlib import Path
import statistics
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import dosedev2


def rms(xs):
    xs = list(xs)
    return math.sqrt(sum(x * x for x in xs) / len(xs)) if xs else None


def line_fires(modules, d):
    """{slot: {line: dict(stage, pattern, latency, u_mV, level)}} for the firing reads of c with one line arrived."""
    measure, plans4, reads4 = modules
    d = Path(d)
    rec = json.loads((d / "record.json").read_text())
    plan, slots = plans4.network(tuple(rec["needs"]), rec["control"])
    result = json.loads((d / "evidence" / "result.json").read_text())
    rows = reads4.network_reads(measure.Trace(d / "evidence" / "trace.raw"), result, slots)
    out = {}
    for x in rows:
        r = x["reads"].get("c")
        if r is None or x["stage"] == "skew control" or not r["fire"]:
            continue
        arrived = sorted({a["port"] for a in r["arrivals"]})
        if len(arrived) != 1:
            continue
        p = str(arrived[0])
        out[x["slot"]] = dict(line=p, stage=x["stage"], pattern=x.get("pattern"), latency=r["latency"], u_mV=r["ports"][p]["u_before_mV"],
                              level=r["q_peak_before_fire"], writes=r["ports"][p]["writes"])
    return rec["id"], out


if __name__ == "__main__":
    repo, config, g6_path, dest = sys.argv[1:5]
    dosedev2.repo_paths(repo)
    import measure
    import plans4
    import reads4
    mods = (measure, plans4, reads4)
    cfg = json.loads(Path(config).read_text())["doses"]
    g6 = json.loads(Path(g6_path).read_text())
    res = {}
    for label in ("1x", "2x"):
        _, quiet = line_fires(mods, cfg[label]["quiet"])
        slopes = {p: g6[label]["slopes"][f"c{p}"] for p in ("1", "2")}
        rows, pooled = [], []
        for d in cfg[label]["noisy"]:
            rid, noisy = line_fires(mods, d)
            for p in ("1", "2"):
                reads = []
                for slot, r in sorted(noisy.items()):
                    q = quiet.get(slot)
                    if r["line"] != p or q is None or q["line"] != p:
                        continue
                    reads.append(dict(slot=slot, stage=r["stage"], pattern=r["pattern"], latency=r["latency"], latency_quiet=q["latency"],
                                      u_mV=r["u_mV"], u_quiet_mV=q["u_mV"], du_mV=r["u_mV"] - q["u_mV"], dlat=r["latency"] - q["latency"],
                                      dlevel=r["level"] - q["level"]))
                ref = next(x for x in g6[label]["campaign_3"]["rows"] if x["run"] == rid and x["kind"] == f"c{p}")
                lat = [x["latency"] for x in reads]
                assert len(reads) == ref["fires"] and abs(statistics.stdev(lat) - ref["within_sd_units"]) <= 1e-12, (rid, p, len(reads), ref["fires"])
                dl, du = [x["dlat"] for x in reads], [x["du_mV"] for x in reads]
                mdl, mdu = statistics.fmean(dl), statistics.fmean(du)
                pooled += [(a - mdl, b - mdu) for a, b in zip(dl, du)]
                by_stage = {}
                for x in reads:
                    by_stage.setdefault(x["stage"], []).append(x["dlat"])
                rows.append(dict(run=rid, line=p, fires=len(reads), within_units=statistics.stdev(lat), within_diff_units=statistics.stdev(dl),
                                 quiet_sd_units=statistics.stdev([x["latency_quiet"] for x in reads]),
                                 offset_units=statistics.fmean([x["latency_quiet"] for x in reads]) - statistics.fmean(lat),
                                 du_mean_mV=mdu, du_sd_mV=statistics.stdev(du), u_quiet_range_mV=max(x["u_quiet_mV"] for x in reads) - min(x["u_quiet_mV"] for x in reads),
                                 mean_dlat_by_stage={k: statistics.fmean(v) for k, v in by_stage.items()}, reads=reads))
        sxx = sum(b * b for _, b in pooled)
        sxy = sum(a * b for a, b in pooled)
        syy = sum(a * a for a, _ in pooled)
        slope = sxy / sxx
        resid = [a - slope * b for a, b in pooled]
        dof = len(pooled) - len(rows)                        # one mean removed per row
        res[label] = dict(
            rows=rows, deck_slopes={p: dict(secant=v["slope_per_mV"], three_points=v["slope_three_points_per_mV"], dose_mV=v["dose_mV"]) for p, v in slopes.items()},
            pooled_within_rows=dict(reads=len(pooled), rows=len(rows), latency_sd_units=math.sqrt(syy / dof), du_sd_mV=math.sqrt(sxx / dof),
                                    slope_units_per_mV=slope, correlation=sxy / math.sqrt(sxx * syy), share_of_latency_variance_explained_by_du=sxy * sxy / (sxx * syy),
                                    residual_sd_units=math.sqrt(sum(x * x for x in resid) / (dof - 1))),
            summary=dict(w_units_rms=rms(r["within_units"] for r in rows), w_diff_units_rms=rms(r["within_diff_units"] for r in rows),
                         quiet_sd_units_rms=rms(r["quiet_sd_units"] for r in rows), du_sd_mV_rms=rms(r["du_sd_mV"] for r in rows),
                         du_mean_mV_rms=rms(r["du_mean_mV"] for r in rows), offset_units_rms=rms(r["offset_units"] for r in rows),
                         by_row={f'{r["run"][-7:]} line {r["line"]}': dict(within=r["within_units"], within_diff=r["within_diff_units"], du_sd_mV=r["du_sd_mV"], du_mean_mV=r["du_mean_mV"]) for r in rows}))
    Path(dest).write_text(json.dumps(res, indent=1) + "\n")
    f = lambda v: round(v, 5) if isinstance(v, float) else v
    for label in ("1x", "2x"):
        print(label, "deck slopes", {p: {k: f(x) for k, x in v.items()} for p, v in res[label]["deck_slopes"].items()})
        print("   pooled", {k: f(v) for k, v in res[label]["pooled_within_rows"].items()})
        print("   summary", {k: f(v) for k, v in res[label]["summary"].items() if k != "by_row"})
        for k, v in res[label]["summary"]["by_row"].items():
            print("     ", k, {a: f(b) for a, b in v.items()})
