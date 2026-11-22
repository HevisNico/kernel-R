"""The noise sensitivity values b, w and d of the family rehearsal (PREDICTION.md 7, amendment 2a C1), from the noisy
F2 runs, by campaign 3's definitions. New code. It reads no run by itself; `main` reads the runs named on its command
line, through the network code's reader (family_reads.record_of with rows).

Campaign 3's definitions, reused (main at 14cc793a):
  [C3a] research/network-circuit/phase1/constants.py (SHA-256 a36dc136...), `port`, its noise part:
        - a noisy run of a port counts when its word is the word of the run without noise (s^first F^...) and it has
          at least 3 FIREs;
        - run offset = (median latency of the FIREs after the first one, without noise - mean FIRE latency of the
          noisy run) / slope;
        - within-run scatter: sum of (latency - mean of its run)^2 / slope^2 over the counted runs, over the number of
          FIREs minus one per run; within = sqrt(that sum / count) when count >= 8;
        - doses: the steps of the silent reads of the noisy runs.
  [C3b] the same file, `instance`: dose deviation = noisy step - the port's dose without noise.
  [C3c] research/network-noise-study/validation/vanalyze.py (SHA-256 82627bc3...), `constants`, the pooled values:
        between = sqrt(mean of the run offsets^2); within = sqrt(pooled squares / pooled count);
        per_dose = sqrt(mean of the dose deviations^2).
They are re-expressed on the family's reads (reads4.network_reads' rows) as follows [readings of this code]:
  - the pulses of a port are its reads in its training slots: layer 1 for a port of a first-layer cell, the layer-2
    slots whose arrival is on that line for a port of c;
  - a pulse's latency is the read's FIRE latency (units); its step is the read's move_mV on that port
    (u before - u after, mV), taken on silent reads only;
  - the slope (decided 2026-11-22): campaign 3's `secant` [C3a, reused as written] of the fired reads' (u_before_mV,
    latency) of the instance's own guard-on calibration deck(s), at the trained level, through the frozen
    reads4.calibration_reads(tr, result, record["reads"]) (as campaign 5's predicted.py, line 458, calls it):
      a port of a pair cell   the cell's "both" reads of the plain guard-on deck (cal-on), u of that port;
      a port of a unary cell  the cell's "port P at 1.0" reads of the guard-on unary deck (cal-on-unary);
      a line P of c           c's "port P" reads of the plain guard-on deck;
    the trained level is the port's u_before_mV at its first FIRE in the instance's run without noise;
  - the dose without noise (decided 2026-11-22): the mean move_mV of the port's silent reads in the instance's run
    without noise.
Output: per port, per instance, and pooled over every counted port of every instance.

  noise_constants.py PREDICTED.json RUNS_DIR DECKS_DIR -- INSTANCE QUIET_ID NOISY_ID... [-- ...]
      DECKS_DIR/<seed>-cal-on and DECKS_DIR/<seed>-cal-on-unary: the instance's guard-on decks (B2 and top-up
      evidence, fetched by name and checked against their sums before this is run)
"""
import json
import math
import statistics
from pathlib import Path
import sys

MIN_FIRES = 3          # [C3a] len(lat) >= 3
MIN_WITHIN = 8         # [C3a] count >= 8 for a port's within-run value
MIN_OFFSETS = 8        # [C3a] instance: len(offsets) >= 8 for noise_between_runs


def secant(points, u):
    """[C3a] constants.secant, as written: slope of latency against u at `u`, from the two measured points around it
    (or the two nearest), the points of one stored state (within 0.02 mV) merged first."""
    points = sorted(set(points))
    merged = []
    for p in points:
        if merged and p[0] - merged[-1][0][0] < 0.02:
            merged[-1].append(p)
        else:
            merged.append([p])
    points = [(statistics.mean(x[0] for x in g), statistics.mean(x[1] for x in g)) for g in merged]
    assert len(points) >= 2
    i = min(max(sum(1 for p in points if p[0] <= u), 1), len(points) - 1)
    (u0, l0), (u1, l1) = points[i - 1], points[i]
    return (l1 - l0) / (u1 - u0)


def calibration_points(cal_rows, port, kind):
    """[decided] The fired calibration reads of a port as (u_before_mV, latency). cal_rows: reads4.calibration_reads of
    the deck; kind: "pair", "unary" or "line" (the port's cell kind; a port of c is a line)."""
    cell, p = port[0], port[1]
    want = {"pair": "both", "unary": f"port {p} at 1.0", "line": f"port {p}"}[kind]
    return [(r["ports"][p]["u_before_mV"], r["latency"]) for r in cal_rows if r["cell"] == cell and r["read"] == want and r["fire"]]


def trained_level(quiet_pulses):
    """[decided] The port's u before its first FIRE in the run without noise."""
    return next(x["u_before_mV"] for x in quiet_pulses if x["fire"])


def quiet_dose(quiet_pulses):
    """[decided] The mean step of the port's silent reads in the run without noise."""
    steps = [x["step_mV"] for x in quiet_pulses if not x["fire"]]
    assert steps, "the run without noise has no silent read on this port"
    return statistics.mean(steps)


def inputs(member, unary_ports, quiet_rows, cal_on_rows, cal_on_unary_rows=None):
    """{port: (slope, dose)} of one instance: its learning ports (campaign_predict.ports_of's set)."""
    import family_predict as FP
    out = {}
    for c, k in FP.kinds(member).items():
        for p in ((1, 2) if k == "pair" else (unary_ports[c],)):
            out[f"{c}{p}"] = (k, cal_on_rows if k == "pair" else cal_on_unary_rows)
    for c in FP.kinds(member):
        out[f"c{FP.LINE_PORT[c]}"] = ("line", cal_on_rows)
    res = {}
    for port, (kind, rows) in out.items():
        assert rows is not None, f"no calibration deck for {port}"
        q = pulses(quiet_rows, port)
        res[port] = (secant(calibration_points(rows, port, kind), trained_level(q)), quiet_dose(q))
    return res


def pulses(rows, port):
    """[reading] The training pulses of one port ("a1", "b2", "c1"...) in a run: (fire, latency, step_mV) per read."""
    cell, p = port[0], port[1]
    out = []
    for x in rows:
        r = x["reads"].get(cell)
        if r is None:
            continue
        if cell != "c" and x["stage"] == "layer 1":
            pass
        elif cell == "c" and x["stage"] == "layer 2" and {a["port"] for a in r.get("arrivals", [])} == {int(p)}:
            pass
        else:
            continue
        out.append(dict(fire=bool(r["fire"]), latency=r["latency"], step_mV=r["ports"][p]["move_mV"], u_before_mV=r["ports"][p].get("u_before_mV")))
    return out


def word(P):
    return "".join("F" if x["fire"] else "s" for x in P)


def port_noise(quiet, noisy, slope, dose_mV):
    """[C3a, C3b] One port. quiet: its pulses without noise; noisy: {run id: pulses}; slope: latency per mV; dose_mV:
    its dose without noise."""
    w = word(quiet)
    assert "F" in w, "the run without noise never fires on this port"
    first = w.index("F")
    assert w == "s" * first + "F" * (len(w) - first) and len(w) - first >= 2, f"the word without noise is {w}"
    later = [x["latency"] for x in quiet[first + 1:]]
    ref = statistics.median(later)
    runs, offsets, squares, count, doses = [], [], 0.0, 0, []
    for rid, N in sorted(noisy.items()):
        nw = word(N)
        doses += [x["step_mV"] for x in N if not x["fire"]]
        lat = [x["latency"] for x in N if x["fire"]]
        same = nw == "s" * first + "F" * (len(nw) - first) and len(lat) >= MIN_FIRES
        e = dict(run=rid, word=nw, same_word_as_without_noise=same)
        if same:
            mean = statistics.mean(lat)
            e.update(fires=len(lat), offset_mV=(ref - mean) / slope, within_sd_mV=statistics.stdev(lat) / slope)
            offsets.append(e["offset_mV"])
            squares += sum((v - mean) ** 2 for v in lat) / slope ** 2
            count += len(lat) - 1
        runs.append(e)
    out = dict(word_without_noise=w, latency_later_median=ref, slope_per_mV=slope, dose_mV=dose_mV, noisy_runs=runs,
               run_offsets_mV=offsets, noisy_doses_mV=doses, dose_deviations_mV=[x - dose_mV for x in doses],
               within_squares=squares, within_count=count)
    if count >= MIN_WITHIN:
        out["within_run_mV"] = math.sqrt(squares / count)
    return out


def instance(ports):
    """[C3b] {port: port_noise(...)} of one instance."""
    offsets = [x for p in ports.values() for x in p["run_offsets_mV"]]
    devs = [x for p in ports.values() for x in p["dose_deviations_mV"]]
    out = dict(ports=ports, run_offsets=len(offsets), noisy_doses=len(devs),
               dose_noise_sd_mV=math.sqrt(statistics.mean(x * x for x in devs)) if devs else None)
    if len(offsets) >= MIN_OFFSETS:
        out["noise_between_runs_mV"] = math.sqrt(statistics.mean(x * x for x in offsets))
    return out


def pooled(instances):
    """[C3c] over every port of every instance: b (between), w (within) and d (per dose), in mV."""
    offsets = [x for i in instances.values() for p in i["ports"].values() for x in p["run_offsets_mV"]]
    devs = [x for i in instances.values() for p in i["ports"].values() for x in p["dose_deviations_mV"]]
    squares = sum(p["within_squares"] for i in instances.values() for p in i["ports"].values())
    count = sum(p["within_count"] for i in instances.values() for p in i["ports"].values())
    return dict(between_mV=math.sqrt(statistics.mean(x * x for x in offsets)) if offsets else None,
                within_mV=math.sqrt(squares / count) if count else None,
                per_dose_mV=math.sqrt(statistics.mean(x * x for x in devs)) if devs else None,
                run_offsets=len(offsets), doses=len(devs), within_count=count)


def values(per_instance):
    """per_instance: {instance: dict(quiet=rows, noisy={run id: rows}, slopes={port: s}, doses={port: mV})}."""
    inst = {}
    for k, v in per_instance.items():
        ports = {p: port_noise(pulses(v["quiet"], p), {r: pulses(rows, p) for r, rows in v["noisy"].items()}, v["slopes"][p], v["doses"][p])
                 for p in v["slopes"]}
        inst[k] = instance(ports)
    return dict(definitions="campaign 3: network-circuit/phase1/constants.py a36dc136, network-noise-study/validation/vanalyze.py 82627bc3",
                per_instance=inst, pooled=pooled(inst))


def deck_rows(folder):
    """reads4.calibration_reads of one deck folder (record.json, evidence/result.json, evidence/trace.raw)."""
    import measure
    import reads4
    folder = Path(folder)
    rec = json.loads((folder / "record.json").read_text())
    res = json.loads((folder / "evidence" / "result.json").read_text())
    return reads4.calibration_reads(measure.Trace(folder / "evidence" / "trace.raw"), res, rec["reads"])


def main(a):
    import family_reads as R
    pred, runs_dir, decks = Path(a[0]), Path(a[1]), Path(a[2])
    rec = {(x["seed"], x["member"]): x for x in json.loads(pred.read_text())["instances"]}
    st = R.statuses(runs_dir)
    groups, cur = [], []
    for x in a[3:] + ["--"]:
        if x == "--":
            if cur:
                groups.append(cur)
            cur = []
        else:
            cur.append(x)
    per = {}
    for g in groups:
        k, quiet, noisy = g[0], g[1], g[2:]
        seed, member = int(k.split("-")[0]), k.split("-")[1]
        x = rec[(seed, member)]
        read = lambda rid: R.record_of(runs_dir / rid, st[rid], with_rows=True, predicted=pred)
        q = read(quiet)
        assert q["counts"], f"refused: the run without noise {quiet} does not count"
        nz = {r: read(r) for r in noisy}
        unary = (x.get("unary_ports") or {})
        un = deck_rows(decks / f"{seed}-cal-on-unary") if unary else None
        sd = inputs(member, unary, q["rows"], deck_rows(decks / f"{seed}-cal-on"), un)
        per[k] = dict(quiet=q["rows"], noisy={r: v["rows"] for r, v in nz.items() if v["counts"]},
                      slopes={p: v[0] for p, v in sd.items()}, doses={p: v[1] for p, v in sd.items()},
                      not_counted=[r for r, v in nz.items() if not v["counts"]])
    out = values(per)
    out["not_counted"] = {k: v["not_counted"] for k, v in per.items()}
    return out


if __name__ == "__main__":
    assert __debug__, "refused: not with python -O, the guards are asserts"
    print(json.dumps(main(sys.argv[1:]), indent=1))
