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
  - `slope` (latency per mV at the trained state) and `dose_mV` (the port's dose without noise) are INPUTS, per port.
    Campaign 3 took both from the port's isolated scan reads; their family source is a choice made outside this file.
Output: per port, per instance, and pooled over every counted port of every instance.

  noise_constants.py PREDICTED.json SLOPES.json RUNS_DIR QUIET_ID NOISY_ID...   prints the values as JSON
"""
import json
import math
import statistics
from pathlib import Path
import sys

MIN_FIRES = 3          # [C3a] len(lat) >= 3
MIN_WITHIN = 8         # [C3a] count >= 8 for a port's within-run value
MIN_OFFSETS = 8        # [C3a] instance: len(offsets) >= 8 for noise_between_runs


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
        out.append(dict(fire=bool(r["fire"]), latency=r["latency"], step_mV=r["ports"][p]["move_mV"]))
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


def main(a):
    """PREDICTED.json SLOPES.json RUNS_DIR then groups `INSTANCE QUIET_ID NOISY_ID...` separated by '--'.
    SLOPES.json: {instance: {slopes: {port: s}, doses: {port: mV}}}."""
    import family_reads as R
    pred, slopes, runs_dir = Path(a[0]), json.loads(Path(a[1]).read_text()), Path(a[2])
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
        rec = lambda rid: R.record_of(runs_dir / rid, st[rid], with_rows=True, predicted=pred)
        q = rec(quiet)
        assert q["counts"], f"refused: the run without noise {quiet} does not count"
        nz = {r: rec(r) for r in noisy}
        per[k] = dict(quiet=q["rows"], noisy={r: v["rows"] for r, v in nz.items() if v["counts"]},
                      slopes=slopes[k]["slopes"], doses=slopes[k]["doses"])
    return values(per)


if __name__ == "__main__":
    assert __debug__, "refused: not with python -O, the guards are asserts"
    print(json.dumps(main(sys.argv[1:]), indent=1))
