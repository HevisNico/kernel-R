"""From the qualification runs to the bounds of each port. No simulation is run.

  closure.py DATA             -> QUALIFICATION.json   (DATA: the folder of the qualification runs, outside the repository)
  closure.py DATA --check     compares with the committed QUALIFICATION.json instead of writing it
  closure.py --table K        prints, from the committed file, the bounds of design K in the form that supervise.py reads

Every number is recomputed from the raw waveforms. The reserve of a port is counted, in mV, from the
capacitor voltage of its service threshold: reserve = 1000 * (U_S - u), with u the stored node minus
the summing node. Units of the kernel are 0.1 uV; bounds are rounded outwards.

Folders of DATA:  thr-CONFIG-PORT   threshold scans            reads-CONFIG-N   maps of the three reads
                  seq-CONFIG-LEAK   first supervised sequences, without noise (observer: stored node)
                  seq-CONFIG-top    sequences that go 0.1 mV above the capacity, to measure doses up to it; their reads are not services
                  noisy-, nz-       noisy sequences from which the read noise is measured
                  confK-, confnK-   confirmation of design K, without and with noise: never used to set a bound
                  eq-thr-, eq-reads-  threshold scans and maps replayed without the ammeter of the first runs
                  fingerprint       the check of the noise fingerprint
"""
import functools
import gzip
import hashlib
import json
import math
from pathlib import Path
import statistics
import sys
import tempfile

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import extract
import kernel as K
import sim

CONFIGS = json.loads((HERE / "configs.json").read_text())
JOINT = (0.250, 0.280)          # contract of the joint read: criterion P7 of ../circuit/PREDICTION.md
SINGLE = (0.5, 1.0)             # contract of a single read: one FIRE inside the pulse, well after a joint read
MARGIN = dict(threshold_mV=0.03, latency=0.0005, dose=0.005, loss=0.03, epsilon_mV=0.002)
DESIGNS = (0, 2, 3)             # noise margins, in standard deviations of the measured noise
NETLISTS = set()                # the kinds of deck met in the data: None (no junction area), "areas", "zero"
SOURCES = ["junction/netlist.py", "junction/areas.csv", "sim.py", "extract.py", "kernel.py", "supervise.py", "qualify.py", "closure.py", "configs.json", "runtime/spinit",
           "../circuit/cell.spice", "../circuit/blocks.spice", "../circuit/noise.json", "../circuit/spiceinit.txt"]


def units_up(mv):
    return math.ceil(mv * 1e4 - 1e-9)


def units_down(mv):
    return math.floor(mv * 1e4 + 1e-9)


def raw_blob(path):
    """Bytes of a file of a run. A waveform stored as `trace.raw.gz` to save room is read through gzip: the bytes are the same."""
    return path.read_bytes() if path.exists() else gzip.decompress(Path(str(path) + ".gz").read_bytes())


def raw_digest(folder):
    return hashlib.sha256(raw_blob(folder / "trace.raw")).hexdigest()


def read_raw(folder):
    if (folder / "trace.raw").exists():
        return extract.read_raw(folder / "trace.raw")
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "trace.raw").write_bytes(raw_blob(folder / "trace.raw"))
        return extract.read_raw(Path(tmp) / "trace.raw")


def deck_of(r):
    """The deck that the tools of this folder build today for the run recorded in r."""
    common = dict(ammeter=r.get("ammeter", True),         # the runs made before the ammeter was removed did not record it
                  junction=r.get("junction"))              # nor did those made before the junction areas
    NETLISTS.add(common["junction"])
    if "events" in r:
        return sim.deck(section=r["section"], temperature=r["temperature_C"], noise=r["noise"], leak_S=r["leak"][0][1], **common)
    c = CONFIGS[r["config"]]
    preset = dict(vinit1=r["preset_mV"][0] * 1e-3, vinit2=r["preset_mV"][1] * 1e-3) if r["kind"] == "reads" else {}
    return sim.deck(section=c["section"], temperature=c["temperature_C"], **common, **preset)


@functools.lru_cache(maxsize=None)
def rows_of(folder):
    """Record and re-extracted slots of one run, after checking that its waveform and its deck are the recorded ones
    and that the deck is the one the committed tools build."""
    r = json.loads((folder / "result.json").read_text())
    assert raw_digest(folder) == r["raw_sha256"], folder
    assert sim.digest(folder / "input.spice") == r["deck_sha256"] == hashlib.sha256(deck_of(r).encode()).hexdigest(), folder
    key = dict(raw_sha256=r["raw_sha256"], extract_sha256=sim.digest(HERE / "extract.py"))
    cache = folder / "slots.cache.json"          # a convenience beside the evidence, never used by --check
    if "--check" not in sys.argv and cache.exists() and json.loads(cache.read_text())["key"] == key:
        saved = json.loads(cache.read_text())
        r["fingerprint"] = saved["fingerprint"]
        return r, {int(k): v for k, v in saved["rows"].items()}
    d = read_raw(folder)
    last = max(x["slot"] for x in r["records"])
    r["fingerprint"] = extract.noise_fingerprint(d)
    rows = {k: extract.slot_record(d, k) for k in range(2, last + 1)}
    if "--check" not in sys.argv:
        cache.write_text(json.dumps(dict(key=key, fingerprint=r["fingerprint"], rows=rows)))
    return r, rows


def correct(name, x):
    lat = x["fire_latency"]
    window = JOINT if name == "joint" else SINGLE
    return x["fires"] == 1 and lat is not None and window[0] <= lat <= window[1] and x["writes1"] == 0 and x["writes2"] == 0


def thresholds(data):
    out = {}
    for c in CONFIGS:
        out[c] = []
        for p in (1, 2):
            r, rows = rows_of(data / f"thr-{c}-{p}")
            reads = [(x[f"u{p}_pre_pulse"], x["fire_latency"], x["fires"]) for x in rows.values() if x["sel"][p - 1] == 1 and x["amp"][p - 1] == 1]
            good = [(u, l) for u, l, f in reads if f == 1 and l is not None and l <= 1.0]
            ok = max(good)
            bad = min(u for u, l, f in reads if not (f == 1 and l is not None and l <= 1.0) and u > ok[0])
            monotone = all(a[1] <= b[1] + 1e-9 for a, b in zip(sorted(good), sorted(good)[1:]))
            out[c].append(dict(port=p, u_service_V=ok[0], latency_at_threshold=ok[1], first_incorrect_V=bad, bracket_uV=(bad - ok[0]) * 1e6,
                               correct_reads=len(good), latency_monotone=monotone,
                               trained_after=r["trained_after_reads"] if "trained_after_reads" in r else sum(1 for l in r["log"] if l["read"] and l["delta_mV"] == 0 and not l["fired"]),
                               **({"own_drift_mV_per_period": r["drift_V_per_period"] * 1e3} if "drift_V_per_period" in r else {})))
    return out


def reads_map(data, thr):
    """Latency of the three reads against the reserves, without noise: the map of presets and the supervised sequences."""
    out = {}
    for c in CONFIGS:
        us = [t["u_service_V"] for t in thr[c]]
        joint, single = [], [[], []]
        folders = sorted(x for x in data.glob(f"reads-{c}-*[0-9]") if x.is_dir()) + [data / f"seq-{c}-{x}" for x in ("base", "max", "top") if (data / f"seq-{c}-{x}" / "result.json").exists()]
        for f in folders:
            r, rows = rows_of(f)
            if "events" in r:
                reads = [(e["read"], rows[e["slot"]]) for e in r["events"] if e["phase"] == "read"]
            else:
                reads = [("port1", rows[2]), ("port2", rows[4]), ("joint", rows[6])]
            for name, x in reads:
                res = [(us[p] - x[f"u{p + 1}_pre_pulse"]) * 1e3 for p in (0, 1)]
                if x["fire_latency"] is None:
                    continue
                if name == "joint":
                    joint.append((res[0] + res[1], x["fire_latency"], abs(res[0] - res[1])))
                else:
                    p = 0 if name == "port1" else 1
                    single[p].append((res[p], x["fire_latency"]))
        out[c] = dict(joint=sorted(joint), single=[sorted(s) for s in single])
    return out


def crossing(points, level):
    """Sum of reserves at which the joint latency first falls below `level`, going up: linear interpolation between
    the two neighbours; without a crossing, the largest measured sum (no extrapolation)."""
    for (s0, l0, _), (s1, l1, _) in zip(points, points[1:]):
        if l0 >= level > l1:
            return s0 + (l0 - level) / (l0 - l1) * (s1 - s0)
    assert all(l >= level for _, l, _ in points)
    return points[-1][0]


def interp(points, x):
    return float(np.interp(x, [a for a, *_ in points], [b[1] for b in points]))


def local(points, x, half=0.05):
    """Value and slope of a measured curve at x; beyond its ends, the straight line of its last 0.1 mV."""
    inside = min(max(x, points[0][0] + half), points[-1][0] - half)
    slope = (interp(points, inside + half) - interp(points, inside - half)) / (2 * half)
    return interp(points, inside) + slope * (x - inside), slope, not points[0][0] <= x <= points[-1][0]


def noise(data, thr, maps):
    """Noise of the reads, from the noisy supervised sequences, against the noiseless curves of the same configuration."""
    out = {}
    for c in CONFIGS:
        folders = sorted(x for kind in ("noisy", "nz") for x in data.glob(f"{kind}-{c}-[0-9]") if (x / "result.json").exists())
        us = [t["u_service_V"] for t in thr[c]]
        dj, ds, dd, dl, n, beyond = [], [], [], [], 0, 0
        quiet = {s["leak_S"]: s for s in (sequence(data / f"seq-{c}-{x}", us) for x in ("base", "max"))}
        for f in folders:
            r, rows = rows_of(f)
            loss, net = steps(r, rows, us)
            ref = min(quiet.values(), key=lambda s: abs(s["leak_S"] - r["leak"][0][1]))
            for p in (0, 1):
                mid = statistics.mean(loss[p]) if loss[p] else statistics.mean(ref["loss_mV"][p]) * r["leak"][0][1] / ref["leak_S"]
                dl += [v - mid for v in loss[p]]
                dd += [v + mid - statistics.mean(ref["gross_dose_mV"][p]) for v in net[p]]
            for e in r["events"]:
                if e["phase"] != "read":
                    continue
                x = rows[e["slot"]]
                n += 1
                if x["fire_latency"] is None:
                    continue
                res = [(us[p] - x[f"u{p + 1}_pre_pulse"]) * 1e3 for p in (0, 1)]
                if e["read"] == "joint":
                    value, slope, outside = local(maps[c]["joint"], res[0] + res[1])
                    dj.append(x["fire_latency"] - value)
                else:
                    p = 0 if e["read"] == "port1" else 1
                    value, slope, outside = local(maps[c]["single"][p], res[p])
                    ds.append((x["fire_latency"] - value) / slope)
                beyond += outside
        out[c] = dict(runs=len(folders), with_ammeter=sum(rows_of(f)[0].get("ammeter", True) for f in folders), reads=n, reads_beyond_the_measured_curve=beyond, joint_reads=len(dj), single_reads=len(ds),
                      sd_joint_latency=statistics.stdev(dj), largest_joint_latency_shift=max(abs(v) for v in dj),
                      sd_single_as_reserve_mV=statistics.stdev(ds), largest_single_as_reserve_mV=max(abs(v) for v in ds),
                      doses=len(dd), sd_dose_mV=statistics.stdev(dd), largest_dose_shift_mV=max(abs(v) for v in dd),
                      losses=len(dl), largest_loss_shift_mV=max((abs(v) for v in dl), default=None))
    return out


def steps(r, rows, us):
    """Change of reserve from one observation to the next, per port: the losses of the waits and the net doses of the maintenances."""
    marks = [e for e in r["events"] if e["phase"] in ("maintenance", "end")]
    obs = [[(us[p] - rows[e["slot"] - 1][f"u{p + 1}_obs"]) * 1e3 for p in (0, 1)] for e in marks]
    loss, net = [[], []], [[], []]
    for i, e in enumerate(marks[:-1]):
        for p in (0, 1):
            step = obs[i + 1][p] - obs[i][p]
            if e["action"][p] == "maintenance":
                net[p].append(step)
            else:
                loss[p].append(-step)
    return loss, net


def sequence(folder, us):
    """Losses, doses and reads of one supervised sequence, in the capacitor coordinate."""
    r, rows = rows_of(folder)
    marks = [e for e in r["events"] if e["phase"] in ("maintenance", "end")]
    loss, net = steps(r, rows, us)
    wrong_write = sum(rows[e["slot"]][f"writes{p + 1}"] != (1 if e["action"][p] == "maintenance" else 0) for e in marks[:-1] for p in (0, 1))
    reads = [(e["read"], rows[e["slot"]]) for e in r["events"] if e["phase"] == "read"]
    at_reads = [[(us[p] - x[f"u{p + 1}_pre_pulse"]) * 1e3 for _, x in reads] for p in (0, 1)]
    joint = [x["fire_latency"] for n, x in reads if n == "joint" and x["fire_latency"] is not None]
    single = [x["fire_latency"] for n, x in reads if n != "joint" and x["fire_latency"] is not None]
    gross = [[v + statistics.mean(loss[p]) for v in net[p]] if loss[p] else [] for p in (0, 1)]
    after = [[(us[p] - rows[b["slot"] - 1][f"u{p + 1}_obs"]) * 1e3 for a, b in zip(marks, marks[1:]) if a["action"][p] == "maintenance"] for p in (0, 1)]
    capacitor = r.get("observer") == "capacitor"
    read_slots = {e["slot"] for e in r["events"] if e["phase"] == "read"}
    return dict(noise=r["noise"], leak_S=r["leak"][0][1], observer=r.get("observer", "stored node"), services=len(reads),
                correct=sum(correct(n, x) for n, x in reads), incorrect=[dict(period=i, read=n, fires=x["fires"], latency=x["fire_latency"])
                                                                         for i, (n, x) in enumerate(reads) if not correct(n, x)],
                refused=r["refused_at_period"], entered_at_slot=r["entered_at_slot"],
                preparation_writes=[sum(rows[e["slot"]][f"writes{p + 1}"] for e in r["events"] if e["phase"] == "preparation") for p in (0, 1)],
                maintenance=[sum(e["action"][p] == "maintenance" for e in marks[:-1]) for p in (0, 1)], writes_not_as_commanded=wrong_write,
                slots_without_read=len(rows) - len(read_slots), fires_outside_reads=sum(x["fires"] for k, x in rows.items() if k not in read_slots),
                largest_reserve_after_maintenance_mV=[max(v) if v else None for v in after],
                loss_mV=[[min(v), max(v)] if v else None for v in loss], gross_dose_mV=[[min(v), max(v)] if v else None for v in gross],
                joint_latency=[min(joint), max(joint)] if joint else None, single_latency=[min(single), max(single)] if single else None,
                reserve_at_reads_mV=[[min(v), max(v)] if v else None for v in at_reads], wall_s=r["wall_s"], points=r["points"],
                noise_fingerprint=r["fingerprint"], bounds=r["bounds"],
                observer_error_uV=max(abs(e["observed_V"][p] - rows[e["slot"] - 1][f"u{p + 1}_obs"]) for e in marks for p in (0, 1)) * 1e6 if capacitor else None,
                kernel_enclosure_broken=sum(1 for i, e in enumerate(marks[:-1]) for p in (0, 1) if capacitor and e["kernel"][p]["lower"] is not None
                                            and not e["kernel"][p]["lower"] <= round((us[p] - rows[e["slot"] - 1][f"u{p + 1}_obs"]) / K.UNIT) <= e["kernel"][p]["upper"]) if capacitor else None)


def sequences(data, thr, kind="seq"):
    out = {}
    for f in sorted(x for x in data.glob(f"{kind}-*") if (x / "result.json").exists()):
        c = next(k for k in CONFIGS if f.name.startswith(f"{kind}-{k}-"))
        out[f.name] = dict(config=c, **sequence(f, [t["u_service_V"] for t in thr[c]]))
    return out


def doses(seqs):
    """Gross dose of a maintenance cycle and loss per period at the base leak, per configuration and port, without noise."""
    out = {}
    for c in CONFIGS:
        gross, base, top, slope, points = [[], []], [[], []], [[], []], [[], []], [[], []]
        for s in seqs.values():
            if s["config"] != c or s["noise"]:
                continue
            for p in (0, 1):
                gross[p] += s["gross_dose_mV"][p] or []
                top[p].append(s["largest_reserve_after_maintenance_mV"][p])
                slope[p] += [v / s["leak_S"] for v in s["loss_mV"][p] or []]
                points[p] += [(s["leak_S"], v) for v in s["loss_mV"][p] or []]
                if abs(s["leak_S"] - 1e-11) < 1e-15:
                    base[p] += s["loss_mV"][p] or []
        out[c] = dict(gross_dose_mV=[[min(g), max(g)] for g in gross], loss_at_1e11_ohm_mV=[[min(b), max(b)] for b in base],
                      loss_per_siemens_mV=[[min(v), max(v)] for v in slope], doses_measured_up_to_reserve_mV=[max(v) for v in top])
        # the loss as a line in the imposed conductance: what the cell loses by itself, and what each siemens adds
        line = []
        for pts in points:
            lo, hi = min(g for g, _ in pts), max(g for g, _ in pts)
            mean = lambda g: statistics.mean(v for x, v in pts if x == g)
            k = (mean(hi) - mean(lo)) / (hi - lo)
            line.append(dict(mV_per_siemens=k, own_loss_mV=[min(v - k * g for g, v in pts), max(v - k * g for g, v in pts)], leaks_S=[lo, hi]))
        out[c]["loss_line"] = line
    return out


def designs(thr, maps, nz, dz, own=False):
    """Bounds of each port for each noise margin k (in standard deviations). H is what the room condition leaves.

      S     margin on the threshold, plus k sd of the single read counted as reserve
      C     half the sum of reserves at which the joint latency reaches its lower limit plus a margin plus k sd
      D     the measured gross doses, widened by a margin and by k sd of the dose
      eps   a fixed bound on the error of a report
      H     (C - S - 2 eps - Dmax) / 2, rounded down; the conductance that loses H per period, with a margin on the slope

    With own=False the loss is taken proportional to the imposed conductance (the netlists without junction areas, where the
    cell loses almost nothing by itself). With own=True it is the measured line: the loss of the cell alone plus the part of
    the conductance, both with the margin; the largest leak can then be negative: the cell alone loses more than H.
    """
    out = {}
    for c in CONFIGS:
        n = nz[c]
        out[c] = {}
        for k in DESIGNS:
            level = JOINT[0] + MARGIN["latency"] + k * n["sd_joint_latency"]
            limit = crossing(maps[c]["joint"], level)
            ports = []
            for p in (0, 1):
                dmin = units_down(dz[c]["gross_dose_mV"][p][0] - MARGIN["dose"] - k * n["sd_dose_mV"])
                dmax = units_up(dz[c]["gross_dose_mV"][p][1] + MARGIN["dose"] + k * n["sd_dose_mV"])
                S = units_up(MARGIN["threshold_mV"] + k * n["sd_single_as_reserve_mV"])
                eps = units_up(MARGIN["epsilon_mV"])
                C = units_down(limit / 2)
                linear = units_down(dz[c]["doses_measured_up_to_reserve_mV"][p])
                H = (min(C, linear) - S - 2 * eps - dmax) // 2
                b = K.Bounds(S=S, H=max(H, 0), Dmin=dmin, Dmax=dmax, linear_capacity=linear, semantic_capacity=C, epsilon=eps)
                if own:
                    line = dz[c]["loss_line"][p]
                    leak = (max(H, 0) / 1e4 / (1 + MARGIN["loss"]) - line["own_loss_mV"][1]) / line["mV_per_siemens"]
                    extra = dict(own_loss_mV=line["own_loss_mV"][1], holds_the_reference_leak=H >= 0 and leak >= 1e-11)
                else:
                    leak, extra = max(H, 0) / 1e4 / (dz[c]["loss_per_siemens_mV"][p][1] * (1 + MARGIN["loss"])), {}
                ports.append(dict(bounds=vars(b), well_formed=H >= 0 and b.well_formed(), room_for_2H_units=min(C, linear) - S - 2 * eps - dmax,
                                  largest_loss_per_period_mV=max(H, 0) / 1e4, largest_leak_S=leak, largest_leak_over_1e11_ohm=leak / 1e-11, **extra))
            out[c][str(k)] = dict(joint_level=level, sum_limit_mV=limit, joint_curve_crossed=limit < maps[c]["joint"][-1][0],
                                  well_formed=all(x["well_formed"] for x in ports), ports=ports)
    return out


def confirmation(data, thr, dz, plan):
    """The sequences run with the bounds of a design, after it was fixed: what the kernel and the reads did."""
    out = {}
    for k in DESIGNS:
        for kind in (f"conf{k}", f"confn{k}"):
            for name, s in sequences(data, thr, kind).items():
                design = [x["bounds"] for x in plan[s["config"]][str(k)]["ports"]]
                top = [b["semantic_capacity"] / 1e4 for b in design]
                out[name] = dict(design=k, bounds_are_the_design=s["bounds"] == design, **s,
                                 reads_inside_floor_and_capacity=all(design[p]["S"] / 1e4 <= s["reserve_at_reads_mV"][p][0] and s["reserve_at_reads_mV"][p][1] <= top[p]
                                                                    for p in (0, 1)))
    return out


def summary(conf):
    """Counts of the confirmation, per design and with or without noise."""
    out = {}
    for name, s in conf.items():
        g = out.setdefault(f"design {s['design']}, {'noise' if s['noise'] else 'no noise'}", dict(
            sequences=0, services=0, correct=0, refusals=0, writes_not_as_commanded=0, fires_outside_reads=0, enclosures_broken=0, reads_outside_floor_and_capacity=0,
            bounds_not_the_design=0, smallest_joint_latency=1.0, largest_single_latency=0.0, largest_observer_error_uV=0.0, wall_s=[]))
        g["sequences"] += 1
        g["services"] += s["services"]
        g["correct"] += s["correct"]
        g["refusals"] += sum(x is not None for x in s["refused"])
        g["writes_not_as_commanded"] += s["writes_not_as_commanded"]
        g["fires_outside_reads"] += s["fires_outside_reads"]
        g["enclosures_broken"] += s["kernel_enclosure_broken"]
        g["reads_outside_floor_and_capacity"] += not s["reads_inside_floor_and_capacity"]
        g["bounds_not_the_design"] += not s["bounds_are_the_design"]
        g["smallest_joint_latency"] = min(g["smallest_joint_latency"], s["joint_latency"][0])
        g["largest_single_latency"] = max(g["largest_single_latency"], s["single_latency"][1])
        g["largest_observer_error_uV"] = max(g["largest_observer_error_uV"], s["observer_error_uV"])
        g["wall_s"].append(s["wall_s"])
    for g in out.values():
        g["wall_s"] = [min(g["wall_s"]), statistics.mean(g["wall_s"]), max(g["wall_s"])]
    return out


def table(k, name="QUALIFICATION.json"):
    q = json.loads((HERE / name).read_text())
    return {c: dict(bounds=[x["bounds"] for x in d[str(k)]["ports"]], v_service_V=[x["u_service_V"] for x in q["thresholds"][c]],
                    largest_leak_S=min(x["largest_leak_S"] for x in d[str(k)]["ports"]))
            for c, d in q["designs"].items() if d[str(k)]["well_formed"] and all(x.get("holds_the_reference_leak", True) for x in d[str(k)]["ports"])}


def aborted(data):
    """Runs that the simulator did not finish: a folder with a deck and no record. They are listed, never hidden."""
    out = []
    full = json.loads((data / "DISK_FULL.json").read_text()) if (data / "DISK_FULL.json").exists() else dict(runs=[])
    cut = {r["run"] for r in full["runs"]}
    for folder in sorted(x for x in data.iterdir() if x.is_dir() and (x / "input.spice").exists() and not (x / "result.json").exists()):
        log = (folder / "session.log").read_text(errors="replace").splitlines()
        deck = (folder / "input.spice").read_text()
        out.append(dict(run=folder.name, ammeter="\nvdose " in deck, noise="trnoise" in deck, deck_sha256=sim.digest(folder / "input.spice"),
                        message=next((l.strip() for l in log if "timestep too small" in l.lower()),
                                     "none: " + full["reason"] if folder.name in cut else "no message found")))
    assert cut >= {a["run"] for a in out if a["message"].startswith("none: ")}
    return out


def disk_full(data):
    """The runs that a full disk cut or prevented, as recorded when it happened; each was run again under the same name followed by -again."""
    if not (data / "DISK_FULL.json").exists():
        return None
    full = json.loads((data / "DISK_FULL.json").read_text())
    return dict(reason=full["reason"], cut_while_running=sorted(r["run"] for r in full["runs"] if r["folder"]),
                never_started=sorted(r["run"] for r in full["runs"] if not r["folder"]),
                run_again=sorted(r["run"] + "-again" for r in full["runs"] if (data / (r["run"] + "-again") / "result.json").exists()))


def identity(data):
    """The expanded deck with all areas at zero against the deck that is not expanded: the same points?"""
    rows = []
    for folder in sorted(x for x in data.glob("id-zero-*") if x.is_dir()):
        other = data / folder.name.replace("id-zero-", "id-plain-")
        new, old = json.loads((folder / "result.json").read_text()), json.loads((other / "result.json").read_text())
        assert new["junction"] == "zero" and old["junction"] is None and new["ammeter"] is old["ammeter"] is False
        assert raw_digest(folder) == new["raw_sha256"] and raw_digest(other) == old["raw_sha256"]
        a, b = read_raw(folder), read_raw(other)
        rows.append(dict(config=new["config"], points=len(a), identical=a.shape == b.shape and bool(np.array_equal(a, b, equal_nan=True))))
    return rows


def equivalence(data):
    """The same sessions with and without the ammeter of the write current: largest differences, slot by slot."""
    if not list(data.glob("eq-*")):
        return None
    rows = []
    for folder in sorted(x for x in data.glob("eq-*") if x.is_dir()):
        new, a = rows_of(folder)
        old, b = rows_of(data / folder.name[3:])
        assert new["ammeter"] is False and old.get("ammeter", True) and set(a) == set(b), folder
        same = all(a[k][key] == b[k][key] for k in a for key in ("sel", "amp", "fires", "writes1", "writes2"))
        volts = max(abs(a[k][key] - b[k][key]) for k in a for key in ("u1_pre_pulse", "u2_pre_pulse", "u1_obs", "u2_obs"))
        latency = max((abs(a[k]["fire_latency"] - b[k]["fire_latency"]) for k in a if a[k]["fire_latency"] is not None and b[k]["fire_latency"] is not None), default=0.0)
        rows.append(dict(run=folder.name[3:], slots=len(a), same_fires_and_writes=same, largest_difference_uV=volts * 1e6, largest_latency_difference=latency))
    return dict(sessions=rows, all_same_fires_and_writes=all(r["same_fires_and_writes"] for r in rows),
                largest_difference_uV=max(r["largest_difference_uV"] for r in rows), largest_latency_difference=max(r["largest_latency_difference"] for r in rows))


def inventory(data):
    """Every deck, simulator log, record and raw waveform of the qualification runs: kept outside Git, identified here."""
    files = []
    for folder in sorted(x for x in [*data.iterdir(), *(data / "fingerprint").iterdir()] if x.is_dir() and not x.is_symlink()):
        for name in ("input.spice", "session.log", "result.json", "trace.raw", "fakepid.c"):
            stored = (folder / name).is_file() or (name == "trace.raw" and (folder / "trace.raw.gz").is_file())
            if stored and (folder / "input.spice").exists():
                blob = raw_blob(folder / name)          # a waveform kept through gzip is identified by its own bytes, not by the archive's
                files.append(dict(path=(folder / name).relative_to(data).as_posix(), bytes=len(blob), sha256=hashlib.sha256(blob).hexdigest()))
    return files


def main():
    if sys.argv[1] == "--table":
        print(json.dumps(table(int(sys.argv[2]), *sys.argv[3:4]), indent=1))
        return
    data = Path(sys.argv[1]).resolve()
    thr = thresholds(data)
    maps = reads_map(data, thr)
    nz = noise(data, thr, maps)
    seqs = sequences(data, thr)
    seqs.update(sequences(data, thr, "noisy"))
    seqs.update(sequences(data, thr, "nz"))
    dz = doses(seqs)
    assert len(NETLISTS) == 1, "runs on different netlists in one qualification: " + repr(NETLISTS)
    junction = NETLISTS == {"areas"}
    plan = designs(thr, maps, nz, dz, own=junction)
    conf = confirmation(data, thr, dz, plan)
    noisy = {name: s["noise_fingerprint"] for name, s in {**seqs, **conf}.items() if s["noise"]}
    result = dict(status="phase-1 qualification, exploratory; no registered run and no leakage jump",
                  netlist="with the junction areas of stage J on every transistor" if junction else "without junction areas",
                  loss_model="measured line: own loss plus imposed conductance" if junction else "proportional to the imposed conductance",
                  contract=dict(joint=JOINT, single=SINGLE),
                  margins=MARGIN, source_sha256={name: sim.digest(HERE / name) for name in SOURCES}, thresholds=thr,
                  reads_map={c: dict(joint=[list(x) for x in m["joint"]], single=[[list(x) for x in s] for s in m["single"]]) for c, m in maps.items()},
                  read_noise=nz, sequences=seqs, doses=dz, designs=plan, confirmation=conf, confirmation_summary=summary(conf),
                  noise_fingerprints=dict(noisy_sequences=len(noisy), distinct=len(set(noisy.values()))),
                  fingerprint_check=json.loads((data / "fingerprint" / "result.json").read_text()),
                  aborted_runs=aborted(data), disk_full=disk_full(data), ammeter_equivalence=equivalence(data), identity_of_the_expanded_deck=identity(data),
                  evidence_files=inventory(data))
    target = HERE / (sys.argv[2] if len(sys.argv) > 2 and not sys.argv[2].startswith("--") else "QUALIFICATION.json")
    text = json.dumps(result, indent=1) + "\n"
    if "--check" in sys.argv:
        assert json.loads(target.read_text()) == json.loads(text), "the qualification data do not give the committed QUALIFICATION.json"
        print("PASS: every number of QUALIFICATION.json recomputed from the raw waveforms")
    else:
        target.write_text(text)
        print("written", target, len(result["evidence_files"]), "evidence files")


if __name__ == "__main__":
    main()
