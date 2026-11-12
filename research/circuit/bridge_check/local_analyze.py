"""Window endpoints, local increments and latch events, by the rules of GAIN_PROTOCOL.md and LOCAL_PROTOCOL.md.

No simulation is run. Inputs: the frozen DC curves (gain_runs/), the frozen global fit
(gain_summary.json), the campaign results (../results/) and the five raw traces of the rest
replays (runs/*/trace.txt.gz, kept in the private repository; their SHA-256 is in metadata.json).

Writes window_samples.csv, latch_events.csv, local_summary.json and LOCAL_RESULTS.md.
A run whose trace is absent is reported as not evaluable; nothing is substituted.
"""
import csv
import glob
import gzip
import hashlib
import json
import math
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
TU, PERIOD, OFFSET = 20e-6, 440e-6, 4.1e-6
CS, CF = 400e-15, 30e-12
GRID = 0.0005
COL = dict(t=0, vq=1, p=2, cmpm=3, vrefmn=4, vmem1=5, vmem2=6, vs1=7, sum1=8, a1=9, b1=10, si1=11, vs2=12, sum2=13, a2=14, b2=15, si2=16)
DASH = "—"


# ---- DC curves
def curves(temp):
    manifest = json.loads((HERE / "gain_manifest.json").read_text())
    out = []
    for run in manifest["runs"]:
        if run["temperature_C"] != temp:
            continue
        with gzip.open(HERE / "gain_runs" / run["name"] / "dc.txt.gz", "rt") as fh:
            data = np.loadtxt(fh)
        out.append((run, data[:, 1], np.log(-data[:, 2] / run["input_A"])))
    return out


def observed_range(temp, extra):
    """Stored voltages seen at this temperature: the campaign CSVs, the design start, and `extra`."""
    names = {-40: ["pvt_tt_m40"], 125: ["pvt_tt_125"]}.get(temp)
    files = [ROOT / "results" / f"{n}.csv" for n in names] if names else [
        Path(p) for p in sorted(glob.glob(str(ROOT / "results" / "*.csv"))) if Path(p).stem not in ("pvt_tt_m40", "pvt_tt_125")]
    values = [0.3895] + list(extra)
    for path in files:
        with path.open(newline="") as fh:
            for row in csv.DictReader(fh):
                values += [float(row["vmem1"]), float(row["vmem2"])]
    return min(values), max(values), len(files)


def local_fit(temp, extra):
    """Temperature-specific slope on the observed range, and the largest distance of an adjacent-grid secant to it."""
    lo, hi, files = observed_range(temp, extra)
    glo, ghi = math.floor(lo / GRID + 1e-9) * GRID, math.ceil(hi / GRID - 1e-9) * GRID
    out = dict(temperature_C=temp, observed_min_V=lo, observed_max_V=hi, range_min_V=glo, range_max_V=ghi, campaign_files=files)
    cs = curves(temp)
    x = cs[0][1]
    keep = (x >= glo - 1e-9) & (x <= ghi + 1e-9)
    if glo < x[0] - 1e-9 or ghi > x[-1] + 1e-9 or keep.sum() < 2:
        return dict(out, status="not_evaluable", reason="the observed range leaves the DC grid or has fewer than two grid points")
    ref = next(c for c in cs if c[0]["divisor"] == 1 and c[0]["vq_V"] == 1.25)
    slope, intercept = np.linalg.lstsq(np.column_stack((x[keep], np.ones(keep.sum()))), ref[2][keep], rcond=None)[0]
    beta = -float(slope)
    secants = np.concatenate([np.diff(y[keep]) / np.diff(xx[keep]) for _, xx, y in cs])
    resid = max(float(np.max(np.abs(y[keep] - (intercept - beta * xx[keep])))) for _, xx, y in cs)
    return dict(out, status="analyzed", grid_points=int(keep.sum()), beta_per_V=beta, inverse_beta_V=1 / beta, intercept=float(intercept),
                epsilon_per_V=float(np.max(np.abs(secants + beta))), secant_min_per_V=float(secants.min()), secant_max_per_V=float(secants.max()),
                all_secants_negative=bool((secants < 0).all()), secants=int(len(secants)),
                local_fit_max_abs_log_error=resid, nominal_dose=beta * (CS / CF) * 0.1)


# ---- traces
def load(name):
    folder = HERE / "runs" / name
    meta = json.loads((folder / "metadata.json").read_text())
    cache = HERE / "tmp" / f"{name}.npy"
    if cache.exists():
        return np.load(cache), meta
    path = folder / "trace.txt.gz"
    if not path.exists():
        return None, meta
    assert hashlib.sha256(path.read_bytes()).hexdigest() == meta["gz_sha256"], "trace differs from its recorded hash"
    with gzip.open(path, "rt") as fh:
        return np.loadtxt(fh), meta


def crossings(d, col, lo, hi):
    """Every 0.9 V crossing of a column in [lo, hi): (time, +1 rising or -1 falling), linearly interpolated."""
    a, b = d[:-1, col], d[1:, col]
    out = []
    for sign, idx in ((1, np.flatnonzero((a < 0.9) & (b >= 0.9))), (-1, np.flatnonzero((a >= 0.9) & (b < 0.9)))):
        for i in idx:
            t = d[i, 0] + (d[i + 1, 0] - d[i, 0]) * (0.9 - a[i]) / (b[i] - a[i])
            if lo <= t < hi:
                out.append((float(t), sign))
    return sorted(out)


def at(d, col, t):
    j = int(np.searchsorted(d[:, 0], t, side="right"))
    a, b = d[j - 1], d[j]
    return float(a[col] + (b[col] - a[col]) * (t - a[0]) / (b[0] - a[0]))


def windows(name, d):
    """One row per period and active port: the ERROR window between the entry and exit latches, and its endpoint voltages."""
    rows = []
    for k in range(1, 22):
        lo, hi, edge = k * PERIOD, (k + 1) * PERIOD, k * PERIOD + OFFSET
        fire = [t for t, s in crossings(d, COL["p"], lo, hi) if s > 0]
        for q in ((1,) if k <= 10 else (2,) if k <= 20 else (1, 2)):
            entry = [t for t, s in crossings(d, COL[f"a{q}"], lo, hi) if s > 0]
            leave = [t for t, s in crossings(d, COL[f"b{q}"], lo, hi) if s > 0]
            steer = crossings(d, COL[f"si{q}"], lo, hi)
            row = dict(run=name, period=k, port=q, joint=k == 21, fired=bool(fire), fire_latency=(fire[0] - edge) / TU if fire else None,
                       protection_rises=len(fire), pre_time=edge - 1e-12, vmem_pre=at(d, COL[f"vmem{q}"], edge - 1e-12),
                       steering_rises=sum(s > 0 for _, s in steer), steering_falls=sum(s < 0 for _, s in steer),
                       entry_latency=None, exit_latency=None)
            if entry and leave and leave[0] > entry[0]:
                te, tx = entry[0], leave[0]
                row.update(entry_latency=(te - edge) / TU, exit_latency=(tx - edge) / TU)
                for label, t in (("entry", te), ("exit", tx)):
                    for sig in ("vs", "vmem", "sum"):
                        row[f"{sig}_{label}"] = at(d, COL[f"{sig}{q}"], t)
                    row[f"p_{label}"] = at(d, COL["p"], t)
            rows.append(row)
    return rows


def events(name, d):
    """Every 0.9 V crossing of the protection latch p and of the raw FIRE comparator, with dwell lengths and context."""
    out = []
    for k in range(0, 22):
        lo, hi, edge = k * PERIOD, (k + 1) * PERIOD, k * PERIOD + OFFSET
        latch = crossings(d, COL["p"], lo, hi)
        first_fire = next((t for t, s in latch if s > 0), None)
        wins = []
        for q in (1, 2):
            e = [t for t, s in crossings(d, COL[f"a{q}"], lo, hi) if s > 0]
            x = [t for t, s in crossings(d, COL[f"b{q}"], lo, hi) if s > 0]
            if e and x and x[0] > e[0]:
                wins.append((q, e[0], x[0]))
        for signal in ("p", "cmpm"):
            cr = crossings(d, COL[signal], lo, hi)
            bounds = [lo] + [t for t, _ in cr] + [hi]
            for i, (t, s) in enumerate(cr):
                near = min(((t - u, "rise" if ls > 0 else "fall") for u, ls in latch), key=lambda z: abs(z[0]), default=(None, None))
                nxt = bounds[i + 2]
                out.append(dict(run=name, period=k, signal="latch" if signal == "p" else "comparator", direction="rise" if s > 0 else "fall",
                                time=t, latency=(t - edge) / TU, dwell_before_s=t - bounds[i], dwell_before_censored=i == 0,
                                dwell_after_s=nxt - t, dwell_after_censored=i == len(cr) - 1,
                                after_first_fire_s=None if first_fire is None else t - first_fire,
                                nearest_latch_transition_s=near[0] if signal == "cmpm" else None,
                                nearest_latch_transition=near[1] if signal == "cmpm" else None,
                                protection_active=at(d, COL["p"], t) >= 0.9 if signal == "cmpm" else s > 0,
                                inside_error_window=any(e <= t <= x for _, e, x in wins),
                                distance_to_error_window_s=min((max(e - t, t - x, 0.0) for _, e, x in wins), default=None)))
    return out


def fmt(x, spec=".4g"):
    return DASH if x is None else format(x, spec)


def main():
    summary = dict(rule="GAIN_PROTOCOL.md and LOCAL_PROTOCOL.md", traces={})
    manifest = json.loads((HERE / "manifest.json").read_text())
    glob_fit = {s["temperature_C"]: s for s in json.loads((HERE / "gain_summary.json").read_text())}
    rows, evs = [], []
    for run in manifest["runs"]:
        d, meta = load(run["name"])
        if d is None:
            summary["traces"][run["name"]] = dict(status="not_evaluable", reason="raw trace not present")
            continue
        summary["traces"][run["name"]] = dict(status="analyzed", points=int(len(d)), raw_sha256=meta["raw_sha256"])
        rows += windows(run["name"], d)
        evs += events(run["name"], d)
    extra = [r[k] for r in rows for k in ("vmem_pre", "vmem_entry", "vmem_exit") if r.get(k) is not None]
    fits = {t: local_fit(t, extra if t == 27 else []) for t in (-40, 27, 125)}
    summary["local_fit"] = list(fits.values())
    summary["global_fit"] = [glob_fit[t] for t in (-40, 27, 125)]

    # proxies per window, with the global and the local slope at 27 C
    g, l = glob_fit[27], fits[27]
    for r in rows:
        if r.get("vs_entry") is None:
            continue
        dvs, dvm = r["vs_entry"] - r["vs_exit"], r["vmem_entry"] - r["vmem_exit"]
        dcap = (r["vmem_entry"] - r["sum_entry"]) - (r["vmem_exit"] - r["sum_exit"])
        r.update(sensor_drop_V=dvs, vmem_drop_V=dvm, capacitor_drop_V=dcap, sum_move_V=r["sum_exit"] - r["sum_entry"],
                 residual_C=CF * dcap - CS * dvs)
        for tag, beta in (("global", g["beta_per_V"]), ("local", l.get("beta_per_V"))):
            if beta is None:
                continue
            r[f"sensor_dose_{tag}"] = beta * (CS / CF) * dvs
            r[f"sensor_tolerance_{tag}"] = abs(beta * (CS / CF) * (dvs - 0.1))
            r[f"residual_log_gain_{tag}"] = beta / CF * abs(r["residual_C"])
            r[f"sum_move_log_gain_{tag}"] = beta * abs(r["sum_move_V"])
            r[f"capacitor_log_gain_{tag}"] = beta * abs(dcap)
            r[f"step_log_gain_{tag}"] = beta * dvm
        r["step_sign_robust_global"] = abs(g["beta_per_V"] * dvm) > 2 * g["all_grid_max_abs_log_error"]
        if l["status"] == "analyzed":
            r["step_error_bound_local"] = l["epsilon_per_V"] * abs(dvm)
    # the increment between two successive reads of the same port, and what the window does not explain of it
    by = {}
    for r in rows:
        by.setdefault((r["run"], r["port"]), []).append(r)
    for seq in by.values():
        seq.sort(key=lambda r: r["period"])
        for now, nxt in zip(seq, seq[1:]):
            now["next_pre_period"] = nxt["period"]
            dv = now["vmem_pre"] - nxt["vmem_pre"]
            now["read_to_read_drop_V"] = dv
            if l["status"] == "analyzed":
                now["increment_local"] = l["beta_per_V"] * dv
                now["increment_error_bound_local"] = l["epsilon_per_V"] * abs(dv)
                if now.get("capacitor_drop_V") is not None:
                    now["handoff_local"] = l["beta_per_V"] * abs(dv - now["capacitor_drop_V"])
                    now["off_window_drift_local"] = l["beta_per_V"] * abs(dv - now["vmem_drop_V"])
    fields = []
    for r in rows:
        fields += [k for k in r if k not in fields]
    with (HERE / "window_samples.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, lineterminator="\n")
        w.writeheader(); w.writerows(rows)
    if evs:
        with (HERE / "latch_events.csv").open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(evs[0]), lineterminator="\n")
            w.writeheader(); w.writerows(evs)

    # ---- summaries
    def stats(sel, key):
        v = [abs(r[key]) for r in sel if r.get(key) is not None]
        return dict(n=len(v), max=max(v) if v else None, min=min(v) if v else None)

    groups = {}
    for name in summary["traces"]:
        mine = [r for r in rows if r["run"] == name]
        silent = [r for r in mine if not r["fired"] and r.get("vs_entry") is not None]
        firing = [r for r in mine if r["fired"] and r.get("vs_entry") is not None]
        groups[name] = dict(
            windows=len(mine), silent_windows=len(silent), firing_windows=len(firing),
            windows_without_entry_or_exit=sum(r.get("vs_entry") is None for r in mine),
            silent_steering=sorted({(r["steering_rises"], r["steering_falls"]) for r in silent}),
            firing_steering=sorted({(r["steering_rises"], r["steering_falls"]) for r in firing}),
            protection_rises_per_period=sorted({r["protection_rises"] for r in mine}),
            silent={k: stats(silent, k) for k in ("sensor_dose_local", "sensor_tolerance_local", "residual_log_gain_local", "sum_move_log_gain_local",
                                                  "step_log_gain_local", "step_error_bound_local", "increment_local", "increment_error_bound_local",
                                                  "handoff_local", "off_window_drift_local", "sensor_tolerance_global", "residual_log_gain_global",
                                                  "step_log_gain_global")},
            firing={k: stats(firing, k) for k in ("capacitor_log_gain_local", "step_log_gain_local", "sum_move_log_gain_local", "increment_local")},
            silent_step_sign_robust_global=sum(bool(r.get("step_sign_robust_global")) for r in silent),
            silent_steps_positive=sum(r["vmem_drop_V"] > 0 for r in silent),
            silent_increments_positive=sum(r.get("read_to_read_drop_V", 0) > 0 for r in silent if r.get("read_to_read_drop_V") is not None))
    summary["windows"] = groups

    ev_sum = {}
    for name in summary["traces"]:
        mine = [e for e in evs if e["run"] == name]
        fire_periods = sorted({e["period"] for e in mine if e["signal"] == "latch" and e["direction"] == "rise"})
        comp = [e for e in mine if e["signal"] == "comparator"]
        latch = [e for e in mine if e["signal"] == "latch"]
        per_period = {}
        for e in comp:
            per_period.setdefault(e["period"], []).append(e)
        short = [e for e in comp if not e["dwell_after_censored"] and e["dwell_after_s"] < 200e-9]
        ev_sum[name] = dict(
            periods_with_fire=len(fire_periods),
            latch_rises_per_period=sorted({sum(1 for e in latch if e["period"] == k and e["direction"] == "rise") for k in range(22)}),
            latch_falls_per_period=sorted({sum(1 for e in latch if e["period"] == k and e["direction"] == "fall") for k in range(22)}),
            comparator_transitions_per_fire_period=sorted({len(per_period.get(k, [])) for k in fire_periods}),
            comparator_transitions_in_silent_periods=sum(len(v) for k, v in per_period.items() if k not in fire_periods),
            comparator_segments_shorter_than_200ns=len(short),
            longest_short_segment_s=max((e["dwell_after_s"] for e in short), default=None),
            comparator_transitions_inside_error_window=sum(e["inside_error_window"] for e in comp),
            latch_transitions_inside_error_window=sum(e["inside_error_window"] for e in latch),
            nearest_comparator_transition_to_error_window_s=min((e["distance_to_error_window_s"] for e in comp if e["distance_to_error_window_s"] is not None), default=None),
            comparator_transitions_without_a_latch_transition_in_the_period=sum(e["nearest_latch_transition_s"] is None for e in comp),
            largest_comparator_distance_to_latch_transition_s=max(
                (abs(e["nearest_latch_transition_s"]) for e in comp if e["nearest_latch_transition_s"] is not None), default=None),
            comparator_offsets_from_latch_rise_s=[f(e["nearest_latch_transition_s"] for e in comp if e["nearest_latch_transition"] == "rise") for f in (min, max)]
            if any(e["nearest_latch_transition"] == "rise" for e in comp) else None,
            comparator_offsets_from_latch_fall_s=[f(e["nearest_latch_transition_s"] for e in comp if e["nearest_latch_transition"] == "fall") for f in (min, max)]
            if any(e["nearest_latch_transition"] == "fall" for e in comp) else None,
            latch_high_dwell_s=[f(e["dwell_after_s"] for e in latch if e["direction"] == "rise" and not e["dwell_after_censored"]) for f in (min, max)]
            if any(e["direction"] == "rise" and not e["dwell_after_censored"] for e in latch) else None,
            first_latch_fire_latencies=[min(e["latency"] for e in latch if e["period"] == k and e["direction"] == "rise") for k in fire_periods])
    summary["events"] = ev_sum
    (HERE / "local_summary.json").write_text(json.dumps(summary, indent=2) + "\n")

    # ---- report
    L = ["# Window endpoints, local increments and latch events", "",
         "Written by `local_analyze.py` under `GAIN_PROTOCOL.md` and `LOCAL_PROTOCOL.md`. No simulation is run here.",
         "These are finite-trace diagnostics of five replays. They are not uniform bounds and not Lean certificates.", "",
         "## Calibration by temperature", "",
         "| Temperature | Global fit over 0.35 to 0.42 V: beta per V | largest error | Observed range (V) | Local beta per V | 1/beta (mV) | epsilon per V | Secants (min, max) per V | All negative | Local fit largest error |",
         "|---|---|---|---|---|---|---|---|---|---|"]
    for t in (-40, 27, 125):
        a, b = glob_fit[t], fits[t]
        if b["status"] != "analyzed":
            L.append(f"| {t} °C | {a['beta_per_V']:.3f} | {a['all_grid_max_abs_log_error']:.4f} | {b['range_min_V']:.4f} to {b['range_max_V']:.4f} | not evaluable: {b['reason']} | | | | | |")
            continue
        L.append(f"| {t} °C | {a['beta_per_V']:.3f} | {a['all_grid_max_abs_log_error']:.4f} | {b['range_min_V']:.4f} to {b['range_max_V']:.4f} ({b['grid_points']} points) | "
                 f"{b['beta_per_V']:.3f} | {1e3 * b['inverse_beta_V']:.2f} | {b['epsilon_per_V']:.3f} | {b['secant_min_per_V']:.3f}, {b['secant_max_per_V']:.3f} | "
                 f"{'yes' if b['all_secants_negative'] else 'NO'} | {b['local_fit_max_abs_log_error']:.5f} |")
    L += ["", "The error of a step of the stored voltage is at most `epsilon * |delta V|` for the piecewise-linear interpolation of each DC curve. "
          "It is not a bound on the transistor between grid points, nor on a pulse, nor on a device with mismatch.", ""]
    if fits[27]["status"] == "analyzed":
        f = fits[27]
        L += [f"At 27 °C the nominal dose is `beta * (Cs/Cf) * 0.1` = {f['nominal_dose']:.5f} with the local slope, {glob_fit[27]['nominal_dose']:.5f} with the global one. "
              f"For a step of one dose, 1.35 mV, the local error bound is {f['epsilon_per_V'] * 1.35e-3:.5f} in log-gain; the endpoint error of the global law is "
              f"{2 * glob_fit[27]['all_grid_max_abs_log_error']:.4f}.", ""]
    L += ["## Write windows", "",
          "A window goes from the entry latch to the exit latch of the pulsed port. Log-gain values use the local slope at 27 °C. "
          "The calibration is that of nominal devices: for the mismatch cell it is a proxy.", "",
          "| Run | Silent windows | Sensor dose | Sensor tolerance (largest) | Residual, in log-gain (largest) | Summing-node move (largest) | Step at the window (range) | Local error bound of a step (largest) | Read-to-read increment (range) | Not explained by the window (largest) | Increments positive |",
          "|---|---|---|---|---|---|---|---|---|---|---|"]
    for name, gsum in groups.items():
        s = gsum["silent"]
        L.append(f"| `{name}` | {gsum['silent_windows']} | {fmt(s['sensor_dose_local']['min'], '.5f')} to {fmt(s['sensor_dose_local']['max'], '.5f')} | "
                 f"{fmt(s['sensor_tolerance_local']['max'], '.2e')} | {fmt(s['residual_log_gain_local']['max'], '.2e')} | {fmt(s['sum_move_log_gain_local']['max'], '.2e')} | "
                 f"{fmt(s['step_log_gain_local']['min'], '.5f')} to {fmt(s['step_log_gain_local']['max'], '.5f')} | {fmt(s['step_error_bound_local']['max'], '.2e')} | "
                 f"{fmt(s['increment_local']['min'], '.5f')} to {fmt(s['increment_local']['max'], '.5f')} | {fmt(s['handoff_local']['max'], '.2e')} | "
                 f"{gsum['silent_increments_positive']} of {s['increment_local']['n']} |")
    L += ["", "On a window with a FIRE the sensor current goes to the dump, so the quantity to bound is the change of the capacitor itself.", "",
          "| Run | Firing windows | Steering switch turned on | Capacitor change, in log-gain (largest) | Step at the window (largest) | Read-to-read increment (largest) |", "|---|---|---|---|---|---|"]
    for name, gsum in groups.items():
        s = gsum["firing"]
        on = sum(1 for r in rows if r["run"] == name and r["fired"] and r["steering_rises"])
        L.append(f"| `{name}` | {gsum['firing_windows']} | {on} | {fmt(s['capacitor_log_gain_local']['max'], '.2e')} | {fmt(s['step_log_gain_local']['max'], '.2e')} | {fmt(s['increment_local']['max'], '.2e')} |")
    L += ["", "With the global affine law, the sign of a silent step is robust to twice its largest error on "
          + ", ".join(f"{g_['silent_step_sign_robust_global']} of {g_['silent_windows']} windows of `{n}`" for n, g_ in groups.items()) + ".", "",
          "## FIRE and comparator events", "",
          "FIRE is the rising crossing of the protection latch at 0.9 V. The raw comparator is a different signal.", "",
          "| Run | Periods with FIRE | Latch rises per period | Latch high for (µs) | Comparator transitions in a period with FIRE | in a silent period | Comparator segments shorter than 200 ns | longest of them (ns) | Comparator transitions around the latch rise (ns from it) | around the latch fall (ns from it) | inside an ERROR window | Nearest to an ERROR window (µs) |",
          "|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for name, e in ev_sum.items():
        ns = lambda v: DASH if v is None else f"{1e9 * v[0]:+.2f} to {1e9 * v[1]:+.2f}"
        L.append(f"| `{name}` | {e['periods_with_fire']} | {e['latch_rises_per_period']} | "
                 + (DASH if e['latch_high_dwell_s'] is None else f"{1e6 * e['latch_high_dwell_s'][0]:.1f} to {1e6 * e['latch_high_dwell_s'][1]:.1f}")
                 + f" | {e['comparator_transitions_per_fire_period']} | {e['comparator_transitions_in_silent_periods']} | "
                 f"{e['comparator_segments_shorter_than_200ns']} | {fmt(None if e['longest_short_segment_s'] is None else 1e9 * e['longest_short_segment_s'], '.2f')} | "
                 f"{ns(e['comparator_offsets_from_latch_rise_s'])} | {ns(e['comparator_offsets_from_latch_fall_s'])} | "
                 f"{e['comparator_transitions_inside_error_window']} | {fmt(None if e['nearest_comparator_transition_to_error_window_s'] is None else 1e6 * e['nearest_comparator_transition_to_error_window_s'], '.2f')} |")
    L += ["", "- The protection latch rises at most once per period in these replays, and falls once after each rise.",
          "- The raw comparator has several transitions in every period with a FIRE. The statement that there is no extra crossing holds for the latch, not for the comparator.",
          "- Every comparator transition of these replays lies within the nanoseconds given above of a latch transition: three around the FIRE and three around the release. "
          "The latch has one rise and one fall in such a period. No comparator transition falls inside an ERROR window, and the nearest is more than 16 µs away from one.",
          "- Every transition, with its date, its dwell lengths and its distance to the latch transitions and to the ERROR windows, is in `latch_events.csv`.",
          "- The delayed enable nodes of the latch are not saved, so the comparison with its 200 ns lockout is descriptive.", ""]
    (HERE / "LOCAL_RESULTS.md").write_text("\n".join(L))
    print("\n".join(L))


if __name__ == "__main__":
    main()
