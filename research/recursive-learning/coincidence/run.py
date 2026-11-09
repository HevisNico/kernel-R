"""Evaluate the registered two-pulse coincidence experiment."""
import argparse
import csv
import hashlib
import itertools
import json
import math
import platform
from pathlib import Path

import numpy as np


MODEL = "11f476c3eb299263b980d5b69fb4592e8c0c093b"
PROTOCOL = "1f04221262694383b1505a8d064f62903a85a34a"
SEED = 20261110
A = math.log(4)
REST = 0.1
SENSOR_REST = 0.025
FABRICATION = (0., .003, .1)
THRESHOLDS = (0., .003, .01, .02, .03, .05)
CURRENTS = (0., .003, .01, .03, .05, .1)
SCALES = (50, 100, 200)
ARRIVALS = (-35, -25, -5, 5, 25, 35)
JITTER_PAIRS = list(itertools.product((-5, 5), repeat=2))
DOSE_GRID = tuple(i / 20 for i in range(12, 31))
DECAY_DURATIONS = (.15, .20, .25, .30, .35, .40, .45, .50, .55, .60,
                   .65, .70, .80, 1., 1.5, 2., 4., 8., 12.)
BASE_SETTINGS = (
    ("R", "native", 0., 0.),
    *(("decay", f"decay_{duration:g}", 0., duration)
      for duration in DECAY_DURATIONS),
)
TIMED_SETTINGS = (
    ("timer", "nominal_timer", 4., .15),
    ("timer", "narrow_cap", .12, 12.),
    ("timer", "wide_cap", .125, 12.),
    *(("timer", f"grid_{dose:.2f}", dose / 12, 12.) for dose in DOSE_GRID),
)


def response(t):
    return A / (A - .5) * (np.exp(-.5 * t) - np.exp(-A * t))


NOMINAL = np.array([4., math.log(1.25)/.02, math.log(8)/1.06, A/.15,
                    (1-SENSOR_REST)/response(.02)])


def crossings(fn, threshold, end):
    """Find the first crossing on an increasing branch with fixed brackets."""
    if np.any(fn(0.) >= threshold) or np.any(fn(end) <= threshold):
        raise RuntimeError("First crossing is outside the checked bracket")
    lo = np.zeros_like(threshold)
    hi = np.full_like(threshold, end)
    for _ in range(42):
        mid = (lo + hi) / 2
        below = fn(mid) < threshold
        lo = np.where(below, mid, lo)
        hi = np.where(below, hi, mid)
    return (lo + hi) / 2


def sample_points():
    # Each cell has three port blocks. A port has cap, lm, ls, le, input gain,
    # ERROR entry, ERROR exit and current. FIRE is the last coordinate per cell.
    rng = np.random.Generator(np.random.PCG64(SEED))
    points = [np.zeros((2, 25))]
    for index in range(50):
        for sign in (-1, 1):
            point = np.zeros(50)
            point[index] = sign
            points.append(point.reshape(2, 25))
    for port, orientation, current in itertools.product(range(2), (-1, 1), (-1, 1)):
        point = np.zeros((2, 25))
        point[:, 8 * port] = [orientation, -orientation]
        point[:, 24] = [-orientation, orientation]
        point[:, 8 * port + 7] = current
        points.append(point)
    error_corners = []
    for port, orientation in itertools.product(range(2), (-1, 1)):
        point = np.zeros((2, 25))
        point[:, 8 * port + 5] = [orientation, -orientation]
        point[:, 8 * port + 6] = [-orientation, orientation]
        point[:, 24] = [-orientation, orientation]
        error_corners.append(point)
    return np.concatenate((points, rng.uniform(-1, 1, (512, 2, 25)), error_corners))


def realizations(points, fabrication, error, fire, current):
    ports = points[..., :24].reshape(-1, 2, 3, 8)
    return np.concatenate((
        NOMINAL * (1 + fabrication * ports[..., :5]),
        .1 * (1 + error * ports[..., 5:6]),
        .025 * (1 + error * ports[..., 6:7]),
        1 + current * ports[..., 7:8],
        np.broadcast_to((1 + fire * points[..., 24])[..., None, None],
                        (*ports.shape[:-1], 1)),
    ), axis=-1)


def prepare(physical, setting, nodes, weights):
    """Retain charge from the training pulse and calculate the actual dose."""
    method, _, nominal_current, duration = setting
    cap, lm, ls, le, sensor_gain, high, low, factor, fire = np.moveaxis(physical[..., :2, :], -1, 0)
    mark = crossings(lambda t: SENSOR_REST + sensor_gain * response(t), 1+0*cap, .1)
    onset = mark + math.log(1.25)/lm + np.log(.8/high)/ls
    sensor_end = onset + np.log(high/low)/le
    horizon = sensor_end - onset if method == "R" else np.full_like(onset, duration)
    if np.any(np.maximum(sensor_end, onset+horizon) > 16):
        raise RuntimeError("Training sensor or timer still active at 16")
    current = nominal_current * factor
    cap_dose = np.log(cap/1.2)

    if method == "timer":
        rate_bound = current
        cap_time = cap_dose / current
    else:
        rate_bound = 8*le*high
        fraction = np.minimum(cap_dose/(8*high), np.nextafter(1., 0.))
        cap_time = -np.log1p(-fraction)/le

    def dose(elapsed):
        elapsed = np.minimum(np.maximum(0., elapsed), horizon)
        value = current*elapsed if method == "timer" else -8*high*np.expm1(-le*elapsed)
        return np.minimum(cap_dose, value)

    learned_dose = dose(horizon)
    raw_left = np.maximum(0., 1-onset)
    # Split the training convolution where the gain reaches its cap or stops
    # changing. The second segment then has an exactly constant gain.
    moving = np.minimum(raw_left, np.minimum(cap_time, horizon))
    elapsed = moving[..., None] * ((1+nodes)/2)
    elapsed = np.minimum(np.maximum(0., elapsed), horizon[..., None])
    change = current[..., None]*elapsed if method == "timer" else -8*high[..., None]*np.expm1(-le[..., None]*elapsed)
    increment = 1.2*np.expm1(np.minimum(change, cap_dose[..., None]))
    kernel = A * np.exp(-A*(onset[..., None]+elapsed) - .5*(1-onset[..., None]-elapsed))
    weighted_tail = moving/2 * np.sum(weights*increment*kernel, axis=-1)
    start = np.minimum(1., onset+moving)
    constant_tail = 1.2*np.expm1(dose(moving))*A*np.exp(-.5) * (
        np.exp(-(A-.5)*start)-np.exp(-(A-.5))) / (A-.5)
    residual = 1.2*response(1) + weighted_tail + constant_tail
    # h is increasing through 1. Bound the gain-dependent convolution above
    # by its peak gain increment times the unweighted pulse tail.
    train_max = REST + 1.2*response(1) + A*raw_left*1.2*np.expm1(dose(raw_left))
    if np.any(train_max >= fire):
        raise RuntimeError("Unable to certify silent training for a sampled point")

    # Before ERROR there is no learning on the read port. SILENT alone gives
    # this lower bound on read ERROR latency, even with changed sensor rest.
    earliest_error = np.log(.8/high)/ls
    if np.any(earliest_error <= .9):
        raise RuntimeError("Readout may enter ERROR before the root bracket ends")
    # The quiet read uses the other port's realization. Reverse the port axis
    # to align it with the training choice used for the retained main charge.
    quiet_delay = earliest_error[..., ::-1]
    quiet_rate = rate_bound[..., ::-1]
    quiet_tail = np.maximum(0., 1-quiet_delay)
    quiet_max = REST + residual*np.exp(-.5*15) + 1.2*response(1) + (
        A*quiet_tail*1.2*np.expm1(quiet_rate*quiet_tail))
    if np.any(quiet_max >= fire):
        raise RuntimeError("Unable to certify the untrained read stays silent")

    # Account for the write current in a conservative reserve envelope. Each
    # port's contribution uses the worst possible input or sensor drain.
    all_ports = physical[..., :5]
    sensor_work = np.maximum(A*all_ports[..., 4], np.max(all_ports[..., 1:4], axis=-1)).sum(axis=-1)
    write_work = 3*np.max(rate_bound, axis=-1)
    mark_work = .5*np.sum(all_ports[..., 1], axis=-1)
    main_work = np.maximum(np.maximum(A*np.max(all_ports[..., 0], axis=-1), A*fire[..., 0]), 1.1)
    reserve = 100 - (main_work+sensor_work+write_work+mark_work)/10
    if np.any(reserve <= 0):
        raise RuntimeError("The reserve envelope does not keep the write gate open")

    return residual, 1.2*np.exp(learned_dose), fire, learned_dose, cap_dose, reserve


def evaluate(prepared, scale):
    residual, gain, fire, dose, cap_dose, reserve = prepared
    arrivals = 17 + np.array(ARRIVALS)/scale
    rest = residual[..., None]*np.exp(-.5*(arrivals-1))
    threshold = np.broadcast_to(fire[..., None], rest.shape)
    latency = crossings(lambda t: REST + rest*np.exp(-.5*t) + gain[..., None]*response(t), threshold, .9)
    # The shortest FAST + SLOW path at the recovery cap exceeds pulse support.
    protection = np.log(np.min(fire)/.25)/A + math.log(.25/.1)/1.1
    if protection <= 1 or arrivals[-1]+.9 > 20:
        raise RuntimeError("Cannot exclude an extra or late report")

    margin = {}
    counts = {}
    witnesses = {}
    for offset in (-30, 0, 30):
        observations = []
        for left, right in JITTER_PAIRS:
            left_index = ARRIVALS.index(left)
            right_index = ARRIVALS.index(offset+right)
            skew = abs(offset+right-left + scale*(latency[:, 1, :, right_index]-latency[:, 0, :, left_index]))
            observations.append(15-skew if offset == 0 else skew-15)
        slacks = np.stack(observations, axis=-1)
        point, label, jitter = np.unravel_index(np.argmin(slacks), slacks.shape)
        margin[offset] = float(slacks[point, label, jitter])
        witnesses[offset] = [int(point), int(label), *JITTER_PAIRS[jitter]]
        counts[offset] = int(np.count_nonzero(slacks <= 0 if offset == 0 else slacks < 0))

    # The three other input-port pairs have a silent cell, so only the trained
    # pair can supply a coincidence. A shared wire delay cancels in the skew.
    return dict(failures=sum(counts.values()), report_guards_passed=True,
                positive_slack_us=margin[0],
                negative_slack_us=min(margin[-30], margin[30]),
                reserve_lower_bound=float(reserve.min()),
                cap_contacts=int(np.count_nonzero(dose == cap_dose)),
                failure_counts=json.dumps(counts), worst_witnesses=json.dumps(witnesses))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--runner-commit", required=True)
    parser.add_argument("--quadrature-order", type=int, choices=(16, 32), default=32)
    parser.add_argument("--fabrication", type=float, choices=FABRICATION)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    nodes, weights = np.polynomial.legendre.leggauss(args.quadrature_order)
    points = sample_points()
    # Store exact coordinates and the construction order used for every box.
    np.save(args.output/"points.npy", points, allow_pickle=False)
    fields = ["fabrication", "error", "fire", "current", "scale", "setting",
              "write_current", "duration", "optimized", "failures",
              "report_guards_passed", "positive_slack_us",
              "negative_slack_us", "reserve_lower_bound", "cap_contacts",
              "failure_counts", "worst_witnesses"]
    radii = FABRICATION if args.fabrication is None else (args.fabrication,)
    with (args.output/"sweep.csv").open("w", newline="") as file:
        writer = csv.DictWriter(file, fieldnames=fields)
        writer.writeheader()
        for fabrication, error, fire in itertools.product(radii, THRESHOLDS, THRESHOLDS):
            for current in CURRENTS:
                physical = realizations(points, fabrication, error, fire, current)
                settings = TIMED_SETTINGS + (BASE_SETTINGS if current == 0 else ())
                rows = {scale: [] for scale in SCALES}
                for setting in settings:
                    prepared = prepare(physical, setting, nodes, weights)
                    for scale in SCALES:
                        row = dict(fabrication=fabrication, error=error, fire=fire, current=current,
                                   scale=scale, setting=setting[1], write_current=setting[2],
                                   duration=setting[3], optimized=False, **evaluate(prepared, scale))
                        rows[scale].append(row)
                for candidates in rows.values():
                    timed = [row for row in candidates if row["write_current"] > 0]
                    best = min(timed, key=lambda row: (row["failures"],
                        -min(row["positive_slack_us"], row["negative_slack_us"])))
                    best["optimized"] = True
                    writer.writerows(candidates)
            file.flush()
            print(f"fabrication={fabrication:g} ERROR={error:g} FIRE={fire:g}", flush=True)
    manifest = dict(model=MODEL, protocol=PROTOCOL, runner=args.runner_commit,
                    python=platform.python_version(), numpy=np.__version__,
                    seed=SEED, random_draws=512, total_points=len(points),
                    fabrication_radii=radii, decay_durations=DECAY_DURATIONS,
                    root_bisections=42, quadrature_order=args.quadrature_order)
    for filename in ("points.npy", "sweep.csv"):
        manifest[filename] = hashlib.sha256((args.output/filename).read_bytes()).hexdigest()
    (args.output/"manifest.json").write_text(json.dumps(manifest, indent=2)+"\n")


if __name__ == "__main__":
    main()
