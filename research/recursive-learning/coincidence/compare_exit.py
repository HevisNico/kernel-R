"""Evaluate the registered lower ERROR exit on the shared sample."""
import argparse
import csv
import hashlib
import itertools
import json
import platform
from pathlib import Path

import numpy as np

import run as r


EXIT = .0025
VARIANTS = (("lower_relative", EXIT), ("lower_absolute", .025))
SETTING = ("R", "lower_exit", 0., 0.)

def training_checks(physical, prepared):
    _, _, _, dose, cap_dose, _, sensor_end = prepared
    low = physical[..., :2, 6]
    earliest_read = 17 + min(r.ARRIVALS) / min(r.SCALES)
    residual = abs(low - r.SENSOR_REST) * np.exp(-.5 * (earliest_read - sensor_end))
    headroom = cap_dose - dose
    last_exit = float(sensor_end.max())
    largest_residual = float(residual.max())
    smallest_headroom = float(headroom.min())
    if not (last_exit < 2 and largest_residual <= .00002 and smallest_headroom > 0):
        raise RuntimeError(
            f"Training checks failed: exit={last_exit}, residual={largest_residual}, "
            f"headroom={smallest_headroom}"
        )
    return dict(last_error_exit=last_exit, max_read_sensor_residual=largest_residual,
                min_log_gain_headroom=smallest_headroom)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--runner-commit", required=True)
    parser.add_argument("--protocol-commit", required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    points = r.sample_points()
    exit_samples = points[..., 6:24:8]
    nodes, weights = np.polynomial.legendre.leggauss(32)
    fields = ["fabrication", "error", "fire", "scale", "setting", "failures",
              "report_guards_passed", "positive_slack_us", "negative_slack_us",
              "reserve_lower_bound", "cap_contacts", "failure_counts", "worst_witnesses",
              "last_error_exit", "max_read_sensor_residual", "min_log_gain_headroom"]
    csv_path = args.output / "lower-exit.csv"
    with csv_path.open("w", newline="") as file:
        writer = csv.DictWriter(file, fieldnames=fields)
        writer.writeheader()
        for fab, error, fire in itertools.product(r.FABRICATION, r.THRESHOLDS, r.THRESHOLDS):
            physical = r.realizations(points, fab, error, fire, 0.)
            for label, error_reference in VARIANTS:
                physical[..., 6] = EXIT + error_reference * error * exit_samples
                prepared = r.prepare(physical, SETTING, nodes, weights)
                checks = training_checks(physical, prepared)
                for scale in r.SCALES:
                    writer.writerow(dict(fabrication=fab, error=error, fire=fire, scale=scale,
                                         setting=label, **checks, **r.evaluate(prepared, scale)))
    np.save(args.output / "points.npy", points, allow_pickle=False)
    manifest = dict(model=r.MODEL, base_protocol=r.PROTOCOL, runner=args.runner_commit,
                    protocol=args.protocol_commit,
                    python=platform.python_version(), numpy=np.__version__,
                    total_points=len(points), seed=r.SEED, quadrature_order=32)
    for name in ("lower-exit.csv", "points.npy"):
        manifest[name] = hashlib.sha256((args.output/name).read_bytes()).hexdigest()
    (args.output/"manifest.json").write_text(json.dumps(manifest, indent=2)+"\n")


if __name__ == "__main__":
    main()
