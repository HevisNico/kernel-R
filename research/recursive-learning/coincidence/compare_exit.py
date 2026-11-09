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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--runner-commit", required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    points = r.sample_points()
    exit_samples = points[..., 6:24:8]
    nodes, weights = np.polynomial.legendre.leggauss(32)
    fields = ["fabrication", "error", "fire", "scale", "setting", "failures",
              "report_guards_passed", "positive_slack_us", "negative_slack_us",
              "reserve_lower_bound", "cap_contacts", "failure_counts", "worst_witnesses"]
    csv_path = args.output / "lower-exit.csv"
    with csv_path.open("w", newline="") as file:
        writer = csv.DictWriter(file, fieldnames=fields)
        writer.writeheader()
        for fab, error, fire in itertools.product(r.FABRICATION, r.THRESHOLDS, r.THRESHOLDS):
            physical = r.realizations(points, fab, error, fire, 0.)
            for label, error_reference in VARIANTS:
                physical[..., 6] = EXIT + error_reference * error * exit_samples
                prepared = r.prepare(physical, SETTING, nodes, weights)
                for scale in r.SCALES:
                    writer.writerow(dict(fabrication=fab, error=error, fire=fire, scale=scale,
                                         setting=label, **r.evaluate(prepared, scale)))
    np.save(args.output / "points.npy", points, allow_pickle=False)
    manifest = dict(model=r.MODEL, base_protocol=r.PROTOCOL, runner=args.runner_commit,
                    python=platform.python_version(), numpy=np.__version__,
                    total_points=len(points), seed=r.SEED, quadrature_order=32)
    for name in ("lower-exit.csv", "points.npy"):
        manifest[name] = hashlib.sha256((args.output/name).read_bytes()).hexdigest()
    (args.output/"manifest.json").write_text(json.dumps(manifest, indent=2)+"\n")


if __name__ == "__main__":
    main()
