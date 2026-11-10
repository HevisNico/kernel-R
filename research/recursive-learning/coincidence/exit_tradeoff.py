"""Measure timing scores and plot the registered ERROR exit tradeoff."""
import argparse
import csv
import hashlib
import itertools
import json
import math
import platform
from pathlib import Path

import matplotlib
import numpy as np

from compare_exit import training_checks
import run as r

matplotlib.use("Agg")
from matplotlib import pyplot as plt


EXITS = (.025, .01, .005, .0025)
PREDICTED = (16, 22, 22, 23)
SETTING = ("R", "exit_tradeoff", 0., 0.)


def capacities(exit_level):
    dose = 8 * (.1 - exit_level)
    nominal = math.ceil(math.log(4 / 1.2) / dose)
    guaranteed = math.ceil(math.log(3.6 / 1.2) / (dose + .05))
    return nominal, guaranteed


def plot_scores(path, scores):
    ticks = np.arange(len(EXITS))
    measured = [scores.get((.1, 100, level), 0) for level in EXITS]
    nominal, guaranteed = zip(*(capacities(level) for level in EXITS))
    with plt.rc_context({"svg.fonttype": "none", "svg.hashsalt": "kernel-r-exit-tradeoff"}):
        fig, (score_ax, capacity_ax) = plt.subplots(
            2, 1, figsize=(7.6, 5), sharex=True,
            gridspec_kw={"height_ratios": [2, 1]}, layout="constrained",
        )
        score_ax.set_title("ERROR exit threshold and coincidence score", loc="left", weight="bold")
        score_ax.plot(ticks, measured, "o-", label="Measured", color="#176587")
        score_ax.plot(ticks, PREDICTED, "s--", label="Registered prediction",
                      color="#965015", markerfacecolor="none")
        for x, value in zip(ticks, measured):
            score_ax.annotate(str(value), (x, value), xytext=(0, 10),
                              textcoords="offset points", ha="center")
        score_ax.set_ylabel("Passing boxes / 36")
        score_ax.set_ylim(0, 36)
        score_ax.set_yticks((0, 12, 24, 36))
        score_ax.legend(loc="lower left", frameon=False)
        capacity_ax.plot(ticks, nominal, "o-", label="Nominal", color="#176587")
        capacity_ax.plot(ticks, guaranteed, "s--", label="Wide box minimum",
                         color="#675284", markerfacecolor="none")
        capacity_ax.set_ylabel("Levels below cap")
        capacity_ax.set_ylim(0, 3.65)
        capacity_ax.set_yticks((0, 1, 2, 3))
        capacity_ax.legend(loc="lower left", frameon=False)
        capacity_ax.set_xticks(ticks, [f"{level:g}" for level in EXITS])
        capacity_ax.set_xlabel("Nominal ERROR exit threshold")
        for ax in (score_ax, capacity_ax):
            ax.set_xlim(-.3, len(EXITS) - .7)
            ax.spines[["top", "right"]].set_visible(False)
            ax.grid(axis="y", color="#dddddd")
            ax.set_axisbelow(True)
        fig.suptitle("100 µs per unit · ±10% fabrication · inherited absolute ERROR errors",
                     fontsize=10, color="#444444")
        fig.savefig(path, metadata={"Date": None})
        plt.close(fig)


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
    fields = ["fabrication", "error", "fire", "scale", "exit", "failures",
              "report_guards_passed", "positive_slack_us", "negative_slack_us",
              "reserve_lower_bound", "cap_contacts", "failure_counts", "worst_witnesses",
              "last_error_exit", "max_read_sensor_residual", "min_log_gain_headroom"]
    scores = {}
    with (args.output / "exit-tradeoff.csv").open("w", newline="") as file:
        writer = csv.DictWriter(file, fieldnames=fields)
        writer.writeheader()
        for fab, error, fire in itertools.product(r.FABRICATION, r.THRESHOLDS, r.THRESHOLDS):
            physical = r.realizations(points, fab, error, fire, 0.)
            for level in EXITS:
                physical[..., 6] = level + .025 * error * exit_samples
                prepared = r.prepare(physical, SETTING, nodes, weights)
                checks = training_checks(physical, prepared)
                for scale in r.SCALES:
                    result = r.evaluate(prepared, scale)
                    key = fab, scale, level
                    scores[key] = scores.get(key, 0) + (result["failures"] == 0)
                    writer.writerow(dict(fabrication=fab, error=error, fire=fire,
                                         scale=scale, exit=level, **checks, **result))

    plot_scores(args.output / "exit-tradeoff.svg", scores)
    np.save(args.output / "points.npy", points, allow_pickle=False)
    manifest = dict(model=r.MODEL, base_protocol=r.PROTOCOL, runner=args.runner_commit,
                    protocol=args.protocol_commit, python=platform.python_version(),
                    numpy=np.__version__, matplotlib=matplotlib.__version__,
                    total_points=len(points), seed=r.SEED, quadrature_order=32,
                    scores=[dict(fabrication=fab, scale=scale, exit=level, passes=passes)
                            for (fab, scale, level), passes in sorted(scores.items())])
    for name in ("exit-tradeoff.csv", "exit-tradeoff.svg", "points.npy"):
        manifest[name] = hashlib.sha256((args.output / name).read_bytes()).hexdigest()
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")


if __name__ == "__main__":
    main()
