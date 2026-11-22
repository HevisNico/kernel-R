"""The family campaign's fixed tables (PREDICTION.md at 385c33bf): seeds, the draw, the machines, each member's
measure runs, the limits, the network run list and the noise seeds. Standard library only; no simulation.

Every number here is a number of PREDICTION.md; the tests check them against it.
"""
from fractions import Fraction as F
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
CAMPAIGN = HERE.parent                                      # research/function-family-campaign
SEEDS = tuple(range(8501, 8516))
REHEARSAL_SEEDS = (8303, 8306)
MEMBERS = ("X1", "X2", "F4", "F2", "F3")
MACHINES = {"M1": (8501, 8502, 8503), "M2": (8504, 8505, 8506), "M3": (8507, 8508, 8509),
            "M4": (8510, 8511), "M5": (8512, 8513), "M6": (8514, 8515)}          # section 7, seed order 3, 3, 3, 2, 2, 2
DUPLICATE = dict(machine="M5", seed=8501, run="8501-cal-on-unary", dup="DUP/8501-cal-on-unary-dup")   # section 6
# Section 2's measured means at the design point (s): B2's runs and the top-up's runs.
MEANS = {"cal-on": 1662, "cal-off": 1206, "pair": 701, "line": 600, "bothfire": 54, "onesided": 476,
         "cal-on-unary": 2076, "cal-off-unary": 1376, "unary-scan": 634, "preset": 55}
# Kinds of each layer-1 cell per member (FAMILY.json); c has one line for X1, X2 and two for the others.
KINDS = {"X1": dict(a="unary"), "X2": dict(a="pair"), "F4": dict(a="unary", b="unary"),
         "F2": dict(a="pair", b="pair"), "F3": dict(a="unary", b="pair")}
STAGES = ("D", "S", "O")                                    # section 7: decks, scans and checks, one-sided sets


def record_text(res):
    """The serialization of PREDICTED.json, byte for byte (campaign_predict.write and the reproduction check)."""
    return json.dumps(res, indent=1, default=str) + "\n"


def limit_s(kind):
    """10 x ceil(2 x mean / 10) (section 7)."""
    return 10 * math.ceil(F(2 * MEANS[kind], 10))


def draw():
    """seed -> member, from the committed DRAW.json (section 1)."""
    d = json.loads((CAMPAIGN / "DRAW.json").read_text())
    return {int(s): m for s, m in d["draw"].items()}


def machine_of(seed):
    return next(m for m, ss in MACHINES.items() if seed in ss)


def measure_runs(seed, member):
    """The measure runs of one instance (section 2, with O1: both pair scans everywhere), as (run id, kind, stage).
    Run ids are the ones the frozen family_predict.py reads."""
    k = KINDS[member]
    nl = len(k)
    out = [(f"{seed}-cal-on", "cal-on", "D"), (f"{seed}-cal-off", "cal-off", "D")]
    unary = [c for c, v in k.items() if v == "unary"]
    if unary:
        out += [(f"{seed}-cal-on-unary", "cal-on-unary", "D"), (f"{seed}-cal-off-unary", "cal-off-unary", "D")]
    out += [(f"{seed}-scan-{c}-pair", "pair", "S") for c in ("a", "b")]
    out += [(f"{seed}-scan-c-line{p}", "line", "S") for p in range(1, nl + 1)]
    if nl == 2:
        out.append((f"{seed}-bothfire-c", "bothfire", "S"))
    for c in unary:
        out += [(f"{seed}-unary-scan-{c}{p}", "unary-scan", "S") for p in (1, 2)]
        out.append((f"{seed}-preset-{c}", "preset", "S"))
    out += [(f"{seed}-onesided-{c}", "onesided", "O") for c, v in k.items() if v == "pair"]
    return out


def expected_measure_s(member):
    return sum(MEANS[kind] for _, kind, _ in measure_runs(0, member))


def noise_seed(seed, rnd):
    """10 x S + n (section 4)."""
    assert seed in SEEDS and rnd in (1, 2, 3), (seed, rnd)
    return 10 * seed + rnd


REHEARSAL_NOISE = {(8303, "F2", 1): 83031, (8303, "F2", 2): 83032, (8303, "F2", 3): 83033, (8303, "F2", 4): 83034,
                   (8303, "X1", 1): 83035, (8303, "X2", 1): 83036,
                   (8306, "F2", 1): 83061, (8306, "F2", 2): 83062, (8306, "F2", 3): 83063, (8306, "F2", 4): 83064,
                   (8306, "F4", 1): 83065, (8306, "F3", 1): 83066}             # section 7


def network_runs(instances):
    """The campaign's network runs from the prediction record (section 4): for each eligible instance its run without
    noise (with skew); three noisy runs where every cell has room at K = 3; one untrained run per member, on its first
    eligible instance in seed order. instances: [{seed, member, eligible, room_K3}]."""
    runs = []
    for x in sorted(instances, key=lambda x: x["seed"]):
        if not x["eligible"]:
            continue
        s = x["seed"]
        runs.append(dict(id=f"{s}-{x['member']}-quiet", seed=s, member=x["member"], scenario="quiet", control="skew", noise="none", round=0, machine=machine_of(s)))
        if x["room_K3"]:
            for n in (1, 2, 3):
                runs.append(dict(id=f"{s}-{x['member']}-n{n}", seed=s, member=x["member"], scenario=f"n{n}", control=None, noise="injected",
                                 round=n, noise_seed=noise_seed(s, n), machine=machine_of(s)))
    for m in MEMBERS:
        el = sorted(x["seed"] for x in instances if x["member"] == m and x["eligible"])
        if el:
            runs.append(dict(id=f"{el[0]}-{m}-untrained", seed=el[0], member=m, scenario="untrained", control="untrained", noise="none", round=0,
                             machine=machine_of(el[0])))
    return runs
