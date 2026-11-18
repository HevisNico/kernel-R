"""Campaign 5, the learned (A and B) or (C and D) on three circuit cells: the constants that PREDICTION.md fixes, and
the rules that follow from them (instances, machines, run positions, noise seeds, time limits). No simulation is run
here.

Campaign 4's c4.py (093995b), adapted to campaign 5's PREDICTION.md (commit a2d8bad): the folder, the seeds (7601 up;
the development seeds 7691 to 7693), the nominal cell's noise seed (90 961), the time limits (twice the expected cost;
the rehearsal's min(3 x, 3 580 s)) and the one noise model. `test_campaign.py` checks the numbers against the text.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = "research/learned-dnf-circuit-campaign-5"
PHASE0 = HERE.parent / "learned-dnf-circuit"
NET = HERE.parent / "network-circuit"
sys.path.insert(0, str(PHASE0))
sys.path.insert(0, str(NET))
import dnf                                              # noqa: E402  (phase 0: the calendar, merged into main by #172)

CELLS = ("a", "b", "c")
SECTION = "tt_mm"
AMP_AND, AMP_OR = dnf.AMP_AND, dnf.AMP_OR               # 0.49 on layer 1, 1 on the lines
IDIS = 8.2e-9                                           # the dose bias of a port, restored where a port may write
GATE_LEAD = dnf.GATE_LEAD                               # gates set 3 units before a slot
SLOT, WIRE, WINDOW, SNAP = dnf.SLOT, dnf.WIRE, dnf.WINDOW, dnf.SNAP
SKEW_C, DEADLINE_C = 1.1, 2.2                           # the read of c: skew bound and deadline, after its first arrival
STAGES = 8                                              # calibration stages 0 to 7
SKEW_PAIR = 0.3                                         # the second line of c's skewed calibration pair, units late
MOVE_BOUND_MV = 0.01                                    # G, runs without noise: a gated read moves no stored voltage more
WRITE_PRIME_S = 1e-6                                    # write': the write signal above 0.9 V for at least 1 us
R = 3                                                   # noisy runs per measured instance
JOBS = 4
LIMIT_FACTOR = 2                                        # a campaign run's time limit: 10 ceil(2 x expected / 10) (10.4)
REHEARSAL_FACTOR = 3                                    # a rehearsal run's limit: min(10 ceil(3 x expected / 10), 3 580 s) (11.2)
REHEARSAL_CAP_S = 3580
LIMIT_SHARE = 0.75                                      # the 0.75 rule (11.4), judged against the campaign's limit
NOISE_MODELS = ("none", "injected")                     # the one noise model (section 6); any other is refused before any simulation
CLEANUP_S = 10
MAX_BUDGET_S = 14400
BUDGET_H = 8.0
MEASURED_FRACTION = 0.92                                # round(0.92 x I) measured instances (campaign 3: 11 of 12)
FIRST_SEED = 7601
DEV_SEEDS = (7691, 7692, 7693)                         # the development instances, rehearsal only (11.1)
NOMINAL_KEY = 90000                                     # instance_key of the nominal cell (noise criteria, item 1.5)
REHEARSAL_ROUND_BASE = 960                              # the nominal cell's noisy run of the chain test: 90 961 (section 6)
DECISION5 = dict(between_mV=0.111, within_mV=0.094, per_dose_mV=0.009)

# Amendment 3, section 3: the interpreter of every run.
PINNED_VENV = "/home/user/owner-prep/venv312"
PINNED = dict(python_version="3.12.3", numpy_version="2.3.5",
              python_sha256="e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f",
              numpy_record_sha256="064003bdb6f9f7bb06e46e07cc3398cbfdc3c114dfe55b89d239e564917be2fb")


def interpreter():
    """What this process runs on: the Python and numpy versions, the SHA-256 of the interpreter's executable and of
    numpy's RECORD file (read as the launch kit reads it), and the venv."""
    import hashlib
    import importlib.metadata
    import os
    import platform
    import numpy
    exe = os.path.realpath(sys.executable)
    return dict(python_version=platform.python_version(), numpy_version=numpy.__version__,
                python_sha256=hashlib.sha256(Path(exe).read_bytes()).hexdigest(),
                numpy_record_sha256=hashlib.sha256(importlib.metadata.distribution("numpy").read_text("RECORD").encode()).hexdigest(),
                executable=sys.executable, prefix=sys.prefix)


def require_pinned():
    """Refuses any interpreter but the pinned one. In the pinned venv every value must match; elsewhere (the CI runner,
    whose venv path, and so numpy's RECORD, differs) the Python and numpy versions must. Returns what was seen."""
    seen = interpreter()
    keys = PINNED if seen["prefix"] == PINNED_VENV else ("python_version", "numpy_version")
    bad = {k: seen[k] for k in keys if seen[k] != PINNED[k]}
    if bad:
        raise SystemExit(f"refused: not the pinned interpreter (amendment 3, section 3): {bad}")
    return "interpreter: " + json.dumps(dict(seen, checked=sorted(keys)), sort_keys=True)
POSITIONS = dict(cal_on=0, cal_off=1, quiet=2, n1=3, n2=4, n3=5, untrained=6)
EXECUTOR = "a Claude Code cloud session on behalf of the owner, on two cloud containers whose inventories are recorded"


def seeds(I):
    """Seeds 7601 to 7600 + I; the lower half (rounded up) on machine a, the rest on machine b."""
    s = list(range(FIRST_SEED, FIRST_SEED + I))
    k = (I + 1) // 2
    return dict(a=s[:k], b=s[k:])


def machine_of(seed, I):
    return "a" if seed in seeds(I)["a"] else "b"


def noise_seed(seed, n):
    """The noisy run of round n (1, 2, 3) of the instance of seed S: 10 S + n (76 011 up; the development seeds 76 911 to
    76 933). The nominal cell, for the chain test only: round 1, 90 961 (section 6)."""
    assert n in (1, 2, 3)
    if seed is None:
        assert n == 1, "the nominal cell has one noisy run, round 1 of the chain test"
        return NOMINAL_KEY + REHEARSAL_ROUND_BASE + n
    return 10 * seed + n


def limit(expected_s):
    """A campaign run's time limit: twice its expected cost, rounded up to the next 10 s (PREDICTION.md, 10.4)."""
    from fractions import Fraction
    return ceil10(Fraction(expected_s) * LIMIT_FACTOR)


def rehearsal_limit(expected_s):
    """A rehearsal run's limit: min(10 ceil(3 x expected / 10), 3 580 s) (PREDICTION.md, 11.2)."""
    from fractions import Fraction
    return min(ceil10(Fraction(expected_s) * REHEARSAL_FACTOR), REHEARSAL_CAP_S)


def ceil10(x):
    """The least multiple of 10 at or above x (an int, a Fraction, or a float taken at its exact binary value)."""
    from fractions import Fraction
    import math
    return 10 * math.ceil(Fraction(x) / 10)


def instance_key(seed):
    return NOMINAL_KEY if seed is None else seed


