"""Campaign 4, the learned (A and B) or (C and D) on three circuit cells: the constants that PREDICTION.md fixes, and
the rules that follow from them (instances, machines, run positions, noise seeds). No simulation is run here.

Every number below is a number of PREDICTION.md (commit 1596b36); `test_campaign.py` checks them against its text.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = "research/learned-dnf-circuit-campaign-4"
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
MARGIN = 1.3                                            # time limits: 1.3 times the measured time
CLEANUP_S = 10
MAX_BUDGET_S = 14400
BUDGET_H = 8.0
MEASURED_FRACTION = 0.92                                # round(0.92 x I) measured instances (campaign 3: 11 of 12)
FIRST_SEED = 7501
NOMINAL_KEY = 90000                                     # instance_key of the nominal cell (noise criteria, item 1.5)
REHEARSAL_ROUND_BASE = 950                              # the rehearsal's nominal rounds: 951, 952, ... (no criterion uses them)
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
    """Seeds 7501 to 7500 + I; the lower half (rounded up) on machine a, the rest on machine b."""
    s = list(range(FIRST_SEED, FIRST_SEED + I))
    k = (I + 1) // 2
    return dict(a=s[:k], b=s[k:])


def machine_of(seed, I):
    return "a" if seed in seeds(I)["a"] else "b"


def noise_seed(seed, n):
    """The noisy run of round n (1, 2, 3) of the instance of seed S: 10 S + n. The nominal cell, for the rehearsal
    only: 90000 + 950 + n."""
    assert n in (1, 2, 3)
    return NOMINAL_KEY + REHEARSAL_ROUND_BASE + n if seed is None else 10 * seed + n


def instance_key(seed):
    return NOMINAL_KEY if seed is None else seed


