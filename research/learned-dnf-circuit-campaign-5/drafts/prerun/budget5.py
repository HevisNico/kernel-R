"""Campaign 5, the rehearsal stages against the launch kit's own bound (coordinator's review 2, B1), before
PREDICTION.md is pushed.

  budget5.py OUT.json REPO

For each rehearsal stage of the draft (section 11.2), the same runs on machines a and b, with the rehearsal's limit
min(10 x ceil(3 x expected / 10), 3 580 s), the kit's estimate the expected cost rounded up to 10 s (never above the
limit), and the expected costs of campaign 4's plan.py (093995b, unchanged; the need-4 and need-7 calendars). Each
stage's run list is passed to the kit's own check_budget (research/sky130-supervisor-closure/launchkit/launch.py,
unchanged) with 4 jobs and a budget of 14 400 s; its result, or its refusal, is recorded. RQ is given at both ends of
its calendar (every development instance at need 4, and at need 7).
"""
import importlib.util
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c4                                               # noqa: E402
import plan                                             # noqa: E402

CAP = 3580
REPO = Path(sys.argv[2])
spec = importlib.util.spec_from_file_location("launch", REPO / "research/sky130-supervisor-closure/launchkit/launch.py")
launch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(launch)
COST = plan.costs()


def ceil10(x):
    return 10 * math.ceil(x / 10 - 1e-9)


def run(name, kind, needs=(4, 4, 4, 4), scenario=None, limit=None):
    if kind == "cal":
        e = COST["calibration_deck_s"]
    else:
        e = plan.expected(plan.network_run(7691, "a", needs, scenario, "injected"), COST, "injected")
    lim = min(ceil10(3 * e), CAP) if limit is None else limit
    return dict(name=name, expected_s=e, timeout_s=lim, estimate_s=min(ceil10(e), lim))


def stages():
    q4, q7 = ("quiet", (4, 4, 4, 4)), ("quiet", (7, 7, 7, 7))
    return {
        "RC": [run("cal-on", "cal"), run("cal-off", "cal"), run("cal-stopped", "cal", limit=120), run("quiet", "net", *q4[::-1]),
               run("untrained", "net", (4, 4, 4, 4), "untrained"), run("noisy", "net", (4, 4, 4, 4), "n1")],
        "RM": [run(f"{s}-cal-{g}", "cal") for s in (7691, 7692, 7693) for g in ("on", "off")],
        "RQ at need 4": [run(f"{s}-quiet", "net", (4, 4, 4, 4), "quiet") for s in (7691, 7692, 7693)]
                        + [run("7691-quiet-need7", "net", (7, 7, 7, 7), "quiet"), run("untrained", "net", (4, 4, 4, 4), "untrained")],
        "RQ at need 7": [run(f"{s}-quiet", "net", (7, 7, 7, 7), "quiet") for s in (7691, 7692, 7693)]
                        + [run("7691-quiet-need7", "net", (7, 7, 7, 7), "quiet"), run("untrained", "net", (7, 7, 7, 7), "untrained")],
        "RN at need 4": [run(n, "net", (4, 4, 4, 4), "n1") for n in ("7691-n1", "7692-n1", "7693-n1", "7691-n1-repeat")],
        "RN at need 7": [run(n, "net", (7, 7, 7, 7), "n1") for n in ("7691-n1", "7692-n1", "7693-n1", "7691-n1-repeat")],
        "RMEM": [run(n, "net", (7, 7, 7, 7), "n1") for n in ("7691-n1", "7692-n1", "7693-n1", "7691-n2")],
    }


def main():
    print(c4.require_pinned())
    out = {}
    for name, runs in stages().items():
        both = [dict(r, machine=m) for m in ("a", "b") for r in runs]
        try:
            res = dict(accepted=True, **launch.check_budget(both, launch.MAX_BUDGET_S, c4.JOBS))
        except SystemExit as e:
            res = dict(accepted=False, refusal=str(e))
        except Exception as e:  # the kit's require raises its own error type
            res = dict(accepted=False, refusal=f"{type(e).__name__}: {e}")
        out[name] = dict(runs=runs, check_budget=res)
        print(name, json.dumps(dict(limits=[r["timeout_s"] for r in runs], **{k: res[k] for k in ("accepted", "wall_cap_s", "aggregate_cap_s") if k in res},
                                    refusal=res.get("refusal")), default=str))
    Path(sys.argv[1]).write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
