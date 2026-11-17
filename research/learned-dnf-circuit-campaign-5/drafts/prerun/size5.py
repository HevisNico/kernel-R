"""Campaign 5, pre-run of the sizing (draft PREDICTION.md, sections 10.4 and 10.5), before PREDICTION.md is pushed.

  size5.py OUT.json

Campaign 4's plan.py and c4.py (093995b, copied unchanged into this folder) with three values replaced at run
time, as the draft sets them: the first seed 7601, the time limit of a run 10 x ceil(2 x expected / 10) with no
rehearsal ratio (in place of plan.with_limits), and the kit's estimate the expected cost rounded up to 10 s. The
noise model is the injected one. Prints and writes, for I = 1 to 20, the expected compute and the stage caps, and,
for the I found, every stage's runs, limits, cap and expected compute per machine, with the exact quiet-with-skew
cost and the expected compute in seconds.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c4                                               # noqa: E402
import plan                                             # noqa: E402

c4.FIRST_SEED = 7601


def with_limits(run, cost, model, rehearsal=None):
    e = plan.expected(run, cost, model)
    return dict(run, estimate_s=plan.ceil10(e), timeout_s=plan.ceil10(2.0 * e), expected_s=e)


plan.with_limits = with_limits


def main():
    print(c4.require_pinned())
    cost = plan.costs()
    I, rows = plan.size(cost, "injected", reuse_trip=False, I_max=20)
    st = plan.stages(I, "injected", False, cost)
    detail = []
    for name, runs in st:
        detail.append(dict(stage=name, runs=len(runs), cap_s=plan.stage_cap(runs), limits_s=sorted({r["timeout_s"] for r in runs}),
                           expected_s={m: plan.machine_expected([r for r in runs if r["machine"] == m]) for m in "ab"},
                           seeds={m: sorted({r["seed"] for r in runs if r["machine"] == m}) for m in "ab"}))
    quiet = plan.network_run(7601, "a", (4, 4, 4, 4), "quiet", "injected")
    ends = {f"{s} need {n[0]}": dict(expected_s=plan.expected(plan.network_run(7601, "a", n, s, "injected"), cost, "injected"),
                                    limit_s=with_limits(plan.network_run(7601, "a", n, s, "injected"), cost, "injected")["timeout_s"])
            for n in ((4, 4, 4, 4), (7, 7, 7, 7)) for s in ("quiet", "n1", "untrained")}
    out = dict(I=I, expected_compute_s=plan.expected_compute(st), expected_compute_h=plan.expected_compute(st) / 3600,
               quiet_with_skew_need4_s=plan.expected(quiet, cost, "injected"), runs_at_both_ends=ends, stages=detail, rows=rows)
    Path(sys.argv[1]).write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    print(json.dumps({k: out[k] for k in ("I", "expected_compute_s", "expected_compute_h", "quiet_with_skew_need4_s")}))
    for d in detail:
        print(json.dumps(d, sort_keys=True))
    for k, v in ends.items():
        print(k, v)


if __name__ == "__main__":
    main()
