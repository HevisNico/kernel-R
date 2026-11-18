"""Campaign 6's development batch: the choice of scan set (BATCH_SPEC.md section 5, the owner's rule) and the report
(section 6: k, I and E by the stopping rule, and the design note's five questions). New code; it imports campaign 5's
frozen `plan.py` and `c4.py` (plan.split, plan.machine_expected, c4.limit), and edits neither.

  report6.py choose SMOKE_COSTS.json        B or C from the smokes' wall times (section 5)
  report6.py report BATCH_DIR OUT.json      the batch's report from its collected runs and predictions
  report6.py smoke SMOKE_DIR PRED_DIR OUT   the smoke's B/C choice and the whole chain run once on its nominal instance

The measures of one instance are nine runs of six kinds: cal-on, cal-off, pair (a and b), line (c's line 1 and line 2),
bothfire (c's both lines read once at the preset, v9) and onesided (a and b). E counts each at the batch's mean wall time of its kind (the stopping
rule), and the network at its fixed 718, 132 and 1 400 s.
"""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
C5 = HERE.parent.parent / "learned-dnf-circuit-campaign-5"
sys.path.insert(0, str(C5))
import c4                                               # noqa: E402
import plan                                             # noqa: E402

import batch6                                           # noqa: E402

KINDS = (("cal-on", 1), ("cal-off", 1), ("pair", 2), ("line", 2), ("bothfire", 1), ("onesided", 2))
NET = dict(quiet=F(718), untrained=F(132), noisy=F(1400))
RM_CAL = {"cal-on": sum(map(F, ("725.0", "733.7", "707.1", "722.0", "733.4", "705.0"))) / 6,
          "cal-off": sum(map(F, ("580.9", "597.5", "580.0", "582.7", "603.2", "579.0"))) / 6}
E_MAX, I_MAX = 28800, 40


def _run(i, m, e):
    return dict(id=i, machine=m, expected_s=float(e), timeout_s=c4.limit(F(e)))


def expected_E(I, k, means):
    """E by the stopping rule: I instances in seed order, the first ceil(I/2) on machine a; the measures (KINDS at
    `means`) on all; the network on ceil(k I / 10) instances (the first of each machine, ceil of half on a), one run
    without noise and three noisy runs each, one untrained control run on the first; every stage split as campaign
    5's 10.5 (plan.split, within the kit's bound); E the sum over stages and machines of sum / 4 + 3/4 max."""
    na = math.ceil(I / 2)
    A, B = list(range(na)), list(range(na, I))
    mach = lambda x: "a" if x < na else "b"
    runs = lambda x: [_run(f"{x}-{kind}-{j}", mach(x), means[kind]) for kind, n in KINDS for j in range(n)]
    st = plan.split(runs, A, B)
    m = math.ceil(F(k * I, 10))
    ma = min((m + 1) // 2, len(A))
    net_a, net_b = A[:ma], B[:m - ma]
    first = (net_a + net_b)[0]
    q = lambda x: [_run(f"{x}-q", mach(x), NET["quiet"])] + ([_run(f"{x}-u", mach(x), NET["untrained"])] if x == first else [])
    st += plan.split(q, net_a, net_b)
    for j in (1, 2, 3):
        st += plan.split(lambda x, j=j: [_run(f"{x}-n{j}", mach(x), NET["noisy"])], net_a, net_b)
    return sum(F(plan.machine_expected([r for r in s if r["machine"] == mm])) for s in st for mm in ("a", "b")), len(st)


def decision(k, means):
    """The stopping rule: go only if k >= 2, I = ceil(30 / k) <= 40 and E <= 28 800 s."""
    if k < 2:
        return dict(k=k, I=None, E=None, go=False, why="k < 2")
    I = math.ceil(F(30, k))
    E, stages = expected_E(I, k, means)
    return dict(k=k, I=I, E=E, stages=stages, go=I <= I_MAX and E <= E_MAX)


def least_k(means):
    for k in range(2, 11):
        try:
            if decision(k, means)["go"]:
                return k
        except ValueError:                              # one instance's measures do not fit one kit stage
            return None
    return None


def choose(smoke):
    """The owner's rule (section 5): smoke = {"1/4": {kind: wall_s}, "1/2": {...}} for pair, line, bothfire, onesided.
    Each cost times 1.51; the decks at RM's means; the least k for B (1/4) and C (1/2); B unless C's is strictly lower."""
    out = {}
    for name, step in (("B", "1/4"), ("C", "1/2")):
        means = dict(RM_CAL, **{kind: F(smoke[step][kind]) * batch6.MISMATCH for kind in ("pair", "line", "bothfire", "onesided")})
        out[name] = dict(step=step, means={k: str(v) for k, v in means.items()}, least_k=least_k(means))
    b, c = out["B"]["least_k"], out["C"]["least_k"]
    strictly = c is not None and (b is None or c < b)
    out["choice"] = "C" if strictly else "B"
    out["delta"] = out[out["choice"]]["step"]
    return out


LIMIT_KIND = {"cal-on": "cal", "cal-off": "cal", "pair": "scan", "line": "scan", "bothfire": "onesided", "onesided": "onesided"}


def mean_walls(records):
    """The batch's mean wall time of each kind, exactly: a complete run at its own wall_s (binary value), and a run
    stopped at its limit at that limit (batch6.limit_s of its kind), so that a run cut at its limit does not lower
    the mean. A run that failed otherwise, or never started, has no wall time and is left out (reported)."""
    by = {}
    for r in records:
        if r["status"] == "complete":
            by.setdefault(r["cost_kind"], []).append(F(r["wall_s"]))
        elif r["status"] == "missing (limit)":
            by.setdefault(r["cost_kind"], []).append(F(batch6.limit_s(LIMIT_KIND[r["cost_kind"]])))
    return {k: sum(v) / len(v) for k, v in by.items()}


def report(instances, records):
    """instances: predict6's dicts; records: every run's {id, machine, cost_kind, status, wall_s}."""
    k = sum(1 for x in instances if x.get("eligible") and x.get("gate_K0"))
    means = mean_walls(records)
    d = decision(k, means) if all(kind in means for kind, _ in KINDS) else dict(k=k, go=False, why="a kind has no complete run")
    per_machine = {}
    for r in records:
        per_machine.setdefault(f"{r['cost_kind']}@{r['machine']}", []).append(r["wall_s"])
    q1 = {str(x["seed"]): x.get("question_1") for x in instances}
    left_out = [r["id"] for r in records if r["status"] not in ("complete", "missing (limit)")]
    return dict(k=k, means_rule="complete runs at their wall time, runs at their limit at the limit, the others left out",
                runs_at_their_limit=[r["id"] for r in records if r["status"] == "missing (limit)"], runs_left_out_of_the_means=left_out, eligible=[x["seed"] for x in instances if x.get("eligible") and x.get("gate_K0")], decision={kk: str(v) for kk, v in d.items()},
                means={kk: str(v) for kk, v in means.items()}, question_1=q1,
                question_1_failures=sum(1 for v in q1.values() if v for w in v.values() if not w["agree"]),
                question_2={str(x["seed"]): x.get("question_2") for x in instances},
                question_3={str(x["seed"]): dict(L=x.get("L_rescaled"), theta=x.get("theta"), S=x.get("S")) for x in instances},
                question_5={str(x["seed"]): x.get("question_5") for x in instances},
                question_4={kk: dict(n=len(v), mean=str(sum(map(F, v)) / len(v))) for kk, v in sorted(per_machine.items())},
                not_measured={str(x["seed"]): x["why_not_measured"] for x in instances if not x.get("measured", True)},
                not_eligible={str(x["seed"]): x.get("why_not_eligible") for x in instances if x.get("measured", True) and not x.get("eligible")})


def main(argv=None):
    a = sys.argv[1:] if argv is None else argv
    batch6.require_debug()
    if a[0] == "choose":
        print(json.dumps(choose(json.loads(Path(a[1]).read_text())), indent=1, default=str))
    elif a[0] == "report":
        d = Path(a[1])
        out = report(json.loads((d / "PREDICTIONS.json").read_text())["instances"], json.loads((d / "RUNS.json").read_text()))
        Path(a[2]).write_text(json.dumps(out, indent=1, default=str) + "\n")
        print(json.dumps(dict(k=out["k"], decision=out["decision"])))
    elif a[0] == "smoke":                               # report6.py smoke SMOKE_DIR PRED_DIR OUT.json
        out = smoke_report(Path(a[1]), Path(a[2]))
        Path(a[3]).write_text(json.dumps(out, indent=1, default=str) + "\n")
        print(json.dumps(dict(choice=out["choice"]["choice"], delta=out["choice"]["delta"], chain_k=out["chain"]["k"])))
    else:
        raise SystemExit(__doc__)


def smoke_costs(runs):
    """The smokes' wall times: {"1/4": {pair, line, both, onesided}, "1/2": {...}}, each the mean over the smoke runs of
    that kind and step (at 1/4: pair = a and b, line = line 1 and line 2; onesided = a and b); the one-sided sets and
    the both-lines FIRE check, which have no ascent, count at both steps. Every kind must have completed at both steps."""
    each = {}
    for r in runs:
        if r["status"] == "complete":
            each.setdefault(r["cost_kind"], []).append(F(r["wall_s"]))
    by = {k: sum(v) / len(v) for k, v in each.items()}             # the mean over the smoke runs of each kind
    out = {}
    for step in ("1/4", "1/2"):
        out[step] = dict(pair=by[f"pair@{step}"], line=by[f"line@{step}"], bothfire=by["bothfire"], onesided=by["onesided"])
    return out


def smoke_report(smoke_dir, pred_dir):
    """The declared smoke's two outputs: the owner's B/C rule on its costs, and the whole chain (report) run once on
    its nominal instance, so that every path that computes k has run before the marker. No number of it enters the
    batch's report."""
    runs = json.loads((smoke_dir / "RUNS.json").read_text())
    costs = smoke_costs(runs)
    xs = json.loads((pred_dir / "PREDICTIONS.json").read_text())["instances"]
    recs = [dict(r, machine="a", cost_kind=r["cost_kind"].split("@")[0]) for r in runs if not r["id"].startswith("none-h-")]
    return dict(smoke=True, costs={s: {k: str(v) for k, v in c.items()} for s, c in costs.items()}, choice=choose(costs), chain=report(xs, recs))


if __name__ == "__main__":
    main()
