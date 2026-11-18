"""Campaign 6's development batch: the choice of scan set (BATCH_SPEC.md section 5, the owner's rule) and the report
(section 6: k, I and E by the stopping rule, and the design note's five questions). New code; it imports campaign 5's
frozen `plan.py` and `c4.py` (plan.split, plan.machine_expected, c4.limit), and edits neither.

  report6.py choose SMOKE_COSTS.json        B or C from the smokes' wall times (section 5)
  report6.py report BATCH_DIR OUT.json      the batch's report from its collected runs and predictions

The measures of one instance are nine runs of six kinds: cal-on, cal-off, pair (a and b), line (c's line 1 and line 2),
both (c's both lines) and onesided (a and b). E counts each at the batch's mean wall time of its kind (the stopping
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

KINDS = (("cal-on", 1), ("cal-off", 1), ("pair", 2), ("line", 2), ("both", 1), ("onesided", 2))
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
    """The owner's rule (section 5): smoke = {"1/4": {kind: wall_s}, "1/2": {...}} for pair, line, both, onesided.
    Each cost times 1.51; the decks at RM's means; the least k for B (1/4) and C (1/2); B unless C's is strictly lower."""
    out = {}
    for name, step in (("B", "1/4"), ("C", "1/2")):
        means = dict(RM_CAL, **{kind: F(smoke[step][kind]) * batch6.MISMATCH for kind in ("pair", "line", "both", "onesided")})
        out[name] = dict(step=step, means={k: str(v) for k, v in means.items()}, least_k=least_k(means))
    b, c = out["B"]["least_k"], out["C"]["least_k"]
    strictly = c is not None and (b is None or c < b)
    out["choice"] = "C" if strictly else "B"
    out["delta"] = out[out["choice"]]["step"]
    return out


def mean_walls(records):
    """The batch's mean wall time of each kind, exactly (its records' wall_s, binary values)."""
    by = {}
    for r in records:
        by.setdefault(r["cost_kind"], []).append(F(r["wall_s"]))
    return {k: sum(v) / len(v) for k, v in by.items()}


def report(instances, records):
    """instances: predict6's dicts; records: every run's {id, machine, cost_kind, status, wall_s}."""
    k = sum(1 for x in instances if x.get("eligible") and x.get("gate_K0"))
    means = mean_walls([r for r in records if r["status"] == "complete"])
    d = decision(k, means) if all(kind in means for kind, _ in KINDS) else dict(k=k, go=False, why="a kind has no complete run")
    per_machine = {}
    for r in records:
        per_machine.setdefault(f"{r['cost_kind']}@{r['machine']}", []).append(r["wall_s"])
    q1 = {str(x["seed"]): x.get("question_1") for x in instances}
    return dict(k=k, eligible=[x["seed"] for x in instances if x.get("eligible") and x.get("gate_K0")], decision={kk: str(v) for kk, v in d.items()},
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
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
