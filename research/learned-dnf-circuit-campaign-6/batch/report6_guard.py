"""Campaign 6's development batch: report6.report with ONE change (the owner's ruling, after report6.py raised on the
batch: question 4 averaged every run's wall_s, and the runs that failed or never started have none). Its per-machine
loop takes only the runs whose status is "complete", those mean_walls counts at their own wall time. Everything else
is report6's: the function below is copied verbatim but for that one line, and every helper is imported from
report6.py, which is unchanged, as is every other file.

  report6_guard.py report BATCH_DIR OUT.json      report6.py report, with this report()
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import report6                                          # noqa: E402
from report6 import F, KINDS, batch6, decision, mean_walls      # noqa: E402,F401


def report(instances, records):
    """instances: predict6's dicts; records: every run's {id, machine, cost_kind, status, wall_s}."""
    k = sum(1 for x in instances if x.get("eligible") and x.get("gate_K0"))
    means = mean_walls(records)
    d = decision(k, means) if all(kind in means for kind, _ in KINDS) else dict(k=k, go=False, why="a kind has no complete run")
    per_machine = {}
    for r in (r for r in records if r["status"] == "complete"):
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
    if len(a) == 3 and a[0] == "report":
        d = Path(a[1])
        out = report(json.loads((d / "PREDICTIONS.json").read_text())["instances"], json.loads((d / "RUNS.json").read_text()))
        Path(a[2]).write_text(json.dumps(out, indent=1, default=str) + "\n")
        print(json.dumps(dict(k=out["k"], decision=out["decision"])))
    else:
        raise SystemExit("report6_guard.py report BATCH_DIR OUT.json")


if __name__ == "__main__":
    main()
