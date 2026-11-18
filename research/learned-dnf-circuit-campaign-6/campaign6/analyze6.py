"""Campaign 6's one analysis (PREDICTION.md 5, 8 and 9): campaign 5's analyze.py, whose claim functions are used
unchanged, through an adapter that maps exactly four things. New code.

  analyze6.py OUT_DIR PREDICTED.json MEASURES_A MEASURES_B RUNS_A RUNS_B
      MEASURES_*: the collected folders of M1 to M3 of each machine; RUNS_*: those of Q and the N stages

1. The reproduction check. analyze.main recomputes PREDICTED.json with campaign 5's predicted.predictions (the
   nominal-level prediction). Here it is recomputed with predicted6.predictions from the same measures, byte for byte
   (each instance's Lean file and check.sh again included). If it differs, analyze.py makes every claim "not
   established".
2. `eligible`. analyze.py reads an instance's `eligible`; campaign 6's eligibility is measured, eligible and gate_K0
   (PREDICTION.md 3). The record handed to analyze.py carries `eligible` = that, with the original kept as
   `eligible_python`.
3. The run list and the constants come from PREDICTED.json. analyze.py reads campaign 5's BEFORE_M.md only to pass it
   to predicted.predictions, which mapping 1 replaces, so no record before stage M is read (an empty one is given).
4. The minimum of 2 counted eligible instances (PREDICTION.md 5, the owner's decisions of 2026-11-18). analyze.py's
   verdicts, failures and counts are kept unchanged; the number of distinct eligible instances behind each claim's
   counted runs is added; "held" with fewer than 2 becomes "held on one instance, not established" (1) or "not
   established" (0); "refuted" is never changed. For N-own, a port-run counts only if campaign 5's n_own does not
   return None on its word, so the instances behind N-own are found by the same functions analyze.py uses
   (rows_of, reads4.words, n_own), read-only, on the same runs.
The adapter decides no claim of its own.
"""
import copy
import json
from pathlib import Path
import sys
import tempfile
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c6                                               # noqa: E402
import c4                                               # noqa: E402
import predicted6                                       # noqa: E402
import analyze                                          # noqa: E402  (campaign 5, frozen)
import reads4                                           # noqa: E402

HELD_ON_ONE = "held on one instance, not established"


def mapped(p):
    """Mapping 2: eligible = measured, eligible and gate_K0; the original kept beside it."""
    q = copy.deepcopy(p)
    for x in q["instances"]:
        x["eligible_python"] = x.get("eligible")
        x["eligible"] = bool(x.get("measured") and x.get("eligible") and x.get("gate_K0"))
    return q


def minimum(verdict, n):
    """Mapping 4 on one verdict: "held" needs at least 2 distinct eligible instances; "refuted" is never changed."""
    if verdict != "held":
        return verdict
    return "held" if n >= 2 else (HELD_ON_ONE if n == 1 else "not established")


def counted_instances(p, res, recs):
    """The distinct eligible instances behind each claim's counted runs (mapping 4)."""
    inst = {x["seed"]: x for x in p["instances"]}
    missing = set(res.get("missing", []))
    noisy = [r for r in p["network_runs"] if r["noise"] != "none" and r["id"] not in missing and r["id"] in recs]
    out = {"primary": set(res["claims"]["primary"]["instances"]) if isinstance(res["claims"].get("primary"), dict) else set()}
    for c in c4.CELLS:
        out[f"N-out:{c}"] = {r["seed"] for r in noisy if inst[r["seed"]]["counts_N_out"][c]}
    out["N-word"] = {r["seed"] for r in noisy if any(lp["room_up_to"] for lp in inst[r["seed"]]["learning_ports"].values())}
    own = set()
    for r in noisy:
        x = inst[r["seed"]]
        ports = [(port, lp) for port, lp in x["learning_ports"].items() if lp["own_room"]]
        if not ports:
            continue
        rows, _ = analyze.rows_of(recs[r["id"]]["folder"], analyze.plan_needs(r), None)
        w = reads4.words(rows)
        for port, _ in ports:
            need = x["needs"][port[0]] if port[0] != "c" else x["needs"][port]
            if analyze.n_own(w["words"][port], need) is not None:
                own.add(r["seed"])
    out["N-own"] = own
    return {k: sorted(v) for k, v in out.items()}


def apply_minimum(res, counted):
    claims = res["claims"]
    if isinstance(claims.get("primary"), dict):
        claims["primary"]["counted_instances"] = counted["primary"]
        claims["primary"]["verdict"] = minimum(claims["primary"]["verdict"], len(counted["primary"]))
    if isinstance(claims.get("N-out"), dict):
        for c in c4.CELLS:
            v = claims["N-out"][c]
            v["counted_instances"] = counted[f"N-out:{c}"]
            v["verdict"] = minimum(v["verdict"], len(counted[f"N-out:{c}"]))
    for k in ("N-own", "N-word"):
        if isinstance(claims.get(k), dict):
            claims[k]["counted_instances"] = counted[k]
            claims[k]["verdict"] = minimum(claims[k]["verdict"], len(counted[k]))
    res["minimum_of_2"] = "PREDICTION.md 5: held needs counted runs from at least 2 eligible instances (the owner's decisions of 2026-11-18)"
    return res


def run(outdir, predicted_path, measures_a, measures_b, runs_a, runs_b, check=True):
    outdir = Path(outdir)
    pushed = json.loads(Path(predicted_path).read_text())
    work = Path(tempfile.mkdtemp(prefix="c6-analysis-"))
    again = predicted6.predictions([measures_a, measures_b], work / "gate", check)          # mapping 1
    reproduced = predicted6.text(again) == Path(predicted_path).read_text()
    handed = work / "PREDICTED.json"
    handed.write_text(predicted6.text(mapped(pushed)))
    regenerated = mapped(again)
    with mock.patch.object(analyze.P, "predictions", lambda *a, **k: (regenerated, {})), \
            mock.patch.object(analyze.plan, "read_before_m", lambda path: {}):                 # mapping 3
        res = analyze.main([str(outdir), str(measures_a), str(measures_b), str(runs_a), str(runs_b)], here=work, predicted_path=handed)
    res["predicted6_is_reproduced"] = reproduced
    if res.get("predicted_is_reproduced"):
        recs = analyze.state_records(measures_a, measures_b, runs_a, runs_b)
        res = apply_minimum(res, counted_instances(mapped(pushed), res, recs))
    (outdir / "RESULTS.json").write_text(json.dumps(res, indent=1, default=str) + "\n")
    return res


def main(argv=None):
    a = sys.argv[1:] if argv is None else argv
    c6.require_debug()
    res = run(*a[:6])
    print(json.dumps({k: (v.get("verdict") if isinstance(v, dict) and "verdict" in v else v) for k, v in res["claims"].items() if k != "H"}, default=str))


if __name__ == "__main__":
    main()
