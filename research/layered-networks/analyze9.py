"""analyze8.py with the counts side by side (the owner's request after the audit, relayed 2026-11-26). Development only.
analyze8.py and the earlier analyses are kept as they are.

RESULTS.json gets `counts`: per group and level (K0, K3), every instance of the group in exactly one of these rows,
taken from analyze8's own rows:
- **held**: counted (completed, sealed, compared), every comparison agreeing, and not premise_flagged_D4;
- **refuted**: counted and refuted (a refutation stands, flagged or not);
- **premise_flagged_D4**: not counted at that level because the D4 regate failed there (analyze8's rule);
- **not_sealed**: not counted because its seal or its records' seal log failed (analyze3/analyze6's checks);
- **not_completed**: a step failed, timed out or was interrupted (analyze.py's run_failed at that level, or at stage
  D for both levels), with that step and its status. When no step failed but the level's steps never ran (a partial
  chain), it gives the first step that never ran, with status "not run";
- **no_prediction**: neither eligible (K0) nor with room (K3), so observed only, with no claim.
It also gives `counted` (held + refuted, the instances analyze8 counts) and `instances`. The rows add up to the
group's instances at each level, and this is asserted. Nothing else changes: the rest of RESULTS.json is analyze8's,
byte for byte, apart from the format (layered-campaign-results/9) and analyze9_sha256.

  analyze9.py OUTDIR ROOT [ROOT ...] [times=...] [thresholds=thresholds.json] [controls=DIR]
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import analyze as A  # noqa: E402
import analyze8 as A8  # noqa: E402

FORMAT = "layered-campaign-results/9"
ROWS = ("held", "refuted", "premise_flagged_D4", "not_sealed", "not_completed", "no_prediction")


ORDER = ["deck", "inverters", "D", "seal", "sealpush", "N0", "C0", "N1", "C1", "N2", "C2", "N3", "C3"]


def never_run(r, lv):
    """No step failed: the first step the level needs that never ran (status "not run")."""
    steps = r.get("steps") or {}
    need = [k for k in (ORDER[:7] if lv == "K0" else ORDER) if not (k == "inverters" and r["group"] == "ANDOR3")]
    miss = next((k for k in need if k not in steps), None)                 # ANDOR3 has no inverters step
    return dict(step=miss, status="not run")


def counts(res):
    failed = {}
    for f in res.get("run_failed", []):
        levels = ("K0", "K3") if f["level"] == "stage D" else (f["level"],)
        for lv in levels:
            failed.setdefault((f.get("machine"), f["instance"], lv), f.get("first_failing"))
    out = {}
    for g in sorted(res["groups"]):
        rs = sorted((r for r in res["instances"] if r["group"] == g), key=lambda r: (r["machine"], r["instance"]))
        out[g] = {}
        for lv in ("K0", "K3"):
            row = {k: [] for k in ROWS}
            for r in rs:
                x = r.get(lv) or {}
                name = r["instance"]
                if x.get("counted") and x.get("refuted"):
                    row["refuted"].append(name)
                elif x.get("counted"):
                    row["held"].append(name)
                elif x.get("premise_flagged_D4"):
                    row["premise_flagged_D4"].append(name)
                elif x.get("not_sealed"):
                    row["not_sealed"].append(name)
                elif (r["machine"], name, lv) in failed:
                    ff = failed[(r["machine"], name, lv)] or never_run(r, lv)
                    row["not_completed"].append(dict(instance=name, step=ff.get("step"), status=ff.get("status")))
                else:
                    row["no_prediction"].append(name)
            n = {k: len(v) for k, v in row.items()}
            assert sum(n.values()) == len(rs), (g, lv, n, len(rs))
            out[g][lv] = dict(instances=len(rs), counted=n["held"] + n["refuted"], **{k: dict(n=n[k], list=row[k]) for k in ROWS})
    return out


def main(outdir, *args):
    A8.main(outdir, *args)
    out = Path(outdir)
    res = json.loads((out / "RESULTS.json").read_text())
    res["counts"] = counts(res)
    for g, v in res["counts"].items():
        for lv in ("K0", "K3"):
            assert v[lv]["counted"] == res["groups"][g][lv]["counted"], (g, lv)
    res.update(format=FORMAT, analyze9_sha256=A.sha(__file__))
    (out / "RESULTS.json").write_bytes(A.canon(res))
    (out / "SHA256SUMS").write_text(f"{A.sha(out / 'RESULTS.json')}  RESULTS.json\n")
    print(json.dumps(dict(results_sha256=A.sha(out / "RESULTS.json"),
                          counts={g: {lv: {k: (x[k]["n"] if isinstance(x[k], dict) else x[k]) for k in ("counted",) + ROWS}
                                      for lv, x in v.items()} for g, v in res["counts"].items()}), indent=1))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
