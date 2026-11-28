# The D4 audit, as the code does it (read-only answer for PREDICTION.md, 2026-11-25)

No code was changed. Quotes are from research/layered-stage-d 577d71b9.

## Which instances
- **plan_split.py lines 11–12**: "every 6th instance of each group in draw order (positions 6, 12, 18, …) runs its
  stage D with its own solo scans (`groups[g]["d4_audit"]`)".
- **plan_split.py line 47**: `audited = pos % 6 == 0`.
- **campaign_run4.py line 50**:
  `solo = ["solo=1"] if seed in plan["groups"][self.group].get("d4_audit", []) else []`, passed to stage D.

## What runs
- **instrument.py lines 501–518**: after the parallel scans, each cell is scanned again alone, from where the parallel
  scan left it (`if solo:  # D4: each cell again, alone, from where the parallel scan left it`).
- The record holds both, as scans.cells and scans.solo.

## How it enters the fit (fit.py lines 253–268)
```
solo = (scans.get("solo") or {}).get("cells", {}).get(c)
if solo is not None:
    par = {r["group"]: F(r["s_star"]) for r in scans["cells"][c] if r.get("ok")}
    sol = {r["group"]: F(r["s_star"]) for r in solo if r.get("ok")}
    if set(par) != set(sol):
        out["measured"] = False
        out["why_not_measured"].append("D4: a solo scan failed")
        return out
    d4_stage, d4_source = max(abs(par[g] - sol[g]) for g in par), "this run's solo scans"
elif CAL.get("d4_stage") is not None:
    d4_stage, d4_source = F(str(CAL["d4_stage"])), "calibration.json d4_stage"
else:
    out["measured"] = False
    out["why_not_measured"].append("D4: no solo scan and no d4_stage bound")
    return out
H_D4 = math.ceil((2 if gate == "both" else 1) * an["d"] * d4_stage)
```
- calibration.json line 22: `"d4_stage": 0.005`.
- H_D4 enters trainError and testError (fit.py line 287).

## The pass criterion: there is none
- **On an audited instance**, the measured value replaces the constant 0.005 in that instance's own H_D4. The measured
  value is the largest |s*_par − s*_solo| over the cell's groups.
- **A larger measured value** only enlarges that instance's own budgets, so it can lose K0 or K3 eligibility through its
  own fit. It never fails as an audit.
- **The measured value is never compared with 0.005.** The five unaudited instances in between keep 0.005, whatever
  the audit finds.

## A failed solo scan
- That cell is not measured ("D4: a solo scan failed"), so the instance is not eligible and has no prediction.
- Under the plan's failure rule, it is counted and reported under that clause, and never dropped or re-run.

## Where it is recorded
- **Per cell, in D/fit_d.json**: budgets.K<n>.D4_stage, D4_source ("this run's solo scans" or "calibration.json
  d4_stage") and H_D4.
- **The solo scans themselves**: in D/record.json, scans.solo.
- **No analysis reads them**: analyze*.py has no D4 field.
- **CAMPAIGN_PLAN_DRAFT.md line 195** calls D4 "d4_stage 0.005, audited". As the code stands, "audited" means "measured
  on every 6th instance and used there", not "checked against 0.005". A criterion would be a decision of the owner. For
  example: a measured value above 0.005 voids the constant's use on the unaudited instances, and an analysis line
  reports it.
