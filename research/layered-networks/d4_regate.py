"""The D4 regate of one sealed instance (the owner's proportional D4 rule, relayed 2026-11-25). Development only.

Two functions, both without simulation and without Lean. The stage-D gate is fit.cell_fit, a Python mirror with exact
Fractions. The Lean cell in the prediction is data and is not compiled at stage D.

- `audited_lines(D)`: for an instance whose stage D ran its own solo scans (the D4 audit), every cell line's
  |s*_par − s*_solo|. It reads D/record.json with records2.load, the repeat rule the fit uses, and returns
  {cell: {group: value}}. Its per-cell maximum is the D4_stage that fit.cell_fit used (D/fit_d.json, D4_source
  "this run's solo scans").
- `regate(SPEC, INST, allowance)`: the instance's stage-D gate recomputed with calibration.json's d4_stage replaced by
  `allowance`. It runs the same path as the campaign's stage D (stage_d5 → stage_d3 under fit3.rule(rule) →
  stage_d4's masks → stage_d.predict), on a temporary copy of D/record.json and D/overlay_d.json, with the instance's
  inv/inverter_gate.json when it has one.
  - The sealed D/ is never written.
  - The result: per level (K0, K3), whether the gate holds, and the clauses that fail newly against the sealed
    prediction.
  - The same call with the frozen d4_stage (0.005) must reproduce the sealed eligible_K0 and room_K3, and this is
    recorded as `reproduces_sealed`.

  d4_regate.py lines D_DIR                                    the audited lines, as JSON
  d4_regate.py regate SPEC INST_DIR ALLOWANCE [rule=one-port]   the regate, as JSON (ALLOWANCE a decimal or a/b)
"""
import contextlib
import io
import json
from fractions import Fraction as F
from pathlib import Path
import shutil
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fit as fitmod  # noqa: E402
import fit3  # noqa: E402
import records2  # noqa: E402
import stage_d  # noqa: E402
import stage_d3  # noqa: E402,F401
import stage_d4  # noqa: E402,F401  (replaces stage_d.read_masks, as in the campaign)

FROZEN = F(str(fitmod.CAL["d4_stage"]))


def audited_lines(d, load=records2.load):
    rec = load(Path(d))
    sc = rec.get("scans") or {}
    solo_cells = (sc.get("solo") or {}).get("cells") or {}
    out = {}
    for c, res in (sc.get("cells") or {}).items():
        solo = solo_cells.get(c)
        if solo is None:
            continue
        par = {r["group"]: F(r["s_star"]) for r in res or [] if r.get("ok")}
        sol = {r["group"]: F(r["s_star"]) for r in solo if r.get("ok")}
        out[c] = {g: abs(par[g] - sol[g]) for g in sorted(par) if g in sol}
    return out


def _predict(spec, d_dir, allowance, inverters, rule):
    saved = fitmod.CAL.get("d4_stage")
    with tempfile.TemporaryDirectory() as t:
        t = Path(t)
        for n in ("record.json", "overlay_d.json"):
            if (Path(d_dir) / n).exists():
                shutil.copyfile(Path(d_dir) / n, t / n)
        fitmod.CAL["d4_stage"] = str(F(allowance))
        try:
            with fit3.rule(rule), contextlib.redirect_stdout(io.StringIO()):
                stage_d.predict(spec, t, inverters)
        finally:
            fitmod.CAL["d4_stage"] = saved
        pred = json.loads((t / "prediction.json").read_text())
    return pred


def _failing(pred, level):
    """{cell: [clause name]} at a level, the slack dropped (a clause failing with another slack is not new)."""
    return {c["cell"]: [x.split(" (slack")[0] for x in (c.get(level) or {}).get("failing") or []]
            for c in pred.get("cells", [])}


def regate(spec, inst, allowance, rule="one-port"):
    inst = Path(inst)
    d = inst / "D"
    gate = inst / "inv" / "inverter_gate.json"
    inverters = str(gate) if gate.exists() else None
    sealed = json.loads((d / "prediction.json").read_text())
    base = _predict(spec, d, FROZEN, inverters, rule)
    new = _predict(spec, d, F(allowance), inverters, rule)
    reproduces = base["eligible_K0"] == sealed["eligible_K0"] and base["room_K3"] == sealed["room_K3"]
    out = dict(instance=inst.name, allowance=str(F(allowance)), frozen_d4_stage=str(FROZEN), rule=rule,
               inverters=inverters is not None, reproduces_sealed=reproduces,
               sealed=dict(eligible_K0=sealed["eligible_K0"], room_K3=sealed["room_K3"]),
               regated=dict(eligible_K0=new["eligible_K0"], room_K3=new["room_K3"]))
    for level, key in (("K0", "eligible_K0"), ("K3", "room_K3")):
        was, now = _failing(base, level), _failing(new, level)
        out[f"newly_failing_{level}"] = {c: sorted(set(now.get(c, [])) - set(was.get(c, []))) for c in now
                                         if set(now.get(c, [])) - set(was.get(c, []))}
        out[f"gate_holds_{level}"] = bool(new[key])
    return out


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c == "lines":
        print(json.dumps({k: {str(g): str(v) for g, v in x.items()} for k, x in audited_lines(a[0]).items()}, indent=1))
    elif c == "regate":
        kw = dict(x.split("=", 1) for x in a[3:])
        print(json.dumps(regate(a[0], a[1], a[2], kw.get("rule", "one-port")), indent=1, sort_keys=True))
    else:
        sys.exit(__doc__)
