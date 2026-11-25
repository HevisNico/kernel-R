r"""analyze7.py with the proportional D4 rule (the owner's decision, relayed 2026-11-25). Development only.
analyze7.py and the earlier analyses are kept as they are.

THE RULE, in words:
1. **Report.** Every audited cell line is reported against 0.005, the frozen d4_stage of calibration.json. The value is
   |s*_par − s*_solo| per cell and group, from the audited instance's own solo scans (stage D with solo=1, the D4
   audit on every 6th instance of a group).
2. **D4\* per group.** D4\* is the largest audited value of the group. If D4\* ≤ 0.005 (or the group has no audited
   instance), nothing changes.
3. **The regate.** If D4\* > 0.005, every unaudited instance of the group is regated from its sealed D/record.json with
   d4_stage = D4\*, at K0 and at K3 (d4_regate.regate: the campaign's stage-D path, no simulation, no Lean). An
   instance whose gate fails at a level is **premise_flagged_D4** at that level:
   - it is not counted towards established there;
   - it is reported with the clauses that fail newly.
4. **What never changes.** Nothing removes a refutation: an instance refuted at a level stays refuted and counted
   there, flagged or not. The sealed predictions are never modified.
5. **The assumption that remains.** The unaudited instances are taken to be no worse than the worst audited instance of
   their group. This is stated in the results.

The audited instances are those whose D/fit_d.json has D4_source "this run's solo scans". Their own fits already used
their measured values, so they are not regated. The groups' verdicts and the family are then recomputed with
analyze5's wording and thresholds. Everything else in RESULTS.json is analyze7's, unchanged. RESULTS.json gets the
section `d4_audit`, the format layered-campaign-results/8 and analyze8_sha256.

  analyze8.py OUTDIR ROOT [ROOT ...] [times=...] [thresholds=thresholds.json] [controls=DIR]
"""
from fractions import Fraction as F
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import analyze as A  # noqa: E402
import analyze5 as A5  # noqa: E402
import analyze7 as A7  # noqa: E402
import d4_regate as D4  # noqa: E402

FORMAT = "layered-campaign-results/8"
SOLO = "this run's solo scans"
ASSUMPTION = ("the unaudited instances are taken to be no worse than the worst audited instance of their group "
              "(the rule regates them at that group's largest audited value; it does not measure them)")


def is_audited(inst_dir):
    f = Path(inst_dir) / "D" / "fit_d.json"
    if not f.exists():
        return False
    cells = json.loads(f.read_text()).get("cells", [])
    return any(((c.get("budgets") or {}).get("K0") or {}).get("D4_source") == SOLO for c in cells)


def d4_section(rows, inst_dir, spec_of, regate=D4.regate, lines=D4.audited_lines, frozen=D4.FROZEN):
    """The rule on analysis rows ({instance, machine, group, K0, K3}). It returns (section, flags), where flags is
    {(machine, instance): {level: regate result}} for the instances premise_flagged_D4."""
    groups, flags = {}, {}
    for g in sorted({r["group"] for r in rows}):
        rs = sorted((r for r in rows if r["group"] == g), key=lambda r: (r["machine"], r["instance"]))
        aud = [r for r in rs if is_audited(inst_dir(r))]
        ls = []
        for r in aud:
            for c, by_g in sorted(lines(inst_dir(r) / "D").items()):
                for grp, v in sorted(by_g.items()):
                    ls.append(dict(machine=r["machine"], instance=r["instance"], cell=c, group=grp, value=str(v),
                                   value_float=float(v), above_frozen=v > frozen))
        star = max((F(x["value"]) for x in ls), default=None)
        sec = dict(audited=[r["instance"] for r in aud], lines=ls, frozen_d4_stage=str(frozen),
                   D4_star=None if star is None else str(star), D4_star_float=None if star is None else float(star),
                   exceeds=bool(star is not None and star > frozen), regated=[], premise_flagged_D4=dict(K0=[], K3=[]))
        if sec["exceeds"]:
            for r in rs:
                if r in aud or not (inst_dir(r) / "D" / "prediction.json").exists():
                    continue
                res = regate(spec_of(r), inst_dir(r), star)
                sec["regated"].append(dict(machine=r["machine"], instance=r["instance"], **{
                    k: res[k] for k in ("reproduces_sealed", "sealed", "regated", "gate_holds_K0", "gate_holds_K3",
                                        "newly_failing_K0", "newly_failing_K3")}))
                for level in ("K0", "K3"):
                    if (r.get(level) or {}).get("counted") and not res[f"gate_holds_{level}"]:
                        sec["premise_flagged_D4"][level].append(r["instance"])
                        flags.setdefault((r["machine"], r["instance"]), {})[level] = res
        groups[g] = sec
    return dict(rule="proportional D4 (see analyze8.py)", assumption=ASSUMPTION, groups=groups), flags


def apply_flags(res, flags):
    """Mark the flagged levels, then recount the groups and the family with analyze5's wording. A refuted level keeps
    its refutation and its count; it only carries the flag."""
    for r in res["instances"]:
        for level in flags.get((r["machine"], r["instance"]), {}):
            if r[level].get("refuted"):                    # nothing removes a refutation
                r[level] = dict(r[level], premise_flagged_D4=True)
                continue
            r[level] = dict(r[level], counted=False, premise_flagged_D4=True)
    th = res["thresholds"]
    for g, v in res["groups"].items():
        rs = [r for r in res["instances"] if r["group"] == g]
        for level in ("K0", "K3"):
            counted = [r for r in rs if (r.get(level) or {}).get("counted")]
            ref = sorted(r["instance"] for r in counted if r[level].get("refuted"))
            v[level].update(counted=len(counted), refuted_instances=ref, verdict=A5.word(len(counted), bool(ref), th[level][g]),
                            premise_flagged_D4=sorted(r["instance"] for r in rs if (r.get(level) or {}).get("premise_flagged_D4")))
    for level in ("K0", "K3"):
        vs = [res["groups"][g][level]["verdict"] for g in res["groups"]]
        res["family"][level] = "refuted" if "refuted" in vs else "established" if vs and all(x == "established" for x in vs) else "worded per group"
    return res


def main(outdir, *args):
    args = [str(a) for a in args]
    A7.main(outdir, *args)
    out = Path(outdir)
    res = json.loads((out / "RESULTS.json").read_text())
    roots = [Path(a) for a in args if "=" not in a]
    plans = [json.loads((r / "PLAN.json").read_text()) for r in roots]
    inst_dir = lambda r: roots[int(r["machine"].split("_")[1]) - 1] / r["instance"]
    spec_of = lambda r: HERE / plans[int(r["machine"].split("_")[1]) - 1]["groups"][r["group"]]["spec"]
    section, flags = d4_section(res["instances"], inst_dir, spec_of)
    apply_flags(res, flags)
    res["d4_audit"] = section
    res.update(format=FORMAT, analyze8_sha256=A.sha(__file__))
    (out / "RESULTS.json").write_bytes(A.canon(res))
    (out / "SHA256SUMS").write_text(f"{A.sha(out / 'RESULTS.json')}  RESULTS.json\n")
    print(json.dumps(dict(results_sha256=A.sha(out / "RESULTS.json"),
                          d4={g: (s["D4_star"], s["exceeds"], s["premise_flagged_D4"]) for g, s in section["groups"].items()}),
                     indent=1))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
