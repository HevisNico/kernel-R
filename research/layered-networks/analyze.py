"""The one analysis of a campaign OUTROOT (CAMPAIGN_PLAN_DRAFT.md §4, §6; PLAN_NOTES_3.md). Development only.

  analyze.py OUTROOT [OUTDIR]        writes OUTDIR/RESULTS.json and OUTDIR/SHA256SUMS (default OUTROOT/analysis)

Deterministic: it reads only files under OUTROOT, writes canonical JSON (sorted keys, no spaces, ASCII), no date, no
host, no absolute path; two runs on the same OUTROOT give byte-identical output.

**Per instance** (folders with a status.json, written by campaign_run.py / campaign_run2.py):
- the stage-D gates from D/prediction.json: eligible at K0, room at K3, the testError rule, each cell's failing
  clauses, the inverter gate;
- **K0 (no noise)**: the instance is **counted** when it is eligible at K0 and its C0 comparison exists (verdict
  `agrees` or `refuted`);
- **K3 (noisy runs)**: counted when it has room at K3 and all its noisy comparisons C1..C3 exist;
- an eligible instance whose run did not complete (a step failed, timed out or was interrupted) is not counted. It is
  listed under `run_failed` with its first failing step (plan §9);
- every other run is **observed only**, listed with its reason, and counts for no claim and no refutation.

**Per group and level** (plan §4):
- `refuted` when one counted instance has one differing letter or output;
- otherwise, by the number k of counted instances:
  - `established` when k ≥ 30 at K0, or k ≥ 5 at K3;
  - `held on k instances, not established` when 2 ≤ k below that threshold;
  - `held on one instance` when k = 1;
  - `not established` when k = 0.

**Family** (all groups together): per level, `established` only when every group is established; `refuted` when any
group is refuted; otherwise `worded per group`.

**Controls** (plan §6):
- U: from U_*/untrained.json;
- S: the shift slots compared in every counted comparison, and any shift-slot difference;
- the duplicate: from DUP_*/duplicate.json.

**The declared comparison that counts for nothing** (PLAN_NOTES_3.md (a)): eligibility and room recomputed from the
same stage-D records under the superseded max rule (`fit3.rule("max")`, no simulation), with the instances that have
room only under the one-port rule.

Every input file read is listed with its sha256 in RESULTS.json `inputs`.
"""
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

THRESHOLD = dict(K0=30, K3=5)
FORMAT = "layered-campaign-results/1"


def canon(obj):
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


class Reader:
    """Reads JSON files under OUTROOT and remembers each one's sha256 (relative paths)."""

    def __init__(self, root):
        self.root, self.inputs = Path(root), {}

    def json(self, rel):
        p = self.root / rel
        if not p.exists():
            return None
        self.inputs[str(rel)] = sha(p)
        return json.loads(p.read_text())


def word(k, refuted, level):
    if refuted:
        return "refuted"
    if k >= THRESHOLD[level]:
        return "established"
    if k >= 2:
        return f"held on {k} instances, not established"
    return "held on one instance" if k == 1 else "not established"


def first_failing(status):
    order = ["deck", "inverters", "D", "seal", "N0", "C0", "N1", "C1", "N2", "C2", "N3", "C3"]
    for k in order:
        st = status["steps"].get(k)
        if st and st["status"] != "done":
            return dict(step=k, status=st["status"], why=st.get("why"))
    return None


def max_rule(root, name, plan, group, pred_rel):
    """Eligibility and room under the max rule, from the same stage-D record (no simulation)."""
    import fit3
    import spec as specmod
    import stage_d
    import contextlib
    import io
    spec_path = HERE / plan["groups"][group]["spec"]
    s = specmod.load(spec_path)
    src = Path(root) / name
    with tempfile.TemporaryDirectory() as t:
        t = Path(t)
        for f in ("record.json", "overlay_d.json"):
            shutil.copyfile(src / "D" / f, t / f)
        inv = None
        if s["front"]:
            (t / "inv").mkdir()
            shutil.copyfile(src / "inv" / "inverter_gate.json", t / "inv" / "inverter_gate.json")
            inv = str(t / "inv" / "inverter_gate.json")
        with fit3.rule("max"), contextlib.redirect_stdout(io.StringIO()):
            p = stage_d.predict(spec_path, t, inv)
    return dict(eligible_K0=p["eligible_K0"], room_K3=p["room_K3"])


def analyze(root):
    R = Reader(root)
    plan = R.json("PLAN.json")
    rounds = plan.get("rounds", 3)
    insts, observed_only, run_failed = [], [], []
    for st_path in sorted(Path(root).glob("*/status.json")):
        name = st_path.parent.name
        status = R.json(f"{name}/status.json")
        group = status["group"]
        pred = R.json(f"{name}/D/prediction.json")
        comps = {n: R.json(f"{name}/N{n}/comparison.json") for n in range(rounds + 1)}
        row = dict(instance=name, group=group, seed=status["seed"],
                   steps={k: v["status"] for k, v in sorted(status["steps"].items())})
        fail = first_failing(status)
        if pred is None:
            row.update(stage_d=None)
            run_failed.append(dict(instance=name, group=group, level="stage D", first_failing=fail))
            insts.append(row)
            continue
        cells = {c["cell"]: dict(measured=c["measured"], why_not_measured=c["why_not_measured"],
                                 K0_failing=(c.get("K0") or {}).get("failing"), K3_failing=(c.get("K3") or {}).get("failing"))
                 for c in pred["cells"]}
        row["stage_d"] = dict(eligible_K0=pred["eligible_K0"], room_K3=pred["room_K3"],
                              testError_rule=pred.get("testError_rule", "max (stage_d.py)"),
                              inverter_gate=pred["inverter_gate"]["source"] if isinstance(pred["inverter_gate"]["source"], str)
                              else dict(schema=pred["inverter_gate"]["source"].get("schema"),
                                        kit_commit=pred["inverter_gate"]["source"].get("kit_commit")),
                              inverter_K0=pred["inverter_gate"]["K0"], inverter_K3=pred["inverter_gate"]["K3"],
                              cells=cells)
        row["comparisons"] = {f"C{n}": None if c is None else dict(
            run_kind=c["run_kind"], verdict=c["verdict"], compared=c.get("compared"),
            differences=c.get("differences"), why=c.get("why")) for n, c in comps.items()}
        # K0
        if pred["eligible_K0"]:
            c0 = comps[0]
            if c0 is not None and c0["verdict"] in ("agrees", "refuted"):
                row["K0"] = dict(counted=True, refuted=c0["verdict"] == "refuted")
            else:
                row["K0"] = dict(counted=False)
                run_failed.append(dict(instance=name, group=group, level="K0", first_failing=fail))
        else:
            row["K0"] = dict(counted=False)
            why = [f"{c}: not measured ({'; '.join(v['why_not_measured'])})" if not v["measured"]
                   else f"{c}: K0 {v['K0_failing']}" for c, v in cells.items() if not v["measured"] or v["K0_failing"]]
            if not pred["inverter_gate"]["K0"]:
                why.append(f"inverter gate: {pred['inverter_gate'].get('why')}")
            observed_only.append(dict(instance=name, group=group, level="K0 and K3", why=why,
                                      runs=sorted(f"C{n}" for n, c in comps.items() if c is not None)))
        # K3
        noisy = [comps[n] for n in range(1, rounds + 1)]
        if pred["room_K3"]:
            if all(c is not None and c["verdict"] in ("agrees", "refuted") for c in noisy):
                row["K3"] = dict(counted=True, refuted=any(c["verdict"] == "refuted" for c in noisy))
            else:
                row["K3"] = dict(counted=False)
                run_failed.append(dict(instance=name, group=group, level="K3", first_failing=fail))
        else:
            row["K3"] = dict(counted=False)
            if pred["eligible_K0"]:
                why = [f"{c}: K3 {v['K3_failing']}" for c, v in cells.items() if v["K3_failing"]]
                if not pred["inverter_gate"]["K3"]:
                    why.append(f"inverter gate K3: {pred['inverter_gate'].get('why')}")
                observed_only.append(dict(instance=name, group=group, level="K3", why=why,
                                          runs=sorted(f"C{n}" for n, c in comps.items() if c is not None and n > 0)))
        # the declared comparison (counts for nothing)
        row["max_rule_comparison"] = max_rule(root, name, plan, group, f"{name}/D/prediction.json")
        # cost
        row["cost"] = {k: dict(cpu_s=v.get("cpu_s"), wall_s=v.get("wall_s")) for k, v in sorted(status["steps"].items())}
        row["cost_total"] = dict(cpu_s=round(sum(v.get("cpu_s") or 0 for v in status["steps"].values()), 1))
        insts.append(row)
    groups = {}
    for g in plan["groups"]:
        rows = [r for r in insts if r["group"] == g]
        out = dict(planned=len(plan["groups"][g]["seeds"]), instances=len(rows))
        for level in ("K0", "K3"):
            counted = [r for r in rows if (r.get(level) or {}).get("counted")]
            ref = [r["instance"] for r in counted if r[level]["refuted"]]
            out[level] = dict(counted=len(counted), refuted_instances=ref, threshold=THRESHOLD[level],
                              verdict=word(len(counted), bool(ref), level), counted_instances=[r["instance"] for r in counted])
        out["eligible_K0"] = sum(1 for r in rows if (r.get("stage_d") or {}).get("eligible_K0"))
        out["room_K3"] = sum(1 for r in rows if (r.get("stage_d") or {}).get("room_K3"))
        mr = [r for r in rows if r.get("max_rule_comparison")]
        out["max_rule_comparison_counts_for_nothing"] = dict(
            eligible_K0=sum(1 for r in mr if r["max_rule_comparison"]["eligible_K0"]),
            room_K3=sum(1 for r in mr if r["max_rule_comparison"]["room_K3"]),
            room_only_under_one_port=[r["instance"] for r in mr
                                      if r["stage_d"]["room_K3"] and not r["max_rule_comparison"]["room_K3"]])
        groups[g] = out
    family = {}
    for level in ("K0", "K3"):
        vs = [groups[g][level]["verdict"] for g in groups]
        family[level] = ("refuted" if "refuted" in vs else "established" if all(v == "established" for v in vs)
                         else "worded per group")
    controls = dict(U=[], duplicate=[], S=[])
    for p in sorted(Path(root).glob("U_*/untrained.json")):
        u = R.json(str(p.relative_to(root)))
        controls["U"].append(dict(instance=u["instance"], holds=u.get("ok"), r_cell_fires=u.get("r_cell_fires"),
                                  inverter_fires_reported=len(u.get("inverter_fires_reported") or [])))
    for p in sorted(Path(root).glob("DUP_*/duplicate.json")):
        x = R.json(str(p.relative_to(root)))
        controls["duplicate"].append(dict(instance=x["instance"], identical=x.get("ok"), checker=x.get("checker"),
                                          check_exit=x.get("check_duplicate_exit")))
    for r in insts:
        for k, c in sorted((r.get("comparisons") or {}).items()):
            if c and c.get("compared"):
                controls["S"].append(dict(instance=r["instance"], comparison=k, skew_slots=c["compared"]["skew_slots"],
                                          skew_differences=[d for d in c.get("differences") or [] if d["what"] == "skew"]))
    return dict(format=FORMAT, analyze_sha256=sha(__file__), thresholds=THRESHOLD, groups=groups, family=family,
                observed_only=observed_only, run_failed=run_failed, controls=controls, instances=insts,
                counting_rule="counted = a prediction (eligible K0 / room K3) and its comparisons complete; "
                              "one differing letter or output on a counted instance refutes",
                inputs=dict(sorted(R.inputs.items())))


def main(root, outdir=None):
    root = Path(root)
    outdir = Path(outdir) if outdir else root / "analysis"
    res = analyze(root)
    outdir.mkdir(parents=True, exist_ok=True)
    (outdir / "RESULTS.json").write_bytes(canon(res))
    (outdir / "SHA256SUMS").write_text(f"{sha(outdir / 'RESULTS.json')}  RESULTS.json\n")
    print(json.dumps(dict(groups={g: {k: v[k]["verdict"] if k in ("K0", "K3") else v[k] for k in ("K0", "K3", "eligible_K0", "room_K3")}
                                  for g, v in res["groups"].items()}, family=res["family"],
                          observed_only=len(res["observed_only"]), run_failed=len(res["run_failed"])), indent=1, sort_keys=True))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
