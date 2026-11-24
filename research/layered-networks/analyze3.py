"""The campaign analysis over every machine's OUTROOT, with seal regeneration and the seal-log check (PREDICTION
draft, 2026-11-24). Development only. analyze.py and analyze2.py are pushed and kept; their per-OUTROOT analysis
is reused.

  analyze3.py OUTDIR ROOT [ROOT ...] [times=github|bare]     OUTDIR/RESULTS.json, OUTDIR/SHA256SUMS

Per OUTROOT (one machine): analyze2.env_section (ENV.json; mixed environments refused), then analyze.analyze.

Per instance, two checks decide whether its prediction may be counted; an instance that fails either has **no counted
prediction**. Its runs are reported as observed, and the failure is listed under `seal_defects`.
1. **Regeneration.** The prediction is computed again from the stage-D record alone: a copy of D/record.json and
   D/overlay_d.json (and, with a front end, inv/inverter_gate.json) in a scratch folder. It runs through the same
   stage-D script, with the same rule and the instance's LAYERED_ENV_SHA256. The bytes must equal the sealed file
   seal/<TAG>_<seed>.json exactly. The script is the one whose sha256 the prediction records; a changed script changes
   those bytes, and so it is caught.
2. **The seal log.** On the machine's log branch (PLAN `seal_push`), SEALS.txt must have the instance's line with the
   sha256 of seal/SHA256SUMS. The time the remote received the push that added it must be **earlier than the instance's
   stage-N start** (status.json N0 `started`, the machine's UTC clock).
   - Push times: `times=github` uses GitHub's repository activity API (the push's `timestamp`, GitHub's record, not the
     commit date). `times=bare` uses a local bare repository's post-receive log (tests, dry runs). See sealpush.py.
   - A plan with `"dry": true` never pushed: its instances are not sealed.
   - Clock caveat: the comparison mixes GitHub's clock with the machine's. The margin is reported per instance.

Then per group and level, the family, the observed-only list and run_failed, as analyze.py, over all machines and
counting only sealed instances; the controls from every machine. The cross-machine duplicates (DUPX_*) are compared
with the original instance's N0 on its machine: noisy_record.json and trace.digest.json equal without their cost and
time fields, and input.spice byte-identical.
Deterministic: canonical JSON, no date, no absolute path.
"""
import datetime
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import analyze as A  # noqa: E402
import analyze2 as A2  # noqa: E402
import campaign_run as CR  # noqa: E402
import sealpush as SP  # noqa: E402

FORMAT = "layered-campaign-results/3"
SCRIPTS = ("stage_d5.py", "stage_d4.py", "stage_d3.py")


def parse_utc(t):
    t = t.rstrip("Z")
    for fmt in ("%Y-%m-%dT%H:%M:%S.%f", "%Y-%m-%dT%H:%M:%S"):
        try:
            return datetime.datetime.strptime(t[:26], fmt).replace(tzinfo=datetime.timezone.utc)
        except ValueError:
            pass
    raise ValueError(t)


def regenerate(root, name, plan, status):
    """True when the prediction recomputed from the stage-D record equals the sealed bytes; else the reason."""
    d = Path(root) / name
    seal_file = next((p for p in (d / "seal").glob("*.json") if p.name != "MANIFEST.json"), None)
    if seal_file is None or not (d / "D" / "record.json").exists():
        return False, "no seal or no stage-D record"
    sealed = seal_file.read_bytes()
    pred = json.loads(sealed)
    script = next((s for s in SCRIPTS if s in pred.get("code", {})), None)
    if script is None:
        return False, "the sealed prediction names no stage-D script"
    group = status["group"]
    spec = HERE / plan["groups"][group]["spec"]
    with tempfile.TemporaryDirectory() as t:
        t = Path(t)
        for f in ("record.json", "overlay_d.json"):
            shutil.copyfile(d / "D" / f, t / f)
        args = [CR.PY, "-B", str(HERE / script), "predict", str(spec), str(t), f"rule={pred.get('testError_rule', 'one-port')}"]
        if (d / "inv" / "inverter_gate.json").exists():
            (t / "inv").mkdir()
            shutil.copyfile(d / "inv" / "inverter_gate.json", t / "inv" / "inverter_gate.json")
            args.append(f"inverters={t / 'inv' / 'inverter_gate.json'}")
        env = dict(os.environ)
        if status.get("env_sha256"):
            env["LAYERED_ENV_SHA256"] = status["env_sha256"]
        else:
            env.pop("LAYERED_ENV_SHA256", None)
        r = subprocess.run(args, cwd=HERE, capture_output=True, text=True, env=env)
        if r.returncode or not (t / "prediction.json").exists():
            return False, "regeneration failed: " + r.stderr.strip().replace(str(t), "<scratch>")[-300:]
        again = (t / "prediction.json").read_bytes()
    if again != sealed:
        a, b = json.loads(again), pred
        keys = sorted(k for k in set(a) | set(b) if a.get(k) != b.get(k))
        return False, f"regenerated prediction differs from the seal in {keys}"
    return True, None


def seal_log(root, name, plan, status, logs, times_src):
    """(ok, detail) for the instance's line in its machine's seal log."""
    sp_ = plan.get("seal_push")
    if not sp_:
        return False, dict(why="the plan has no seal_push")
    if sp_.get("dry"):
        return False, dict(why="dry seal push (nothing was pushed)")
    key = (str(sp_["remote"]), sp_["branch"])
    if key not in logs:
        with tempfile.TemporaryDirectory() as w:
            try:
                lines = SP.log_lines(sp_["remote"], sp_["branch"], w)
                tm = SP.times(sp_["remote"], sp_["branch"], times_src)
                logs[key] = (lines, tm, None)
            except Exception as e:
                logs[key] = ([], {}, repr(e))
    lines, tm, err = logs[key]
    if err:
        return False, dict(why=f"the seal log cannot be read: {err}")
    want = CR.sha(Path(root) / name / "seal" / "SHA256SUMS")
    mine = [x for x in lines if x["instance"] == name]
    if not mine:
        return False, dict(why="no line for this instance in the seal log")
    hit = [x for x in mine if x["seal_sha256"] == want]
    if not hit:
        return False, dict(why="the logged seal sha256 is not this seal's", logged=[x["seal_sha256"] for x in mine])
    x = hit[0]
    pushed = tm.get(x["commit"])
    if pushed is None:
        return False, dict(why="no recorded push time for the commit that logged the seal", commit=x["commit"])
    n0 = status["steps"].get("N0", {}).get("started")
    if n0 is None:
        return True, dict(pushed_utc=pushed, stage_n_start=None, note="no stage N started")
    margin = (parse_utc(n0) - parse_utc(pushed)).total_seconds()
    detail = dict(pushed_utc=pushed, stage_n_start=n0, margin_s=round(margin, 3), commit=x["commit"])
    if margin <= 0:
        return False, dict(detail, why="the seal was pushed after stage N started")
    return True, detail


def same_n0(a, b):
    out = {}
    for f in ("noisy_record.json", "trace.digest.json"):
        if (a / f).exists() and (b / f).exists():
            out[f] = CR.strip(json.loads((a / f).read_text())) == CR.strip(json.loads((b / f).read_text()))
        else:
            out[f] = None
    if (a / "input.spice").exists() and (b / "input.spice").exists():
        out["input.spice"] = (a / "input.spice").read_bytes() == (b / "input.spice").read_bytes()
    return out


def main(outdir, *args):
    args = [str(a) for a in args]
    roots = [Path(a) for a in args if "=" not in a]
    kw = dict(a.split("=", 1) for a in args if "=" in a)
    times_src = kw.get("times", "github")
    rows, observed, failed, controls, envs, defects = [], [], [], dict(U=[], duplicate=[], S=[], cross_machine_duplicates=[]), {}, []
    logs, by_inst = {}, {}
    plans = {}
    for k, root in enumerate(roots):
        machine = f"machine_{k + 1}"
        envs[machine] = A2.env_section(root)
        res = A.analyze(root)
        plan = json.loads((root / "PLAN.json").read_text())
        plans[machine] = plan
        for r in res["instances"]:
            r["machine"] = machine
            status = json.loads((root / r["instance"] / "status.json").read_text())
            if r.get("stage_d") is not None:
                ok1, why1 = regenerate(root, r["instance"], plan, status)
                ok2, det2 = seal_log(root, r["instance"], plan, status, logs, times_src)
                r["seal"] = dict(regenerated_identical=ok1, regeneration_why=why1, log_ok=ok2, log=det2)
                if not (ok1 and ok2):
                    defects.append(dict(machine=machine, instance=r["instance"], regenerated=why1 or "identical",
                                        log=det2.get("why") or "ok"))
                    for level in ("K0", "K3"):
                        if (r.get(level) or {}).get("counted"):
                            r[level] = dict(counted=False, not_sealed=True)
            rows.append(r)
            by_inst[r["instance"]] = (root, r)
        observed += [dict(o, machine=machine) for o in res["observed_only"]]
        failed += [dict(f, machine=machine) for f in res["run_failed"]]
        for c in ("U", "duplicate", "S"):
            controls[c] += [dict(x, machine=machine) for x in res["controls"][c]]
        for dx in sorted(root.glob("DUPX_*")):
            name = dx.name[len("DUPX_"):]
            orig = by_inst.get(name)
            entry = dict(instance=name, duplicate_machine=machine)
            if orig is None:
                entry["why"] = "original instance not in the analysed OUTROOTs (yet)"
            else:
                entry.update(original_machine=orig[1]["machine"], **{f"{k}_identical": v for k, v in
                                                                     same_n0(orig[0] / name / "N0", dx / "N0").items()})
            controls["cross_machine_duplicates"].append(entry)
    # duplicates listed before their original's machine is read: resolve once more
    for e in controls["cross_machine_duplicates"]:
        if "original_machine" not in e and e["instance"] in by_inst:
            root, r = by_inst[e["instance"]]
            dup_root = roots[int(e["duplicate_machine"].split("_")[1]) - 1]
            e.pop("why", None)
            e.update(original_machine=r["machine"], **{f"{k}_identical": v for k, v in
                                                       same_n0(root / e["instance"] / "N0", dup_root / f"DUPX_{e['instance']}" / "N0").items()})
    groups = {}
    allgroups = sorted({g for p in plans.values() for g in p["groups"]})
    for g in allgroups:
        rs = [r for r in rows if r["group"] == g]
        out = dict(instances=len(rs), eligible_K0=sum(1 for r in rs if (r.get("stage_d") or {}).get("eligible_K0")),
                   room_K3=sum(1 for r in rs if (r.get("stage_d") or {}).get("room_K3")))
        for level in ("K0", "K3"):
            counted = [r for r in rs if (r.get(level) or {}).get("counted")]
            ref = sorted(r["instance"] for r in counted if r[level]["refuted"])
            out[level] = dict(counted=len(counted), refuted_instances=ref, threshold=A.THRESHOLD[level],
                              verdict=A.word(len(counted), bool(ref), level),
                              not_sealed=sorted(r["instance"] for r in rs if (r.get(level) or {}).get("not_sealed")))
        mr = [r for r in rs if r.get("max_rule_comparison")]
        out["max_rule_comparison_counts_for_nothing"] = dict(
            eligible_K0=sum(1 for r in mr if r["max_rule_comparison"]["eligible_K0"]),
            room_K3=sum(1 for r in mr if r["max_rule_comparison"]["room_K3"]),
            room_only_under_one_port=sorted(r["instance"] for r in mr if r["stage_d"]["room_K3"] and not r["max_rule_comparison"]["room_K3"]))
        groups[g] = out
    family = {}
    for level in ("K0", "K3"):
        vs = [groups[g][level]["verdict"] for g in groups]
        family[level] = "refuted" if "refuted" in vs else "established" if vs and all(v == "established" for v in vs) else "worded per group"
    rows.sort(key=lambda r: (r["group"], r["seed"]))
    res = dict(format=FORMAT, analyze3_sha256=A.sha(__file__), times_source=times_src, machines=len(roots),
               env={m: dict(static_sha256=e["static_sha256"], env_json_sha256=e["env_json_sha256"]) for m, e in envs.items()},
               groups=groups, family=family, seal_defects=defects, observed_only=observed, run_failed=failed,
               controls=controls, instances=rows, thresholds=A.THRESHOLD)
    outdir = Path(outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    (outdir / "RESULTS.json").write_bytes(A.canon(res))
    (outdir / "SHA256SUMS").write_text(f"{A.sha(outdir / 'RESULTS.json')}  RESULTS.json\n")
    print(json.dumps(dict(results_sha256=A.sha(outdir / "RESULTS.json"), groups={g: (v["K0"]["verdict"], v["K3"]["verdict"])
                                                                                for g, v in groups.items()},
                          family=family, seal_defects=defects), indent=1, sort_keys=True))
    return True


if __name__ == "__main__":
    sys.exit(0 if main(*sys.argv[1:]) else 1)
