"""The campaign analysis: one file, in place of analyze.py … analyze10.py (the owner's decision, relayed 2026-11-26).
It is analyze10 flattened, with no new rule. Each former layer is a function, applied in order, with a JSON round trip
between them as before.

  analysis.py MODE OUTDIR ROOT [ROOT ...] [times=github|bare|lsremote:LOG] [thresholds=FILE] [controls=DIR]

MODE:
- **campaign:** every ROOT must come from campaign.py in campaign mode: its ENV.json names this tree's campaign.py by
  sha256, the frozen template (campaign.FROZEN_TEMPLATE_SHA256), and mode CAMPAIGN. Any other root is refused, and so
  is a mix.
- **test:** any root (a test run, or a root of the old chain). RESULTS.json then says "mode": "TEST".

It never opens a root for writing:
- It writes only to OUTDIR (refused if it lies inside a root) and to temporary folders outside the roots.
- Every root's SHA256SUMS files are hashed before and after the analysis. Both are recorded (`roots_sha256sums`), and
  a change is a refusal.
- The seal regeneration recomputes each prediction from its sealed stage-D record with stage_d6.py, a calculation
  without simulation. It uses this tree's pinned Lean binary (envcheck_layered3.LEAN_SHA256) and the kernel library,
  built into OUTDIR/kernel_build from the 12 pinned sources (campaign.KERNEL_SOURCES).

THE LAYERS, in order (each as its file's docstring states):
1. per root (analyze, analyze2): the instances, K0/K3 counting, the observed-only list, run_failed, the controls, the
   max-rule comparison, and ENV (mixed environments refused);
2. over the roots (analyze3): the seal regeneration and the seal-log check (push before stage N), and the
   cross-machine duplicates' records;
3. analyze4: N<n>/SEAL_LOG.json against the log;
4. analyze5: the thresholds of thresholds.json;
5. analyze6: the records' own seal_log;
6. analyze7: the duplicates judged by the controls' tests/check_duplicate.py;
7. analyze8: the proportional D4 rule (d4_regate.py);
8. analyze9: the counts side by side;
9. analyze10: the stage-D script named by the prediction, stage_d6 with its kernel field.

RESULTS.json is analyze10's, with these changes, all listed: the format (layered-campaign-analysis/1), analysis_sha256
in place of analyze*_sha256, `mode`, `roots_sha256sums`, `root_drivers` and `pins`; and these defect fixes (the
audit's A1–A6):
- K3: an instance is refuted if ANY completed sealed comparison of a noisy round is "refuted"; held only if every
  round completed and agrees; not completed when no completed round refutes and a round is missing. The seal-log
  checks of a counted level read only its completed rounds.
- Eligibility and room are read from the SEALED prediction (seal/<inst>.json); an instance whose D/prediction.json
  differs from its seal is a seal defect (not sealed, not counted).
- The thresholds are read once, before the first layer (there is no constant default).
- The not_sealed row lists each instance with its comparison verdicts.
- first_failing uses the one step order (ORDER, sealpush included).
- Campaign mode: FREEZE_PINS.json checked over this tree (campaign.pins_check) and the tree clean; thresholds = the
  pinned thresholds.json only; times = github or lsremote:LOG only; controls = the noise tree at the frozen template's
  noise_commit (found among this repository's clean worktrees). Test mode leaves these free.
"""
import contextlib
import datetime
import hashlib
import importlib.util
import io
import json
import os
from fractions import Fraction as F
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign as CP  # noqa: E402  (its constants only: the frozen template, the kernel sources and the kernel build)
import d4_regate as D4  # noqa: E402
import envcheck_layered3 as E3  # noqa: E402
import sealpush as SP  # noqa: E402

PY = sys.executable
FORMAT = "layered-campaign-analysis/1"
SCRIPTS = ("stage_d6.py", "stage_d5.py", "stage_d4.py", "stage_d3.py")
SOLO = "this run's solo scans"
ASSUMPTION = ("the unaudited instances are taken to be no worse than the worst audited instance of their group "
              "(the rule regates them at that group's largest audited value; it does not measure them)")
RULE10 = ("the stage-D script is the latest stage_d<N>.py the sealed prediction names in `code` (stage_d6.py names "
          "itself); a prediction naming stage_d6.py must carry `kernel` and one carrying `kernel` must name stage_d6.py; "
          "the regeneration (with stage_d6, on the kernel library built from the pinned Lean sources) must equal the "
          "sealed bytes, the kernel field included")
ROWS = ("held", "refuted", "premise_flagged_D4", "not_sealed", "not_completed", "no_prediction")
ORDER = ["deck", "inverters", "D", "seal", "sealpush", "N0", "C0", "N1", "C1", "N2", "C2", "N3", "C3"]


class Refused(SystemExit):
    pass


def canon(obj):
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def rt(obj):
    """The JSON round trip each former layer made through RESULTS.json."""
    return json.loads(canon(obj))


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def word(k, refuted, threshold):
    if refuted:
        return "refuted"
    if k >= threshold:
        return "established"
    if k >= 2:
        return f"held on {k} instances, not established"
    return "held on one instance" if k == 1 else "not established"


def family_of(groups):
    fam = {}
    for level in ("K0", "K3"):
        vs = [groups[g][level]["verdict"] for g in groups]
        fam[level] = "refuted" if "refuted" in vs else "established" if vs and all(x == "established" for x in vs) else "worded per group"
    return fam


def strip(x):
    """check_duplicate's exception: "cost", "wall_s", "cpu_s" and keys ending in "_wall_s" or "_cpu_s", at any depth."""
    if isinstance(x, dict):
        return {k: strip(v) for k, v in x.items()
                if not (k in ("cost", "wall_s", "cpu_s") or k.endswith(("_wall_s", "_cpu_s")))}
    if isinstance(x, list):
        return [strip(v) for v in x]
    return x


def parse_utc(t):
    t = t.rstrip("Z")
    for fmt in ("%Y-%m-%dT%H:%M:%S.%f", "%Y-%m-%dT%H:%M:%S"):
        try:
            return datetime.datetime.strptime(t[:26], fmt).replace(tzinfo=datetime.timezone.utc)
        except ValueError:
            pass
    raise ValueError(t)


# ================================================================================================ 1. per root

class Reader:
    def __init__(self, root):
        self.root, self.inputs = Path(root), {}

    def json(self, rel):
        p = self.root / rel
        if not p.exists():
            return None
        self.inputs[str(rel)] = sha(p)
        return json.loads(p.read_text())


def first_failing(status):
    for k in ORDER:
        st = status["steps"].get(k)
        if st and st["status"] != "done":
            return dict(step=k, status=st["status"], why=st.get("why"))
    return None


def max_rule(root, name, plan, group):
    import fit3
    import spec as specmod
    import stage_d
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


def analyze_root(root):
    R = Reader(root)
    plan = R.json("PLAN.json")
    rounds = plan["rounds"]
    insts, observed_only, run_failed = [], [], []
    for st_path in sorted(Path(root).glob("*/status.json")):
        name = st_path.parent.name
        status = R.json(f"{name}/status.json")
        group = status["group"]
        seal_file = next((p for p in sorted((Path(root) / name / "seal").glob("*.json")) if p.name != "MANIFEST.json"), None)
        pred = R.json(str(seal_file.relative_to(root))) if seal_file else R.json(f"{name}/D/prediction.json")
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
        noisy = [comps[n] for n in range(1, rounds + 1)]
        if pred["room_K3"]:
            done_ = [c for c in noisy if c is not None and c["verdict"] in ("agrees", "refuted")]
            if any(c["verdict"] == "refuted" for c in done_):      # one completed refuting round refutes
                row["K3"] = dict(counted=True, refuted=True)
            elif len(done_) == len(noisy):                          # held only if every round completed and agrees
                row["K3"] = dict(counted=True, refuted=False)
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
        row["max_rule_comparison"] = max_rule(root, name, plan, group)
        row["cost"] = {k: dict(cpu_s=v.get("cpu_s"), wall_s=v.get("wall_s")) for k, v in sorted(status["steps"].items())}
        row["cost_total"] = dict(cpu_s=round(sum(v.get("cpu_s") or 0 for v in status["steps"].values()), 1))
        insts.append(row)
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
    return rt(dict(observed_only=observed_only, run_failed=run_failed, controls=controls, instances=insts))


def env_section(root):
    root = Path(root)
    f = root / "ENV.json"
    if not f.exists():
        raise Refused(f"refused: {root} has no ENV.json")
    env = json.loads(f.read_text())
    h = sha(f)
    bad = []
    resumes = json.loads((root / "ENV_RESUMES.json").read_text()) if (root / "ENV_RESUMES.json").exists() else []
    bad += [f"resume at {r['uptime_s']}: static {r['static_sha256'][:12]}" for r in resumes if r["static_sha256"] != env["static_sha256"]]
    per = {}
    for st in sorted(root.glob("*/status.json")):
        name = st.parent.name
        s = json.loads(st.read_text()).get("env_sha256")
        pf = st.parent / "D" / "prediction.json"
        p = json.loads(pf.read_text()).get("env_sha256") if pf.exists() else "no prediction"
        per[name] = dict(status=s, prediction=p)
        if s != h:
            bad.append(f"{name}: status env {s}")
        if pf.exists() and p != h:
            bad.append(f"{name}: prediction env {p}")
    if bad:
        raise Refused("refused: mixed environments in one OUTROOT: " + "; ".join(bad))
    return dict(env_json_sha256=h, static_sha256=env["static_sha256"], static=env["static"],
                uptime_s=env["uptime_s"], resumes=[r["uptime_s"] for r in resumes], instances=per)


# ================================================================================================ 2. seals (analyze3, analyze10)

def regenerate(root, name, plan, status, kernel_build):
    d = Path(root) / name
    seal_file = next((p for p in (d / "seal").glob("*.json") if p.name != "MANIFEST.json"), None)
    if seal_file is not None:                                  # analyze10's check comes first
        p10 = json.loads(seal_file.read_bytes())
        names6, kernel = "stage_d6.py" in p10.get("code", {}), "kernel" in p10
        if names6 and not kernel:
            return False, "the sealed prediction names stage_d6.py but has no kernel field"
        if kernel and not names6:
            return False, "the sealed prediction has a kernel field but does not name stage_d6.py"
    if seal_file is None or not (d / "D" / "record.json").exists():
        return False, "no seal or no stage-D record"
    sealed = seal_file.read_bytes()
    pred = json.loads(sealed)
    script = next((s for s in SCRIPTS if s in pred.get("code", {})), None)
    if script is None:
        return False, "the sealed prediction names no stage-D script"
    spec = HERE / plan["groups"][status["group"]]["spec"]
    with tempfile.TemporaryDirectory() as t:
        t = Path(t)
        for f in ("record.json", "overlay_d.json"):
            shutil.copyfile(d / "D" / f, t / f)
        args = [PY, "-B", str(HERE / script), "predict", str(spec), str(t), f"rule={pred.get('testError_rule', 'one-port')}"]
        if (d / "inv" / "inverter_gate.json").exists():
            (t / "inv").mkdir()
            shutil.copyfile(d / "inv" / "inverter_gate.json", t / "inv" / "inverter_gate.json")
            args.append(f"inverters={t / 'inv' / 'inverter_gate.json'}")
        env = dict(os.environ, LAYERED_KERNEL_BUILD=str(kernel_build))
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
    want = sha(Path(root) / name / "seal" / "SHA256SUMS")
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
            out[f] = strip(json.loads((a / f).read_text())) == strip(json.loads((b / f).read_text()))
        else:
            out[f] = None
    if (a / "input.spice").exists() and (b / "input.spice").exists():
        out["input.spice"] = (a / "input.spice").read_bytes() == (b / "input.spice").read_bytes()
    return out


def layer_seals(roots, times_src, kernel_build, th):
    rows, observed, failed, controls, envs, defects = [], [], [], dict(U=[], duplicate=[], S=[], cross_machine_duplicates=[]), {}, []
    logs, by_inst, plans = {}, {}, {}
    for k, root in enumerate(roots):
        machine = f"machine_{k + 1}"
        envs[machine] = env_section(root)
        res = analyze_root(root)
        plan = json.loads((root / "PLAN.json").read_text())
        plans[machine] = plan
        for r in res["instances"]:
            r["machine"] = machine
            status = json.loads((root / r["instance"] / "status.json").read_text())
            if r.get("stage_d") is not None:
                ok1, why1 = regenerate(root, r["instance"], plan, status, kernel_build)
                sf = next((p for p in sorted((root / r["instance"] / "seal").glob("*.json")) if p.name != "MANIFEST.json"), None)
                dp = root / r["instance"] / "D" / "prediction.json"
                if ok1 and (sf is None or not dp.exists() or dp.read_bytes() != sf.read_bytes()):
                    ok1, why1 = False, "D/prediction.json differs from its seal (the sealed prediction is the one read)"
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
                entry.update(original_machine=orig[1]["machine"], **{f"{k_}_identical": v for k_, v in
                                                                     same_n0(orig[0] / name / "N0", dx / "N0").items()})
            controls["cross_machine_duplicates"].append(entry)
    for e in controls["cross_machine_duplicates"]:
        if "original_machine" not in e and e["instance"] in by_inst:
            root, r = by_inst[e["instance"]]
            dup_root = roots[int(e["duplicate_machine"].split("_")[1]) - 1]
            e.pop("why", None)
            e.update(original_machine=r["machine"], **{f"{k_}_identical": v for k_, v in
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
            out[level] = dict(counted=len(counted), refuted_instances=ref, threshold=th[level][g],
                              verdict=word(len(counted), bool(ref), th[level][g]),
                              not_sealed=sorted(r["instance"] for r in rs if (r.get(level) or {}).get("not_sealed")))
        mr = [r for r in rs if r.get("max_rule_comparison")]
        out["max_rule_comparison_counts_for_nothing"] = dict(
            eligible_K0=sum(1 for r in mr if r["max_rule_comparison"]["eligible_K0"]),
            room_K3=sum(1 for r in mr if r["max_rule_comparison"]["room_K3"]),
            room_only_under_one_port=sorted(r["instance"] for r in mr if r["stage_d"]["room_K3"] and not r["max_rule_comparison"]["room_K3"]))
        groups[g] = out
    rows.sort(key=lambda r: (r["group"], r["seed"]))
    if times_src.startswith("lsremote:"):
        lp = Path(times_src.split(":", 1)[1])
        src_desc = dict(source="lsremote (coordinator's ls-remote log; first-seen times, upper bounds of the push times)",
                        log=lp.name, log_sha256=sha(lp) if lp.exists() else None)
    else:
        src_desc = dict(source={"github": "GitHub repository activity API (push timestamps)",
                                "bare": "local bare repository post-receive log"}.get(times_src, times_src))
    return rt(dict(times_source=src_desc, machines=len(roots),
                   env={m: dict(static_sha256=e["static_sha256"], env_json_sha256=e["env_json_sha256"]) for m, e in envs.items()},
                   groups=groups, family=family_of(groups), seal_defects=defects, observed_only=observed, run_failed=failed,
                   controls=controls, instances=rows, thresholds=dict(K0=th["K0"], K3=th["K3"])))


# ================================================================================================ 3–6

def regroup(res, threshold_of):
    for g, v in res["groups"].items():
        rs = [r for r in res["instances"] if r["group"] == g]
        for level in ("K0", "K3"):
            counted = [r for r in rs if (r.get(level) or {}).get("counted")]
            ref = sorted(r["instance"] for r in counted if r[level]["refuted"])
            v[level].update(counted=len(counted), refuted_instances=ref,
                            verdict=word(len(counted), bool(ref), threshold_of(g, level)),
                            not_sealed=sorted(r["instance"] for r in rs if (r.get(level) or {}).get("not_sealed")))
    res["family"] = family_of(res["groups"])


def completed_rounds(r, level):
    """The rounds of a counted level whose comparison completed: N0 at K0; at K3 the completed noisy rounds (all three
    for a held instance, at least the refuting one for a refuted instance)."""
    if level == "K0":
        return [0]
    comps = r.get("comparisons") or {}
    return [n for n in (1, 2, 3) if (comps.get(f"C{n}") or {}).get("verdict") in ("agrees", "refuted")]


def layer_stage_n_seal_log(res, roots, th):
    for r in res["instances"]:
        root = roots[int(r["machine"].split("_")[1]) - 1]
        commit = ((r.get("seal") or {}).get("log") or {}).get("commit")
        for level in ("K0", "K3"):
            if not (r.get(level) or {}).get("counted"):
                continue
            bad = []
            for n in completed_rounds(r, level):
                f = root / r["instance"] / f"N{n}" / "SEAL_LOG.json"
                got = json.loads(f.read_text()).get("commit") if f.exists() else None
                if got is None or got != commit:
                    bad.append(f"N{n}: SEAL_LOG.json {'missing' if got is None else got[:12]} vs log {str(commit)[:12]}")
            if bad:
                r[level] = dict(counted=False, not_sealed=True)
                res["seal_defects"].append(dict(machine=r["machine"], instance=r["instance"], stage_n_seal_log=bad))
    regroup(res, lambda g, level: th[level][g])
    return rt(res)


def layer_thresholds(res, tf, th):
    for g, v in res["groups"].items():
        for level in ("K0", "K3"):
            t = th[level][g]
            v[level].update(threshold=t, verdict=word(v[level]["counted"], bool(v[level]["refuted_instances"]), t))
    res["family"] = family_of(res["groups"])
    res.update(thresholds=dict(file=Path(tf).name, sha256=sha(tf), K0=th["K0"], K3=th["K3"]))
    return rt(res)


def layer_record_seal_log(res, roots):
    for r in res["instances"]:
        root = roots[int(r["machine"].split("_")[1]) - 1]
        plan = json.loads((root / "PLAN.json").read_text())
        branch = (plan.get("seal_push") or {}).get("branch")
        commit = ((r.get("seal") or {}).get("log") or {}).get("commit")
        for level in ("K0", "K3"):
            if not (r.get(level) or {}).get("counted"):
                continue
            bad = []
            for n in completed_rounds(r, level):
                f = root / r["instance"] / f"N{n}" / "noisy_record.json"
                sl = json.loads(f.read_text()).get("seal_log") if f.exists() else None
                if not sl or sl.get("commit") != commit or sl.get("branch") != branch:
                    bad.append(f"N{n}: record seal_log {sl} vs log {str(commit)[:12]} on {branch}")
            if bad:
                r[level] = dict(counted=False, not_sealed=True)
                res["seal_defects"].append(dict(machine=r["machine"], instance=r["instance"], record_seal_log=bad))
    th = res["thresholds"]
    regroup(res, lambda g, level: th[level][g])
    useal = []
    for k, root in enumerate(roots, start=1):
        for f in sorted(root.glob("U_*/U/untrained_record.json")):
            useal.append(dict(machine=f"machine_{k}", instance=f.parent.parent.name[2:], seal_log=json.loads(f.read_text()).get("seal_log")))
    res["controls"]["U_seal_log"] = useal
    return rt(res)


def load_checker(path):
    spec = importlib.util.spec_from_file_location("check_duplicate_analysis", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def judge(chk, a, b):
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        ok = bool(chk.main(str(a), str(b)))
    return ok, out.getvalue().splitlines()


def layer_duplicates(res, roots, controls_dir):
    where = {}
    for k, root in enumerate(roots, start=1):
        for st in root.glob("*/status.json"):
            where.setdefault(st.parent.name, (k, root))
    xs = []
    for k, root in enumerate(roots, start=1):
        for dx in sorted(root.glob("DUPX_*")):
            name = dx.name[len("DUPX_"):]
            e = dict(instance=name, duplicate_machine=f"machine_{k}")
            if name not in where:
                e["why"] = "original instance not in the analysed OUTROOTs"
                xs.append(e)
                continue
            ok_, oroot = where[name]
            e["original_machine"] = f"machine_{ok_}"
            ctl = Path(controls_dir) if controls_dir else \
                Path(json.loads((oroot / "PLAN.json").read_text())["noise_tree"]) / "research" / "layered-networks"
            cp = ctl / "tests" / "check_duplicate.py"
            e["checker"] = dict(file="tests/check_duplicate.py", sha256=sha(cp) if cp.exists() else None)
            if cp.exists():
                ident, lines = judge(load_checker(cp), oroot / name / "N0", dx / "N0")
                e.update(identical=ident, checker_lines=lines)
            else:
                e.update(identical=None, why="check_duplicate.py not found")
            sc = dx / "seal_check.json"
            if sc.exists():
                s = json.loads(sc.read_text())
                s.pop("seal_dir", None)
                e["seal_check"] = s
            sf = dx / "seal_fetch.json"
            if sf.exists():
                f = json.loads(sf.read_text())
                f.pop("remote", None)
                e["seal_fetch"] = f
            c_dup, c_orig = dx / "N0" / "comparison.json", oroot / name / "N0" / "comparison.json"
            if c_dup.exists():
                cd = json.loads(c_dup.read_text())
                e["comparison"] = dict(verdict=cd.get("verdict"), equals_original=c_orig.exists() and
                                       strip(cd) == strip(json.loads(c_orig.read_text())))
            else:
                e["comparison"] = None
            xs.append(e)
    res["controls"]["cross_machine_duplicates_v3"] = res["controls"].pop("cross_machine_duplicates", [])
    res["controls"]["cross_machine_duplicates"] = xs
    return rt(res)


# ================================================================================================ 7. D4 (analyze8)

def is_audited(inst_dir):
    f = Path(inst_dir) / "D" / "fit_d.json"
    if not f.exists():
        return False
    cells = json.loads(f.read_text()).get("cells", [])
    return any(((c.get("budgets") or {}).get("K0") or {}).get("D4_source") == SOLO for c in cells)


def layer_d4(res, roots):
    plans = [json.loads((r / "PLAN.json").read_text()) for r in roots]
    inst_dir = lambda r: roots[int(r["machine"].split("_")[1]) - 1] / r["instance"]
    spec_of = lambda r: HERE / plans[int(r["machine"].split("_")[1]) - 1]["groups"][r["group"]]["spec"]
    rows, frozen = res["instances"], D4.FROZEN
    groups, flags = {}, {}
    for g in sorted({r["group"] for r in rows}):
        rs = sorted((r for r in rows if r["group"] == g), key=lambda r: (r["machine"], r["instance"]))
        aud = [r for r in rs if is_audited(inst_dir(r))]
        ls = []
        for r in aud:
            for c, by_g in sorted(D4.audited_lines(inst_dir(r) / "D").items()):
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
                reg = D4.regate(spec_of(r), inst_dir(r), star)
                sec["regated"].append(dict(machine=r["machine"], instance=r["instance"], **{
                    k: reg[k] for k in ("reproduces_sealed", "sealed", "regated", "gate_holds_K0", "gate_holds_K3",
                                        "newly_failing_K0", "newly_failing_K3")}))
                for level in ("K0", "K3"):
                    if (r.get(level) or {}).get("counted") and not reg[f"gate_holds_{level}"]:
                        sec["premise_flagged_D4"][level].append(r["instance"])
                        flags.setdefault((r["machine"], r["instance"]), {})[level] = reg
        groups[g] = sec
    for r in res["instances"]:
        for level in flags.get((r["machine"], r["instance"]), {}):
            if r[level].get("refuted"):
                r[level] = dict(r[level], premise_flagged_D4=True)
                continue
            r[level] = dict(r[level], counted=False, premise_flagged_D4=True)
    th = res["thresholds"]
    for g, v in res["groups"].items():
        rs = [r for r in res["instances"] if r["group"] == g]
        for level in ("K0", "K3"):
            counted = [r for r in rs if (r.get(level) or {}).get("counted")]
            ref = sorted(r["instance"] for r in counted if r[level].get("refuted"))
            v[level].update(counted=len(counted), refuted_instances=ref, verdict=word(len(counted), bool(ref), th[level][g]),
                            premise_flagged_D4=sorted(r["instance"] for r in rs if (r.get(level) or {}).get("premise_flagged_D4")))
    for level in ("K0", "K3"):
        vs = [res["groups"][g][level]["verdict"] for g in res["groups"]]
        res["family"][level] = "refuted" if "refuted" in vs else "established" if vs and all(x == "established" for x in vs) else "worded per group"
    res["d4_audit"] = dict(rule="proportional D4 (see analyze8.py)", assumption=ASSUMPTION, groups=groups)
    return rt(res)


# ================================================================================================ 8. counts (analyze9)

def never_run(r, lv):
    steps = r.get("steps") or {}
    need = [k for k in (ORDER[:7] if lv == "K0" else ORDER) if not (k == "inverters" and r["group"] == "ANDOR3")]
    miss = next((k for k in need if k not in steps), None)
    return dict(step=miss, status="not run")


def layer_counts(res):
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
                    row["not_sealed"].append(dict(instance=name, verdicts={
                        k: (c or {}).get("verdict") for k, c in sorted((r.get("comparisons") or {}).items())}))
                elif (r["machine"], name, lv) in failed:
                    ff = failed[(r["machine"], name, lv)] or never_run(r, lv)
                    row["not_completed"].append(dict(instance=name, step=ff.get("step"), status=ff.get("status")))
                else:
                    row["no_prediction"].append(name)
            n = {k: len(v) for k, v in row.items()}
            assert sum(n.values()) == len(rs), (g, lv, n, len(rs))
            out[g][lv] = dict(instances=len(rs), counted=n["held"] + n["refuted"], **{k: dict(n=n[k], list=row[k]) for k in ROWS})
    res["counts"] = out
    for g, v in res["counts"].items():
        for lv in ("K0", "K3"):
            assert v[lv]["counted"] == res["groups"][g][lv]["counted"], (g, lv)
    return rt(res)


# ================================================================================================ the checks around it

def root_driver(root):
    """(driver sha256, template sha256, mode) a root records, or Nones for a root of the old chain."""
    env = json.loads((Path(root) / "ENV.json").read_text()) if (Path(root) / "ENV.json").exists() else {}
    c = env.get("campaign") or {}
    return dict(driver_sha256=c.get("driver_sha256"), template_sha256=c.get("template_sha256"), mode=c.get("mode"))


def sums_of(roots):
    out = {}
    for k, root in enumerate(roots, start=1):
        files = sorted(p for p in Path(root).rglob("SHA256SUMS") if "lean_build" not in p.parts)
        out[f"machine_{k}"] = hashlib.sha256("".join(f"{sha(p)}  {p.relative_to(root)}\n" for p in files).encode()).hexdigest()
    return out


def kernel_library(outdir):
    r = E3.lean_resolution()                               # the real toolchain binary, not elan's proxy
    if r.get("sha256") != E3.LEAN_SHA256:
        raise Refused(f"refused: the lean binary is not the pinned one ({E3.LEAN_SHA256[:12]}): {r.get('sha256')}")
    have = {f"{m}.lean": sha(CP.LEAN_DIR / f"{m}.lean") for m in CP.KERNEL_MODULES}
    if have != CP.KERNEL_SOURCES:
        raise Refused("refused: the kernel's Lean sources differ from the pinned ones")
    return CP.build_kernel(outdir)


def main(mode, outdir, *args):
    if mode not in ("campaign", "test"):
        raise Refused(f"refused: mode {mode!r} is neither campaign nor test")
    args = [str(a) for a in args]
    kw = dict(a.split("=", 1) for a in args if "=" in a)
    roots = [Path(a).resolve() for a in args if "=" not in a]
    out = Path(outdir).resolve()
    for r in roots:
        if out == r or r in out.parents:
            raise Refused(f"refused: OUTDIR {out} lies inside the root {r}")
    drivers = {f"machine_{k}": root_driver(r) for k, r in enumerate(roots, start=1)}
    times = kw.get("times", "github")
    tf = Path(kw.get("thresholds", str(HERE / "thresholds.json"))).resolve()
    controls = kw.get("controls")
    pc = CP.pins_check()
    if mode == "campaign":
        if CP.pins_refusal(pc):
            raise Refused("refused: campaign mode: " + CP.pins_refusal(pc))
        pinned = {p: h for fs in json.loads(CP.PINS.read_text())["groups"].values() for p, h in fs.items()}
        if tf != (HERE / "thresholds.json").resolve() or pinned.get("research/layered-networks/thresholds.json") != sha(tf):
            raise Refused("refused: campaign mode reads the pinned thresholds.json only")
        if not (times == "github" or times.startswith("lsremote:")):
            raise Refused(f"refused: campaign mode: times must be github or lsremote:LOG, not {times!r}")
        noise_commit = json.loads(CP.FROZEN_TEMPLATE.read_text())["noise_commit"]
        trees = [p for p, h in CP.worktrees() if h == noise_commit and CP.git_head(p)[1]]
        if not trees:
            raise Refused(f"refused: campaign mode: no clean worktree at the template's noise_commit {noise_commit[:12]}")
        want = (Path(trees[0]) / "research" / "layered-networks").resolve()
        if controls is not None and Path(controls).resolve() != want:
            raise Refused(f"refused: campaign mode: controls must be the noise tree at {noise_commit[:12]} ({want})")
        controls = str(want)
        bad = [m for m, d in drivers.items() if d != dict(driver_sha256=sha(HERE / "campaign.py"),
                                                          template_sha256=CP.FROZEN_TEMPLATE_SHA256, mode="CAMPAIGN")]
        if bad:
            raise Refused(f"refused: roots not run by this campaign.py on the frozen template in campaign mode: {bad}")
    th = json.loads(tf.read_text())
    before = sums_of(roots)
    out.mkdir(parents=True, exist_ok=True)
    build = kernel_library(out)
    res = layer_seals(roots, times, build, th)
    res = layer_stage_n_seal_log(res, roots, th)
    res = layer_thresholds(res, tf, th)
    res = layer_record_seal_log(res, roots)
    res = layer_duplicates(res, roots, controls)
    res = layer_d4(res, roots)
    res = layer_counts(res)
    after = sums_of(roots)
    if after != before:
        raise Refused(f"refused: a root's SHA256SUMS changed during the analysis: {before} -> {after}")
    res.update(format=FORMAT, analysis_sha256=sha(__file__), mode="CAMPAIGN" if mode == "campaign" else "TEST",
               stage_d_script_rule=RULE10, kernel_sources_sha256=CP.KERNEL_SOURCES, root_drivers=drivers,
               roots_sha256sums=dict(before=before, after=after), pins=pc)
    (out / "RESULTS.json").write_bytes(canon(res))
    (out / "SHA256SUMS").write_text(f"{sha(out / 'RESULTS.json')}  RESULTS.json\n")
    print(json.dumps(dict(results_sha256=sha(out / "RESULTS.json"), mode=res["mode"],
                          counts={g: {lv: {k: (x[k]["n"] if isinstance(x[k], dict) else x[k]) for k in ("counted",) + ROWS}
                                      for lv, x in v.items()} for g, v in res["counts"].items()}), indent=1))
    return True


if __name__ == "__main__":
    if len(sys.argv) < 4:
        sys.exit(__doc__)
    sys.exit(0 if main(*sys.argv[1:]) else 1)
