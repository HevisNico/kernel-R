import contextlib
import datetime
import fnmatch
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
FORMAT = "layered-campaign-analysis/2"
SCRIPTS = ("stage_d6.py", "stage_d5.py", "stage_d4.py", "stage_d3.py")
SOLO = "this run's solo scans"
ASSUMPTION = ("the unaudited instances are taken to be no worse than the worst audited instance of their group "
              "(the rule regates them at that group's largest audited value; it does not measure them)")
RULE10 = ("the stage-D script is the latest stage_d<N>.py the sealed prediction names in `code` (stage_d6.py names "
          "itself); a prediction naming stage_d6.py must carry `kernel` and one carrying `kernel` must name stage_d6.py; "
          "the regeneration (with stage_d6, on the kernel library built from the pinned Lean sources) must equal the "
          "sealed bytes, the kernel field included")
ROWS = ("held", "refuted", "refuted_stopped_by_own_check", "premise_flagged_D4", "not_sealed", "not_completed",
        "no_prediction", "not_run")
ORDER = ["deck", "inverters", "D", "seal", "sealpush", "N0", "C0", "N1", "C1", "N2", "C2", "N3", "C3"]

# ---- the draw (D8, B16): the sizes and the machine count are pinned here, with this file
DRAW_SIZES = dict(NOT1=60, ANDOR3=32, XOR3=37)
DRAW_SIZES_REHEARSAL = dict(NOT1=4, ANDOR3=4, XOR3=4)
MACHINES = 12
DRAW_EXTRA_KEY = "beacon_round"          # drand's /public/<round>: {"round", "signature", "randomness"}
PLAN_LOCAL_KEYS = ("kit_tree", "noise_tree")   # campaign.resolve_trees: the only machine-local keys of PLAN.json
KEYS = ("draw", "rehearsal", "times", "thresholds", "controls", "tips")

# ---- the comparisons (A2, A6)
VERDICTS = ("agrees", "refuted", "run failed", "observed only (no prediction)")      # compare_d.compare's verdicts
SIMULATOR_END = ("the simulator ended during: ", "fatal simulator message during: ")  # session.py's RuntimeErrors

# ---- the files read from a root that no manifest covers (B8), and how each is checked
UNMANIFESTED = {
    "*/status.json": "a home instance's steps: cross-checked against RESULT_INSTANCES.json when the root has it",
    "ENV.json": "the root's environment: each status.json and prediction must name its sha256 (mixed roots refused)",
    "ENV_RESUMES.json": "the resumes' static environment: must equal ENV.json's",
    "TEMPLATE_CHECK.json": "the driver's check: its trees must equal PLAN.json's local keys; its pins sha is checked",
    "PLAN_INPUT.json": "checked byte for byte against the expected plan (with draw=); read as the plan otherwise",
    "PLAN_RESOLVED.json": "must be byte-identical to PLAN.json",
    "PLAN.json": "under the root's SHA256SUMS when the root finished; checked against the expected plan (with draw=)",
    "RESULT.json": "under the root's SHA256SUMS when the root finished: job_errors and stopped_for_disk only",
    "RESULT_INSTANCES.json": "under SHA256SUMS.instances when the instances finished: job_errors, stopped_for_disk, "
                             "and the steps cross-check",
    "U_*/U/untrained_record.json": "the untrained control's record: its seal_log is reported, never counted",
    "*/N0/input.spice": "the N0 deck of a remote duplicate's original (keep_raw): compared, never counted",
    "*/N0/trace.raw": "the N0 raw of a remote duplicate's original (keep_raw): read by check_duplicate, never counted",
}
NOT_WALKED = ("lean_build", "kernel_build")      # per-machine Lean builds: the analysis builds and uses its own

# ---- the regeneration child (B11)
REGEN_ENV = ("PATH", "HOME", "LANG", "LC_ALL", "TMPDIR")


class Refused(SystemExit):
    pass


def refuse(msg):
    raise Refused("refused: " + msg)


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


def own_check(status):
    """A2, the exact criterion: True iff a stage-N record's status says the run was stopped by its own check, i.e. it
    starts with "failed: " (controls4/noise3 record any exception of the lessons, tests and skew slots so) and is not
    one of session.py's two simulator ends. A timeout or a killed stage N writes no record at all."""
    return isinstance(status, str) and status.startswith("failed: ") and \
        not status[len("failed: "):].startswith(SIMULATOR_END)


# ================================================================================================ the files of a root

class Root:
    """One root: its verified files (D10), and the reads of this script (B8)."""

    def __init__(self, path):
        self.path = Path(path)
        self.verified = {}                         # rel path -> sha256, every line of every SHA256SUMS verified
        self.bad = []
        self.inst_manifest = set()                 # instance folders whose SHA256SUMS verified
        self.finished = (self.path / "DONE").exists() and (self.path / "SHA256SUMS").exists()
        self.instances_done = (self.path / "INSTANCES_DONE").exists() and (self.path / "SHA256SUMS.instances").exists()
        self.reads = set()

    def walk(self):
        for m in sorted(self.path.rglob("SHA256SUMS*")):
            rel = m.relative_to(self.path)
            if any(p in NOT_WALKED for p in rel.parts) or not m.is_file():
                continue
            base = self.path if m.parent == self.path else m.parent
            for line in m.read_text().splitlines():
                if not line.strip():
                    continue
                h, n = line.split("  ", 1)
                f = base / n
                r = str(f.relative_to(self.path))
                if not f.is_file():
                    self.bad.append(f"{r}: missing (listed in {rel})")
                elif sha(f) != h:
                    self.bad.append(f"{r}: differs from {rel}")
                else:
                    self.verified[r] = h
            if m.name == "SHA256SUMS" and m.parent.parent == self.path:
                self.inst_manifest.add(m.parent.name)
        return self.bad

    def covered(self, rel):
        rel = str(rel)
        return rel in self.verified or any(fnmatch.fnmatch(rel, p) for p in UNMANIFESTED)

    def file(self, rel):
        rel = str(rel)
        if not self.covered(rel):
            refuse(f"{self.path}: {rel} is read but is under no verified manifest line and not on UNMANIFESTED")
        self.reads.add(rel)
        return self.path / rel

    def exists(self, rel):
        return (self.path / rel).is_file()

    def json(self, rel):
        if not self.exists(rel):
            return None
        return json.loads(self.file(rel).read_text())

    def bytes(self, rel):
        return self.file(rel).read_bytes() if self.exists(rel) else None


# ================================================================================================ 1. per root

def first_failing(status):
    for k in ORDER:
        st = status["steps"].get(k)
        if st and st["status"] != "done":
            return dict(step=k, status=st["status"], why=st.get("why"))
    return None


def max_rule(R, name, plan, group):
    import fit3
    import spec as specmod
    import stage_d
    spec_path = HERE / plan["groups"][group]["spec"]
    s = specmod.load(spec_path)
    with tempfile.TemporaryDirectory() as t:
        t = Path(t)
        for f in ("record.json", "overlay_d.json"):
            shutil.copyfile(R.file(f"{name}/D/{f}"), t / f)
        inv = None
        if s["front"]:
            (t / "inv").mkdir()
            shutil.copyfile(R.file(f"{name}/inv/inverter_gate.json"), t / "inv" / "inverter_gate.json")
            inv = str(t / "inv" / "inverter_gate.json")
        with fit3.rule("max"), contextlib.redirect_stdout(io.StringIO()):
            p = stage_d.predict(spec_path, t, inv)
    return dict(eligible_K0=p["eligible_K0"], room_K3=p["room_K3"])


def tag_of(plan, group):
    import spec as specmod
    return specmod.load(HERE / plan["groups"][group]["spec"])["tag"]


def home_instances(plan):
    """[(name, group, seed)] the plan names as home instances, in group then seed order."""
    return sorted(((f"{tag_of(plan, g)}_{s}", g, s) for g, gp in plan["groups"].items() for s in gp["seeds"]),
                  key=lambda x: (x[1], x[2]))


def check_folders(R, plan):
    """A3, B2, D8: every folder with a status.json is a home instance the plan names, under its own name."""
    want = {n: (g, s) for n, g, s in home_instances(plan)}
    bad = []
    for st in sorted(R.path.glob("*/status.json")):
        name = st.parent.name
        if name.startswith(("U_", "DUP_", "DUPX_")):
            continue
        s = json.loads(R.file(f"{name}/status.json").read_text())
        g, seed = s.get("group"), s.get("seed")
        if name not in want:
            bad.append(f"{name}: a folder the plan does not name")
        elif want[name] != (g, seed):
            bad.append(f"{name}: status.json says group {g} seed {seed}, the plan {want[name][0]} {want[name][1]}")
        elif g not in plan["groups"] or f"{tag_of(plan, g)}_{seed}" != name or s.get("tag", tag_of(plan, g)) != tag_of(plan, g):
            bad.append(f"{name}: not <TAG>_<seed> of its status.json")
    if bad:
        refuse(f"{R.path}: " + "; ".join(bad))


def verify_comparison(R, name, plan, group, seed, n, comp):
    """A6 and B4: the verdict is known; the comparison is recomputed with the pinned compare_d2 and must be
    byte-identical; its fields are checked. Returns the round's noisy_record status."""
    rel = f"{name}/N{n}/comparison.json"
    if comp["verdict"] not in VERDICTS:
        refuse(f"{R.path}: {rel}: unknown verdict {comp['verdict']!r}")
    rec = R.json(f"{name}/N{n}/noisy_record.json")
    if rec is None:
        refuse(f"{R.path}: {rel} exists without its round's noisy_record.json")
    import compare_d2
    kind = "noiseless" if n == 0 else "noisy"
    seal_dir = R.path / name / "seal"
    for f in seal_dir.iterdir():
        R.file(f"{name}/seal/{f.name}") if f.name != "SHA256SUMS" else None
    with contextlib.redirect_stdout(io.StringIO()):
        try:
            again = compare_d2.compare(seal_dir, HERE / plan["groups"][group]["spec"], R.file(f"{name}/N{n}/noisy_record.json"), kind)
        except (SystemExit, Exception) as e:
            refuse(f"{R.path}: {rel}: the recomputation with compare_d2 failed: {e!r}"[:400])
    if (json.dumps(again, indent=1, sort_keys=True) + "\n").encode() != R.bytes(rel):
        refuse(f"{R.path}: {rel} is not what the pinned compare_d2 computes from its seal and noisy_record.json")
    tag = tag_of(plan, group)
    bad = [k for k, v in (("tag", tag), ("seed", seed), ("run_kind", kind), ("noise_round", n),
                          ("noise_seed", rec.get("noise_seed")), ("stage_n_status", rec.get("status")))
           if comp.get(k) != v]
    if comp["verdict"] in ("agrees", "refuted") and not ((comp.get("compared") or {}).get("letters") or 0) > 0:
        bad.append("compared.letters")
    if bad:
        refuse(f"{R.path}: {rel}: fields differ from the record and the plan: {bad}")
    return rec.get("status")


def analyze_root(R, plan, machine, campaign):
    rounds = plan["rounds"]
    insts, observed_only, run_failed = [], [], []
    summ = R.json("RESULT_INSTANCES.json") if R.instances_done else None
    summ_steps = {f"{x['tag']}_{x['seed']}": x["steps"] for x in (summ or {}).get("instances", [])}
    for name, group, seed in home_instances(plan):
        base = dict(instance=name, group=group, seed=seed)
        if not (R.path / name / "status.json").exists():
            insts.append(dict(base, not_run=True, K0=dict(counted=False), K3=dict(counted=False),
                              why="no folder: never started" if (R.path / "PLAN_INPUT.json").exists() else "no root"))
            continue
        status = R.json(f"{name}/status.json")
        if name not in R.inst_manifest:
            row = dict(base, steps={k: v["status"] for k, v in sorted(status["steps"].items())}, stage_d=None,
                       unverified=True, K0=dict(counted=False), K3=dict(counted=False))
            run_failed.append(dict(instance=name, group=group, level="stage D", first_failing=dict(
                step=None, status="no verified instance manifest (the root did not finish this instance)")))
            insts.append(row)
            continue
        if summ is not None and summ_steps.get(name) != {k: v["status"] for k, v in status["steps"].items()}:
            refuse(f"{R.path}: {name}/status.json's steps differ from RESULT_INSTANCES.json's")
        seal_rel = f"{name}/seal/{name}.json"
        pred = R.json(seal_rel) if R.exists(seal_rel) else R.json(f"{name}/D/prediction.json")
        comps = {n: R.json(f"{name}/N{n}/comparison.json") for n in range(rounds + 1)}
        stopped = {}
        for n, c in comps.items():
            if c is not None:
                st = verify_comparison(R, name, plan, group, seed, n, c)
                if c["verdict"] == "run failed" and own_check(st):
                    stopped[n] = st
        row = dict(base, steps={k: v["status"] for k, v in sorted(status["steps"].items())})
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
            differences=c.get("differences"), why=c.get("why"),
            **({"stopped_by_own_check": True} if n in stopped else {})) for n, c in comps.items()}
        ref_ = lambda n: comps[n] is not None and (comps[n]["verdict"] == "refuted" or n in stopped)
        done_ = lambda n: comps[n] is not None and (comps[n]["verdict"] in ("agrees", "refuted") or n in stopped)
        if pred["eligible_K0"]:
            if done_(0):
                row["K0"] = dict(counted=True, refuted=ref_(0))
                if 0 in stopped and comps[0]["verdict"] != "refuted":
                    row["K0"]["stopped_by_own_check"] = True
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
        noisy = list(range(1, rounds + 1))
        if pred["room_K3"]:
            if any(ref_(n) for n in noisy):                         # one completed refuting round refutes
                row["K3"] = dict(counted=True, refuted=True)
                if not any(comps[n] is not None and comps[n]["verdict"] == "refuted" for n in noisy):
                    row["K3"]["stopped_by_own_check"] = True
            elif all(done_(n) for n in noisy):                      # held only if every round completed and agrees
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
        row["max_rule_comparison"] = max_rule(R, name, plan, group)
        row["cost"] = {k: dict(cpu_s=v.get("cpu_s"), wall_s=v.get("wall_s")) for k, v in sorted(status["steps"].items())}
        row["cost_total"] = dict(cpu_s=round(sum(v.get("cpu_s") or 0 for v in status["steps"].values()), 1))
        insts.append(row)
    controls = dict(U=[], duplicate=[], S=[])
    for p in sorted(R.path.glob("U_*/untrained.json")):
        u = R.json(str(p.relative_to(R.path)))
        controls["U"].append(dict(instance=u["instance"], holds=u.get("ok"), r_cell_fires=u.get("r_cell_fires"),
                                  inverter_fires_reported=len(u.get("inverter_fires_reported") or [])))
    for p in sorted(R.path.glob("DUP_*/duplicate.json")):
        x = R.json(str(p.relative_to(R.path)))
        controls["duplicate"].append(dict(instance=x["instance"], identical=x.get("ok"), checker=x.get("checker"),
                                          check_exit=x.get("check_duplicate_exit")))
    for r in insts:
        for k, c in sorted((r.get("comparisons") or {}).items()):
            if c and c.get("compared"):
                controls["S"].append(dict(instance=r["instance"], comparison=k, skew_slots=c["compared"]["skew_slots"],
                                          skew_differences=[d for d in c.get("differences") or [] if d["what"] == "skew"]))
    return rt(dict(observed_only=observed_only, run_failed=run_failed, controls=controls, instances=insts))


def env_section(R):
    root = R.path
    if not R.exists("ENV.json"):
        if R.finished:
            refuse(f"{root} has no ENV.json")
        return None
    env = R.json("ENV.json")
    h = sha(R.file("ENV.json"))
    bad = []
    resumes = R.json("ENV_RESUMES.json") or []
    bad += [f"resume at {r['uptime_s']}: static {r['static_sha256'][:12]}" for r in resumes if r["static_sha256"] != env["static_sha256"]]
    per = {}
    for st in sorted(root.glob("*/status.json")):
        name = st.parent.name
        s = R.json(f"{name}/status.json").get("env_sha256")
        pf = f"{name}/D/prediction.json"
        p = (R.json(pf) or {}).get("env_sha256") if R.exists(pf) and R.covered(pf) else "no prediction"
        per[name] = dict(status=s, prediction=p)
        if s != h:
            bad.append(f"{name}: status env {s}")
        if R.exists(pf) and R.covered(pf) and p != h:
            bad.append(f"{name}: prediction env {p}")
    if bad:
        refuse("mixed environments in one OUTROOT: " + "; ".join(bad))
    return dict(env_json_sha256=h, static_sha256=env["static_sha256"], static=env["static"],
                uptime_s=env["uptime_s"], resumes=[r["uptime_s"] for r in resumes], instances=per)
