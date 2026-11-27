"""The campaign analysis: one file, in place of analyze.py … analyze10.py (the owner's decision, relayed 2026-11-26).
It is analyze10 flattened, with the defect fixes listed below. Each former layer is a function, applied in order, with a
JSON round trip between them as before.

  analysis.py MODE OUTDIR ROOT [ROOT ...] [draw=DRAW.json] [rehearsal=1] [times=github|bare|lsremote:LOG]
                                          [thresholds=FILE] [controls=DIR] [tips=FILE]

MODE:
- **campaign:** every ROOT must come from campaign.py in campaign mode: its ENV.json names this tree's campaign.py by
  sha256, the frozen template (campaign.FROZEN_TEMPLATE_SHA256), and mode CAMPAIGN. Any other root is refused, and so
  is a mix. draw= is required, times must be github, thresholds the pinned file, controls the noise tree at the
  template's noise_commit.
- **test:** any root of this driver. RESULTS.json then says "mode": "TEST". draw= is optional: given, every check of
  the draw and of the expected plans runs as in campaign mode.
- **rehearsal=1:** the draw's sizes are DRAW_SIZES_REHEARSAL instead of DRAW_SIZES. RESULTS.json then carries
  "REHEARSAL" in its first field (NOTICE), in `mode` and in every verdict line: it can never be read as the campaign.

THE DRAW AND THE EXPECTED PLANS (D8, B5, B16):
- DRAW.json must be, byte for byte, draw_seeds.canon of draw_seeds.draw(beacon, round, the pinned EXCLUDED.json,
  DRAW_SIZES) with one key added, `beacon_round`: drand's /public/<round> (round, signature, randomness). The beacon
  value must be the round's randomness, and the round's BLS signature must verify (beacon_verify.verify) against the
  pinned quicknet chain (beacon_chain.QUICKNET). Any failure refuses.
- The expected plans are plan_split3.split(draw, the frozen template, MACHINES). Each root's PLAN_INPUT.json must be
  byte-identical to plan_split.canon of one of them, which names the root's machine K<nn>; its PLAN.json and
  PLAN_RESOLVED.json must be that plan plus PLAN_LOCAL_KEYS only, equal to TEMPLATE_CHECK.json's trees. Two roots on
  one machine refuse. Everything the analysis reads from a plan is then read from the expected plan.
- Every expected home instance is a row. One with no folder, and every instance of a machine with no root, is "not
  run" (counted for nothing); the rows of each group and level sum to the drawn size.

THE ROOTS (D9, D10, A3, A4, B2, B8, B9, B10):
- A repeated root path, two roots of one machine, and a (group, seed) home instance in more than one folder refuse.
- A folder with a status.json is a home instance (U_, DUP_ and DUPX_ never are). Its name must be <TAG>_<seed> of its
  status.json's group and seed, and its plan must name it; anything else refuses.
- Every line of every SHA256SUMS file of a root (each instance's, seal/, inv/, N<n>/extract/, each DUPX_'s,
  SHA256SUMS.instances and the root's; lean_build/ and kernel_build/ are not read and not walked) is verified against
  the file it names. A missing or differing file REFUSES the analysis and names the files. No manifest the driver
  writes lists a deleted raw trace: an instance's SHA256SUMS is written after the raws are dropped, and lists its
  *.json files only.
- Every file this script reads from a root is under a verified manifest line or on the named list UNMANIFESTED.
- A root without DONE or without its final SHA256SUMS is "not finished": it is named at the top of RESULTS.json, its
  instances with a verified instance manifest are analysed as usual, the others are "not completed". A machine of
  the expected plans with no root is named at the top too, and its instances are "not run". Neither refuses.
- OUTDIR must be new or empty, and outside every root. Every root's SHA256SUMS files are hashed before and after the
  analysis; a change refuses.

THE SEALS (A1, B1, B2, B3, B6, B7, B11):
- A seal is exactly seal/<TAG>_<seed>.json beside MANIFEST.json and SHA256SUMS, and seal.verify must hold. The seal
  log must hold exactly one line for the instance, with this seal's sha256, pushed (GitHub's recorded push time)
  before stage N started. In campaign mode an unreadable seal log or unreadable push times REFUSE the analysis (it is
  rerun later, never reinterpreted); times=lsremote is not accepted there. The activity items read for each seal
  branch are saved in OUTDIR/activity/.
- A seal defect makes an agreement count for nothing (not_sealed). A completed comparison that differs, or a run
  stopped by its own check, stays "refuted" with a defective seal, flagged seal_defect (the owner's rule A1(ii)).
- The regeneration child gets a minimal environment (REGEN_ENV).
- Campaign mode requires every sealed prediction to name stage_d6.py and the template's testError_rule.

THE COMPARISONS (A2, A6, B4):
- Each comparison.json is recomputed with the pinned compare_d2 from its sealed prediction and its round's
  noisy_record.json, and must be byte-identical; its tag, seed, run_kind, noise_round, noise_seed and stage_n_status
  are checked, and a completed comparison must compare letters. Any mismatch refuses. A verdict outside VERDICTS
  refuses.
- A run stopped by its own check (own_check below) counts as refuted, in its own row (the owner's rule A2).

THE LAYERS, in order (each as its file's docstring states):
1. per root (analyze, analyze2): the instances, K0/K3 counting, the observed-only list, run_failed, the controls, the
   max-rule comparison, and ENV (mixed environments refused);
2. over the roots (analyze3): the seal regeneration and the seal-log check (push before stage N), and the
   cross-machine duplicates' records;
3. analyze4: N<n>/SEAL_LOG.json against the log;
4. analyze5: the thresholds of thresholds.json;
5. analyze6: the records' own seal_log;
6. analyze7: the duplicates judged by the controls' tests/check_duplicate.py; the expected controls (A7);
7. analyze8: the proportional D4 rule (d4_regate.py), the planned audits against the present ones (A8);
8. analyze9: the counts side by side;
9. analyze10: the stage-D script named by the prediction, stage_d6 with its kernel field.

RESULTS.json is analyze10's, with these changes, all listed: the format (layered-campaign-analysis/2), analysis_sha256
in place of analyze*_sha256, `mode`, `NOTICE`, `draw`, `machines_detail`, `expected_controls`, `roots_sha256sums`,
`root_drivers` and `pins`; and the fixes above, together with the audit's A1–A6 of 2026-11-26:
- K3: an instance is refuted if ANY completed sealed comparison of a noisy round is "refuted"; held only if every
  round completed and agrees; not completed when no completed round refutes and a round is missing. The seal-log
  checks of a counted level read only its completed rounds.
- Eligibility and room are read from the SEALED prediction (seal/<inst>.json); an instance whose D/prediction.json
  differs from its seal is a seal defect.
- The thresholds are read once, before the first layer (there is no constant default).
- The not_sealed row lists each instance with its comparison verdicts.
- first_failing uses the one step order (ORDER, sealpush included).
- Campaign mode: FREEZE_PINS.json checked over this tree (campaign.pins_check) and the tree clean.
- It refuses to run with Python's -O (sys.flags.optimize): no check of this file is an assert.
"""
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


def verify_comparison(R, name, plan, group, seed, n, comp, seal_ok):
    """A6 and B4: the verdict is known; the comparison is recomputed with the pinned compare_d2 and must be
    byte-identical; its fields are checked. Returns the round's noisy_record status. When the seal folder itself is
    defective (B1, B2) nothing can be recomputed from it: the fields are checked, and the instance's agreements count
    for nothing (seal_defect, A1(ii))."""
    rel = f"{name}/N{n}/comparison.json"
    if comp["verdict"] not in VERDICTS:
        refuse(f"{R.path}: {rel}: unknown verdict {comp['verdict']!r}")
    rec = R.json(f"{name}/N{n}/noisy_record.json")
    if rec is None:
        refuse(f"{R.path}: {rel} exists without its round's noisy_record.json")
    import compare_d2
    kind = "noiseless" if n == 0 else "noisy"
    if seal_ok:
        R.file(f"{name}/seal/{name}.json")                  # what seal.load reads (compare_d2's prediction)
        with contextlib.redirect_stdout(io.StringIO()):
            try:
                again = compare_d2.compare(R.path / name / "seal", HERE / plan["groups"][group]["spec"],
                                           R.file(f"{name}/N{n}/noisy_record.json"), kind)
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
                step=None, status="no verified instance manifest (manifest not final: the root did not finish this instance)")))
            insts.append(row)
            continue
        if summ is not None and summ_steps.get(name) != {k: v["status"] for k, v in status["steps"].items()}:
            refuse(f"{R.path}: {name}/status.json's steps differ from RESULT_INSTANCES.json's")
        seal_ok, seal_why = seal_files(R, name)
        seal_rel = f"{name}/seal/{name}.json"
        pred = R.json(seal_rel) if R.exists(seal_rel) else R.json(f"{name}/D/prediction.json")
        comps = {n: R.json(f"{name}/N{n}/comparison.json") for n in range(rounds + 1)}
        stopped = {}
        for n, c in comps.items():
            if c is not None:
                st = verify_comparison(R, name, plan, group, seed, n, c, seal_ok is not None)
                if c["verdict"] == "run failed" and own_check(st):
                    stopped[n] = st
        row = dict(base, steps={k: v["status"] for k, v in sorted(status["steps"].items())},
                   seal_folder=dict(file=seal_ok, why=seal_why))
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
        if not R.covered(str(p.relative_to(R.path))):       # a root that did not finish: never read, never counted
            controls["U"].append(dict(instance=p.parent.name[2:], holds=None, unverified=True,
                                      why="under no verified manifest (the root did not finish)"))
            continue
        u = R.json(str(p.relative_to(R.path)))
        controls["U"].append(dict(instance=u["instance"], holds=u.get("ok"), r_cell_fires=u.get("r_cell_fires"),
                                  inverter_fires_reported=len(u.get("inverter_fires_reported") or [])))
    for p in sorted(R.path.glob("DUP_*/duplicate.json")):
        if not R.covered(str(p.relative_to(R.path))):
            continue
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


# ================================================================================================ 2. seals (analyze3, analyze10)

def seal_files(R, name):
    """B2 and B1: the seal is exactly seal/<name>.json beside MANIFEST.json and SHA256SUMS, and seal.verify holds.
    Returns (rel path of the sealed prediction or None, why or None)."""
    import seal as sealmod
    d = R.path / name / "seal"
    if not d.is_dir():
        return None, "no seal folder"
    names = sorted(p.name for p in d.iterdir())
    if names != sorted(["MANIFEST.json", "SHA256SUMS", f"{name}.json"]):
        return None, f"the seal folder holds {names}, not exactly MANIFEST.json, SHA256SUMS and {name}.json"
    with contextlib.redirect_stdout(io.StringIO()):
        ok = sealmod.verify(d, quiet=True)
    if not ok:
        return None, "seal.verify fails on the seal folder"
    for f in ("MANIFEST.json", f"{name}.json"):
        R.file(f"{name}/seal/{f}")
    return f"{name}/seal/{name}.json", None


def regenerate(R, name, plan, status, kernel_build, seal_rel):
    d = R.path / name
    p10 = json.loads(R.bytes(seal_rel))                        # analyze10's check comes first
    names6, kernel = "stage_d6.py" in p10.get("code", {}), "kernel" in p10
    if names6 and not kernel:
        return False, "the sealed prediction names stage_d6.py but has no kernel field"
    if kernel and not names6:
        return False, "the sealed prediction has a kernel field but does not name stage_d6.py"
    if not R.exists(f"{name}/D/record.json"):
        return False, "no stage-D record"
    sealed = R.bytes(seal_rel)
    pred = json.loads(sealed)
    script = next((s for s in SCRIPTS if s in pred.get("code", {})), None)
    if script is None:
        return False, "the sealed prediction names no stage-D script"
    spec = HERE / plan["groups"][status["group"]]["spec"]
    with tempfile.TemporaryDirectory() as t:
        t = Path(t)
        for f in ("record.json", "overlay_d.json"):
            shutil.copyfile(R.file(f"{name}/D/{f}"), t / f)
        args = [PY, "-B", str(HERE / script), "predict", str(spec), str(t), f"rule={pred.get('testError_rule', 'one-port')}"]
        if (d / "inv" / "inverter_gate.json").exists():
            (t / "inv").mkdir()
            shutil.copyfile(R.file(f"{name}/inv/inverter_gate.json"), t / "inv" / "inverter_gate.json")
            args.append(f"inverters={t / 'inv' / 'inverter_gate.json'}")
        env = {k: os.environ[k] for k in REGEN_ENV if k in os.environ}       # B11: a minimal environment
        env["LAYERED_KERNEL_BUILD"] = str(kernel_build)
        if status.get("env_sha256"):
            env["LAYERED_ENV_SHA256"] = status["env_sha256"]
        r = subprocess.run(args, cwd=HERE, capture_output=True, text=True, env=env)
        if r.returncode or not (t / "prediction.json").exists():
            return False, "regeneration failed: " + r.stderr.strip().replace(str(t), "<scratch>")[-300:]
        again = (t / "prediction.json").read_bytes()
    if again != sealed:
        a, b = json.loads(again), pred
        keys = sorted(k for k in set(a) | set(b) if a.get(k) != b.get(k))
        return False, f"regenerated prediction differs from the seal in {keys}"
    return True, None


def safe(branch):
    return str(branch).replace("/", "__")


def push_times(remote, branch, src, outdir):
    """B7: GitHub's recorded push times (every activity item saved in OUTDIR/activity/), or the local bare log in
    test mode."""
    if src == "github":
        owner_repo = str(remote).rstrip("/").removesuffix(".git").split("github.com/")[-1]
        r = subprocess.run(["gh", "api", "-X", "GET", f"repos/{owner_repo}/activity", "-f", f"ref=refs/heads/{branch}",
                            "-f", "per_page=100", "--paginate"], capture_output=True, text=True, check=True)
        items = SP.activity_pages(r.stdout)
        a = Path(outdir) / "activity"
        a.mkdir(exist_ok=True)
        (a / f"{safe(branch)}.json").write_bytes(canon(dict(repository=owner_repo, ref=f"refs/heads/{branch}", items=items)))
        return SP.github_times(items)
    return SP.times(remote, branch, src)


def seal_log(R, name, plan, status, logs, times_src, campaign, outdir):
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
                tm = push_times(sp_["remote"], sp_["branch"], times_src, outdir)
                logs[key] = (lines, tm, None)
            except Exception as e:
                if campaign:                              # A1(i): never reinterpreted; rerun the analysis later
                    refuse(f"campaign mode: the seal log or its push times cannot be read ({sp_['branch']}): {e!r}"[:500])
                logs[key] = ([], {}, repr(e))
    lines, tm, err = logs[key]
    if err:
        return False, dict(why=f"the seal log cannot be read: {err}")
    want = sha(R.path / name / "seal" / "SHA256SUMS")
    mine = [x for x in lines if x["instance"] == name]
    if len(mine) != 1:                                    # B3: exactly one line per instance
        return False, dict(why=f"{len(mine)} lines for this instance in the seal log, not exactly one",
                           logged=[x["seal_sha256"] for x in mine])
    x = mine[0]
    if x["seal_sha256"] != want:
        return False, dict(why="the logged seal sha256 is not this seal's", logged=[x["seal_sha256"]])
    pushed = tm.get(x["commit"])
    if pushed is None:
        if campaign:
            refuse(f"campaign mode: no recorded push time for {x['commit']} ({sp_['branch']}, {name})")
        return False, dict(why="no recorded push time for the commit that logged the seal", commit=x["commit"])
    n0 = status["steps"].get("N0", {}).get("started")
    if n0 is None:
        return True, dict(pushed_utc=pushed, stage_n_start=None, note="no stage N started", commit=x["commit"])
    margin = (parse_utc(n0) - parse_utc(pushed)).total_seconds()
    detail = dict(pushed_utc=pushed, stage_n_start=n0, margin_s=round(margin, 3), commit=x["commit"])
    if margin <= 0:
        return False, dict(detail, why="the seal was pushed after stage N started")
    return True, detail


def same_n0(Ra, a, Rb, b):
    out = {}
    for f in ("noisy_record.json", "trace.digest.json"):
        if Ra.exists(f"{a}/{f}") and Rb.exists(f"{b}/{f}"):
            out[f] = strip(Ra.json(f"{a}/{f}")) == strip(Rb.json(f"{b}/{f}"))
        else:
            out[f] = None
    if Ra.exists(f"{a}/input.spice") and Rb.exists(f"{b}/input.spice"):
        out["input.spice"] = Ra.bytes(f"{a}/input.spice") == Rb.bytes(f"{b}/input.spice")
    return out


def seal_defect(r, level):
    """A1(ii), the owner's rule: a seal defect makes an agreement count for nothing; a completed refutation (a
    differing comparison, or a run stopped by its own check) stays refuted, flagged."""
    x = r.get(level) or {}
    if x.get("counted") and x.get("refuted"):
        r[level] = dict(x, seal_defect=True)
    elif x.get("counted"):
        r[level] = dict(counted=False, not_sealed=True)


def layer_seals(M, times_src, kernel_build, th, campaign, rule, outdir):
    rows, observed, failed, controls, envs, defects = [], [], [], dict(U=[], duplicate=[], S=[], cross_machine_duplicates=[]), {}, []
    logs, by_inst = {}, {}
    for machine, m in M.items():
        R, plan = m["R"], m["plan"]
        if R is None:                                    # D8: a machine of the expected plans with no root
            for name, group, seed in home_instances(plan):
                rows.append(dict(instance=name, group=group, seed=seed, machine=machine, not_run=True,
                                 why="no root for this machine", K0=dict(counted=False), K3=dict(counted=False)))
            continue
        envs[machine] = env_section(R)
        res = analyze_root(R, plan, machine, campaign)
        for r in res["instances"]:
            r["machine"] = machine
            if r.get("stage_d") is not None:
                status = R.json(f"{r['instance']}/status.json")
                seal_rel, why0 = r["seal_folder"]["file"], r["seal_folder"]["why"]
                if seal_rel is None:
                    ok1, why1 = False, why0
                else:
                    ok1, why1 = regenerate(R, r["instance"], plan, status, kernel_build, seal_rel)
                    dp = f"{r['instance']}/D/prediction.json"
                    if ok1 and (not R.exists(dp) or R.bytes(dp) != R.bytes(seal_rel)):
                        ok1, why1 = False, "D/prediction.json differs from its seal (the sealed prediction is the one read)"
                    if campaign:                              # B6
                        p = json.loads(R.bytes(seal_rel))
                        if "stage_d6.py" not in p.get("code", {}) or p.get("testError_rule") != rule:
                            refuse(f"campaign mode: {machine} {r['instance']}: the sealed prediction does not name "
                                   f"stage_d6.py with the template's testError_rule {rule!r}")
                if seal_rel is None:
                    ok2, det2 = False, dict(why="no valid seal")
                else:
                    ok2, det2 = seal_log(R, r["instance"], plan, status, logs, times_src, campaign, outdir)
                r["seal"] = dict(regenerated_identical=ok1, regeneration_why=why1, log_ok=ok2, log=det2)
                if not (ok1 and ok2):
                    defects.append(dict(machine=machine, instance=r["instance"], regenerated=why1 or "identical",
                                        log=det2.get("why") or "ok"))
                    for level in ("K0", "K3"):
                        seal_defect(r, level)
            rows.append(r)
            if not r.get("not_run"):
                by_inst[r["instance"]] = (machine, r)
        observed += [dict(o, machine=machine) for o in res["observed_only"]]
        failed += [dict(f, machine=machine) for f in res["run_failed"]]
        for c in ("U", "duplicate", "S"):
            controls[c] += [dict(x, machine=machine) for x in res["controls"][c]]
    for machine, m in M.items():
        if m["R"] is None:
            continue
        for dx in sorted(m["R"].path.glob("DUPX_*")):
            name = dx.name[len("DUPX_"):]
            entry = dict(instance=name, duplicate_machine=machine)
            if name not in by_inst:
                entry["why"] = "original instance not in the analysed OUTROOTs"
            elif by_inst[name][1].get("unverified") or f"{dx.name}/N0/noisy_record.json" not in m["R"].verified:
                entry["why"] = "the original or the duplicate is under no verified manifest"
            else:
                om = by_inst[name][0]
                entry.update(original_machine=om, **{f"{k_}_identical": v for k_, v in
                                                     same_n0(M[om]["R"], f"{name}/N0", m["R"], f"{dx.name}/N0").items()})
            controls["cross_machine_duplicates"].append(entry)
    groups = {}
    allgroups = sorted({g for m in M.values() for g in m["plan"]["groups"]})
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
        src_desc = dict(source={"github": "GitHub repository activity API (push timestamps; push and branch_creation "
                                          "items only; every item saved in activity/)",
                                "bare": "local bare repository post-receive log"}.get(times_src, times_src))
    return rt(dict(times_source=src_desc, machines=len(M),
                   env={m: (None if e is None else dict(static_sha256=e["static_sha256"], env_json_sha256=e["env_json_sha256"]))
                        for m, e in envs.items()},
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
    """The rounds of a counted level whose comparison completed (a run stopped by its own check included): N0 at K0;
    at K3 the completed noisy rounds (all three for a held instance, at least the refuting one for a refuted one)."""
    if level == "K0":
        return [0]
    comps = r.get("comparisons") or {}
    return [n for n in (1, 2, 3) if (comps.get(f"C{n}") or {}).get("verdict") in ("agrees", "refuted")
            or (comps.get(f"C{n}") or {}).get("stopped_by_own_check")]


def layer_stage_n_seal_log(res, M, th):
    for r in res["instances"]:
        if r.get("not_run"):
            continue
        R = M[r["machine"]]["R"]
        commit = ((r.get("seal") or {}).get("log") or {}).get("commit")
        for level in ("K0", "K3"):
            if not (r.get(level) or {}).get("counted"):
                continue
            bad = []
            for n in completed_rounds(r, level):
                f = f"{r['instance']}/N{n}/SEAL_LOG.json"
                got = (R.json(f) or {}).get("commit") if R.exists(f) else None
                if got is None or got != commit:
                    bad.append(f"N{n}: SEAL_LOG.json {'missing' if got is None else got[:12]} vs log {str(commit)[:12]}")
            if bad:
                seal_defect(r, level)
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


def layer_record_seal_log(res, M):
    for r in res["instances"]:
        if r.get("not_run"):
            continue
        R, plan = M[r["machine"]]["R"], M[r["machine"]]["plan"]
        branch = (plan.get("seal_push") or {}).get("branch")
        commit = ((r.get("seal") or {}).get("log") or {}).get("commit")
        for level in ("K0", "K3"):
            if not (r.get(level) or {}).get("counted"):
                continue
            bad = []
            for n in completed_rounds(r, level):
                f = f"{r['instance']}/N{n}/noisy_record.json"
                sl = (R.json(f) or {}).get("seal_log") if R.exists(f) else None
                if not sl or sl.get("commit") != commit or sl.get("branch") != branch:
                    bad.append(f"N{n}: record seal_log {sl} vs log {str(commit)[:12]} on {branch}")
            if bad:
                seal_defect(r, level)
                res["seal_defects"].append(dict(machine=r["machine"], instance=r["instance"], record_seal_log=bad))
    th = res["thresholds"]
    regroup(res, lambda g, level: th[level][g])
    useal = []
    for machine, m in M.items():
        if m["R"] is None:
            continue
        for f in sorted(m["R"].path.glob("U_*/U/untrained_record.json")):
            rel = str(f.relative_to(m["R"].path))
            useal.append(dict(machine=machine, instance=f.parent.parent.name[2:], seal_log=m["R"].json(rel).get("seal_log")))
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


def layer_duplicates(res, M, controls_dir):
    where = {r["instance"]: r["machine"] for r in res["instances"] if not r.get("not_run") and not r.get("unverified")}
    xs = []
    for machine, m in M.items():
        if m["R"] is None:
            continue
        R = m["R"]
        for dx in sorted(R.path.glob("DUPX_*")):
            name = dx.name[len("DUPX_"):]
            e = dict(instance=name, duplicate_machine=machine)
            if name not in where:
                e["why"] = "original instance not in the analysed OUTROOTs"
                xs.append(e)
                continue
            if f"{dx.name}/N0/noisy_record.json" not in R.verified:   # its SHA256SUMS is written last: not finished
                e.update(identical=None, unverified=True, why="the duplicate's files are under no verified manifest")
                xs.append(e)
                continue
            om = where[name]
            OR = M[om]["R"]
            e["original_machine"] = om
            ctl = Path(controls_dir) if controls_dir else \
                Path(OR.json("PLAN.json")["noise_tree"]) / "research" / "layered-networks"
            cp = ctl / "tests" / "check_duplicate.py"
            e["checker"] = dict(file="tests/check_duplicate.py", sha256=sha(cp) if cp.exists() else None)
            for d_, R_ in ((OR.path / name / "N0", OR), (dx / "N0", R)):     # what check_duplicate reads (B8)
                for f in sorted(d_.iterdir()) if d_.is_dir() else []:
                    if f.is_file() and f.name in ("noisy_record.json", "trace.digest.json", "trace.raw", "input.spice"):
                        R_.file(str(f.relative_to(R_.path)))
            if cp.exists():
                ident, lines = judge(load_checker(cp), OR.path / name / "N0", dx / "N0")
                e.update(identical=ident, checker_lines=lines)
            else:
                e.update(identical=None, why="check_duplicate.py not found")
            sc = R.json(f"{dx.name}/seal_check.json")
            if sc is not None:
                sc.pop("seal_dir", None)
                e["seal_check"] = sc
            sf = R.json(f"{dx.name}/seal_fetch.json")
            if sf is not None:
                sf.pop("remote", None)
                e["seal_fetch"] = sf
            cd = R.json(f"{dx.name}/N0/comparison.json")
            if cd is not None:
                co = OR.json(f"{name}/N0/comparison.json")
                e["comparison"] = dict(verdict=cd.get("verdict"), equals_original=co is not None and strip(cd) == strip(co))
            else:
                e["comparison"] = None
            xs.append(e)
    res["controls"]["cross_machine_duplicates_v3"] = res["controls"].pop("cross_machine_duplicates", [])
    res["controls"]["cross_machine_duplicates"] = xs
    # A7: the expected controls against the present ones
    exp_u, exp_d = [], []
    for machine, m in M.items():
        plan = m["plan"]
        for g in sorted(plan.get("U_groups") or []):
            u = [x for x in res["controls"]["U"] if x["machine"] == machine and
                 any(r["instance"] == x["instance"] and r["group"] == g for r in res["instances"])]
            exp_u.append(dict(machine=machine, group=g, present=bool(u), instance=u[0]["instance"] if u else None,
                              passed=u[0]["holds"] if u else None,
                              why=None if u else ("no root" if m["R"] is None else "not run (no U folder: no eligible "
                                                  "instance of the group, or the run stopped)")))
        for x in plan.get("remote_duplicates") or []:
            d = [e for e in xs if e["duplicate_machine"] == machine and e["instance"] == x["home_instance"]]
            exp_d.append(dict(machine=machine, instance=x["home_instance"], home_machine=x["home_machine"],
                              present=bool(d), passed=d[0].get("identical") if d else None,
                              why=None if d else ("no root" if m["R"] is None else "not run (no DUPX folder)")))
    summ = lambda xs_: dict(expected=len(xs_), present=sum(1 for x in xs_ if x["present"]),
                            passed=sum(1 for x in xs_ if x["passed"] is True),
                            failed=sum(1 for x in xs_ if x["present"] and x["passed"] is False),
                            not_judged=sum(1 for x in xs_ if x["present"] and x["passed"] is None))
    res["expected_controls"] = dict(U=exp_u, remote_duplicates=exp_d,
                                    summary=dict(U=summ(exp_u), remote_duplicates=summ(exp_d)))
    # D8 without a draw: a home instance a plan names (as a duplicate's home) that no analysed root holds
    names = {r["instance"] for r in res["instances"]}
    res["home_instances_without_root"] = sorted(
        (dict(instance=x["home_instance"], home_machine=x["home_machine"],
              status="not run (its home root is not among the roots; counted for nothing)")
         for m in M.values() for x in m["plan"].get("remote_duplicates") or [] if x["home_instance"] not in names),
        key=lambda x: (x["home_machine"], x["instance"]))
    return rt(res)


# ================================================================================================ 7. D4 (analyze8)

def is_audited(R, name):
    f = f"{name}/D/fit_d.json"
    if not R.exists(f):
        return False
    cells = R.json(f).get("cells", [])
    return any(((c.get("budgets") or {}).get("K0") or {}).get("D4_source") == SOLO for c in cells)


def layer_d4(res, M):
    live = lambda r: not r.get("not_run") and not r.get("unverified")
    inst_dir = lambda r: M[r["machine"]]["R"].path / r["instance"]
    spec_of = lambda r: HERE / M[r["machine"]]["plan"]["groups"][r["group"]]["spec"]
    rows, frozen = res["instances"], D4.FROZEN
    groups, flags = {}, {}
    for g in sorted({r["group"] for r in rows}):
        rs = sorted((r for r in rows if r["group"] == g and live(r)), key=lambda r: (r["machine"], r["instance"]))
        aud = [r for r in rs if is_audited(M[r["machine"]]["R"], r["instance"])]
        planned = sorted((m_, f"{tag_of(m['plan'], g)}_{s}") for m_, m in M.items() if g in m["plan"]["groups"]
                         for s in m["plan"]["groups"][g].get("d4_audit") or [])
        present = sorted((r["machine"], r["instance"]) for r in aud)
        ls = []
        for r in aud:
            R = M[r["machine"]]["R"]
            for f in sorted((inst_dir(r) / "D").glob("*.json")):
                R.file(str(f.relative_to(R.path)))
            for c, by_g in sorted(D4.audited_lines(inst_dir(r) / "D").items()):
                for grp, v in sorted(by_g.items()):
                    ls.append(dict(machine=r["machine"], instance=r["instance"], cell=c, group=grp, value=str(v),
                                   value_float=float(v), above_frozen=v > frozen))
        star = max((F(x["value"]) for x in ls), default=None)
        sec = dict(planned=[list(x) for x in planned], audited=[r["instance"] for r in aud],
                   planned_not_audited=[list(x) for x in planned if x not in present],
                   audited_not_planned=[list(x) for x in present if x not in planned],
                   note=None if aud else "no D4 audit in this group",
                   lines=ls, frozen_d4_stage=str(frozen),
                   D4_star=None if star is None else str(star), D4_star_float=None if star is None else float(star),
                   exceeds=bool(star is not None and star > frozen), regated=[], premise_flagged_D4=dict(K0=[], K3=[]))
        if sec["exceeds"]:
            for r in rs:
                if r in aud or r.get("stage_d") is None:
                    continue
                reg = D4.regate(spec_of(r), inst_dir(r), star)
                if not reg["reproduces_sealed"]:                  # A8
                    refuse(f"{r['machine']} {r['instance']}: the D4 regate at the frozen value does not reproduce the "
                           f"sealed gate ({reg['sealed']})")
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


def layer_counts(res, sizes):
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
                if r.get("not_run"):
                    row["not_run"].append(dict(instance=name, machine=r["machine"], why=r.get("why")))
                elif x.get("counted") and x.get("refuted") and x.get("stopped_by_own_check"):
                    row["refuted_stopped_by_own_check"].append(name)
                elif x.get("counted") and x.get("refuted"):
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
            if sum(n.values()) != len(rs):
                refuse(f"the counts of {g} {lv} do not sum to its instances: {n} vs {len(rs)}")
            if sizes is not None and len(rs) != sizes[g]:
                refuse(f"{g} has {len(rs)} instances in the analysis, not the drawn size {sizes[g]}")
            out[g][lv] = dict(instances=len(rs), counted=n["held"] + n["refuted"] + n["refuted_stopped_by_own_check"],
                              **{k: dict(n=n[k], list=row[k]) for k in ROWS})
    res["counts"] = out
    for g, v in res["counts"].items():
        for lv in ("K0", "K3"):
            if v[lv]["counted"] != res["groups"][g][lv]["counted"]:
                refuse(f"the counts of {g} {lv} differ from the verdict's: {v[lv]['counted']} vs "
                       f"{res['groups'][g][lv]['counted']}")
    return rt(res)


# ================================================================================================ the checks around it

def root_driver(root):
    """(driver sha256, template sha256, mode) a root records, or Nones for a root of the old chain."""
    env = json.loads((Path(root) / "ENV.json").read_text()) if (Path(root) / "ENV.json").exists() else {}
    c = env.get("campaign") or {}
    return dict(driver_sha256=c.get("driver_sha256"), template_sha256=c.get("template_sha256"), mode=c.get("mode"))


def root_pins(root):
    """The FREEZE_PINS.json sha256 a root's driver checked (TEMPLATE_CHECK.json pins.pins_sha256), or None."""
    f = Path(root) / "TEMPLATE_CHECK.json"
    return (json.loads(f.read_text()).get("pins") or {}).get("pins_sha256") if f.exists() else None


def sums_of(roots):
    out = {}
    for k, root in enumerate(roots, start=1):
        files = sorted(p for p in Path(root).rglob("SHA256SUMS*")
                       if not any(x in NOT_WALKED for x in p.relative_to(root).parts))
        out[f"root_{k}"] = hashlib.sha256("".join(f"{sha(p)}  {p.relative_to(root)}\n" for p in files).encode()).hexdigest()
    return out


def kernel_library(outdir):
    r = E3.lean_resolution()                               # the real toolchain binary, not elan's proxy
    if r.get("sha256") != E3.LEAN_SHA256:
        refuse(f"the lean binary is not the pinned one ({E3.LEAN_SHA256[:12]}): {r.get('sha256')}")
    have = {f"{m}.lean": sha(CP.LEAN_DIR / f"{m}.lean") for m in CP.KERNEL_MODULES}
    if have != CP.KERNEL_SOURCES:
        refuse("the kernel's Lean sources differ from the pinned ones")
    return CP.build_kernel(outdir)


def check_draw(path, sizes, campaign):
    """B16 and D8: DRAW.json recomputed from its own beacon and round, the pinned EXCLUDED.json and the pinned sizes;
    the beacon round's signature verified against the pinned chain."""
    import beacon_chain
    import beacon_verify
    import draw_seeds
    b = Path(path).read_bytes()
    try:
        d = json.loads(b)
    except ValueError as e:
        refuse(f"DRAW.json is not JSON: {e}")
    if not campaign and DRAW_EXTRA_KEY not in d:       # a test draw (no beacon): the plans are checked, not the draw
        if not isinstance(d.get("groups"), dict):
            refuse("DRAW.json has no groups")
        return d, dict(sha256=hashlib.sha256(b).hexdigest(), sizes={g: len(v) for g, v in d["groups"].items()},
                       machines=MACHINES, signature_verified=False,
                       note="test mode, a draw with no beacon_round: not recomputed, no signature; its own sizes")
    br = d.get(DRAW_EXTRA_KEY)
    if not isinstance(br, dict) or set(br) != {"round", "signature", "randomness"}:
        refuse(f"DRAW.json has no {DRAW_EXTRA_KEY} {{round, signature, randomness}}")
    if not isinstance(d.get("beacon"), str) or not isinstance(d.get("round"), int):
        refuse("DRAW.json has no beacon string and round integer")
    ex = json.loads((HERE / "EXCLUDED.json").read_text())
    with contextlib.redirect_stdout(io.StringIO()):
        try:
            again = draw_seeds.draw(d["beacon"], d["round"], ex, dict(sizes))
        except AssertionError as e:
            refuse(f"the draw cannot be recomputed: {e}")
    want = draw_seeds.canon(dict(again, **{DRAW_EXTRA_KEY: br}))
    if b != want:
        refuse("DRAW.json is not draw_seeds.draw of its beacon and round on the pinned EXCLUDED.json at the pinned "
               f"sizes {sizes} (with its {DRAW_EXTRA_KEY} added), byte for byte")
    if br["round"] != d["round"] or br["randomness"].lower() != d["beacon"].lower():
        refuse(f"DRAW.json: the beacon is not the randomness of round {d['round']}")
    if not beacon_chain.check():
        refuse("the pinned quicknet chain does not check")
    v = beacon_verify.verify(beacon_chain.QUICKNET, br)
    if not v.get("ok"):
        refuse(f"DRAW.json: the beacon round does not verify against the pinned quicknet key: {v}")
    return d, dict(sha256=hashlib.sha256(b).hexdigest(), beacon=d["beacon"], round=d["round"], sizes=dict(sizes),
                   machines=MACHINES, excluded_sha256=d["excluded_sha256"], signature_verified=True)


def expected_plans(draw):
    import plan_split3
    t = json.loads(CP.FROZEN_TEMPLATE.read_text())
    plans, _ = plan_split3.split(draw, t, MACHINES)
    return {f"K{k:02d}": p for k, p in enumerate(plans, start=1)}, t


def match_plan(R, expected, campaign):
    """D8, B5: the root's PLAN_INPUT.json is byte for byte one expected plan; PLAN.json and PLAN_RESOLVED.json are
    that plan plus PLAN_LOCAL_KEYS, equal to TEMPLATE_CHECK.json's trees. In test mode only PLAN.json is matched: it
    must be one expected plan, PLAN_LOCAL_KEYS aside."""
    import plan_split
    if not campaign:
        plan = R.json("PLAN.json")
        hit = [k for k, p in expected.items() if plan is not None and
               {x: plan[x] for x in plan if x not in PLAN_LOCAL_KEYS} == rt(p)]
        if len(hit) != 1:
            refuse(f"{R.path}: PLAN.json is none of the expected plans of the draw")
        return hit[0]
    b = R.bytes("PLAN_INPUT.json")
    if b is None:
        refuse(f"{R.path}: no PLAN_INPUT.json")
    hit = [k for k, p in expected.items() if plan_split.canon(p) == b]
    if len(hit) != 1:
        refuse(f"{R.path}: PLAN_INPUT.json is none of the expected plans of the draw")
    k = hit[0]
    plan = R.json("PLAN.json")
    if plan is None or R.bytes("PLAN_RESOLVED.json") != R.bytes("PLAN.json"):
        refuse(f"{R.path}: PLAN.json missing, or PLAN_RESOLVED.json differs from it")
    if {x: plan[x] for x in plan if x not in PLAN_LOCAL_KEYS} != rt(expected[k]) or set(PLAN_LOCAL_KEYS) - set(plan):
        refuse(f"{R.path}: PLAN.json is not the expected plan {k} plus {PLAN_LOCAL_KEYS}")
    tc = R.json("TEMPLATE_CHECK.json") or {}
    trees = tc.get("trees") or {}
    if {x: str(plan[x]) for x in PLAN_LOCAL_KEYS} != {x: str(trees.get(x)) for x in PLAN_LOCAL_KEYS}:
        refuse(f"{R.path}: PLAN.json's {PLAN_LOCAL_KEYS} differ from TEMPLATE_CHECK.json's trees")
    return k


def main(mode, outdir, *args):
    if sys.flags.optimize:                                 # A5
        refuse("Python runs with -O (sys.flags.optimize): run analysis.py without it")
    if mode not in ("campaign", "test"):
        refuse(f"mode {mode!r} is neither campaign nor test")
    campaign = mode == "campaign"
    args = [str(a) for a in args]
    kw = {}
    for a in args:                                          # A4
        if "=" in a:
            k, v = a.split("=", 1)
            if k not in KEYS:
                refuse(f"unknown argument {a!r} (keys: {', '.join(KEYS)}; a root path cannot contain '=')")
            if k in kw:
                refuse(f"argument {k} given twice")
            kw[k] = v
    roots = [Path(a).resolve() for a in args if "=" not in a]
    if not roots:
        refuse("no root")
    if len(set(roots)) != len(roots):                       # D9
        refuse(f"a root is given more than once: {sorted(str(r) for r in roots if roots.count(r) > 1)}")
    for r in roots:
        if not r.is_dir():
            refuse(f"{r} is not a folder")
    out = Path(outdir).resolve()
    for r in roots:
        if out == r or r in out.parents:
            refuse(f"OUTDIR {out} lies inside the root {r}")
    if out.exists() and (not out.is_dir() or any(out.iterdir())):     # B10
        refuse(f"OUTDIR {out} exists and is not an empty folder")
    rehearsal = kw.get("rehearsal")
    if rehearsal not in (None, "1"):
        refuse(f"rehearsal={rehearsal!r}: only rehearsal=1")
    sizes = DRAW_SIZES_REHEARSAL if rehearsal == "1" else DRAW_SIZES
    drivers = {f"root_{k}": root_driver(r) for k, r in enumerate(roots, start=1)}
    times = kw.get("times", "github")
    tf = Path(kw.get("thresholds", str(HERE / "thresholds.json"))).resolve()
    controls = kw.get("controls")
    pc = CP.pins_check()
    if campaign:
        if CP.pins_refusal(pc):
            refuse("campaign mode: " + CP.pins_refusal(pc))
        pinned = {p: h for fs in json.loads(CP.PINS.read_text())["groups"].values() for p, h in fs.items()}
        if tf != (HERE / "thresholds.json").resolve() or pinned.get("research/layered-networks/thresholds.json") != sha(tf):
            refuse("campaign mode reads the pinned thresholds.json only")
        if times != "github":                                          # B7
            refuse(f"campaign mode: times must be github, not {times!r}")
        noise_commit = json.loads(CP.FROZEN_TEMPLATE.read_text())["noise_commit"]
        trees = [p for p, h in CP.worktrees() if h == noise_commit and CP.git_head(p)[1]]
        if not trees:
            refuse(f"campaign mode: no clean worktree at the template's noise_commit {noise_commit[:12]}")
        want = (Path(trees[0]) / "research" / "layered-networks").resolve()
        if controls is not None and Path(controls).resolve() != want:
            refuse(f"campaign mode: controls must be the noise tree at {noise_commit[:12]} ({want})")
        controls = str(want)
        bad = [m for m, d in drivers.items() if d != dict(driver_sha256=sha(HERE / "campaign.py"),
                                                          template_sha256=CP.FROZEN_TEMPLATE_SHA256, mode="CAMPAIGN")]
        if bad:
            refuse(f"roots not run by this campaign.py on the frozen template in campaign mode: {bad}")
        bad = [f"root_{k}" for k, r in enumerate(roots, start=1) if root_pins(r) != pc["pins_sha256"]]
        if bad:
            refuse(f"roots whose driver checked another FREEZE_PINS.json than this tree's ({pc['pins_sha256'][:12]}): {bad}")
        if "draw" not in kw:
            refuse("campaign mode: draw=DRAW.json is required")
    elif rehearsal == "1" and "draw" not in kw:
        refuse("rehearsal=1 needs draw=")
    th = json.loads(tf.read_text())
    tips = None
    if "tips" in kw:
        tips = dict(file=Path(kw["tips"]).name, sha256=sha(kw["tips"]), tips=json.loads(Path(kw["tips"]).read_text()))
    # D10: every manifest line of every root, before anything is read
    Rs = [Root(r) for r in roots]
    bad = {str(R.path): R.walk() for R in Rs}
    bad = {k: v for k, v in bad.items() if v}
    if bad:
        refuse("files that differ from their manifests, or are missing: " + json.dumps(bad)[:4000])
    # D8, D9: the machines
    draw_info, notice, template_rule = None, [], None
    M = {}
    if "draw" in kw:
        draw, draw_info = check_draw(kw["draw"], sizes, campaign)
        sizes = draw_info["sizes"]
        if not draw_info["signature_verified"]:
            notice.append("test draw: not recomputed, no beacon signature (test mode)")
        expected, tmpl = expected_plans(draw)
        template_rule = tmpl["testError_rule"]
        by = {}
        for R in Rs:
            k = match_plan(R, expected, campaign)
            if k in by:
                refuse(f"two roots on machine {k}: {by[k].path} and {R.path}")
            by[k] = R
        for k, p in expected.items():
            M[k] = dict(R=by.get(k), plan=rt(p))
            if k not in by:
                notice.append(f"no root: {k} (its instances are not run)")
    else:
        for k, R in enumerate(Rs, start=1):
            plan = R.json("PLAN.json") or R.json("PLAN_INPUT.json")
            if plan is None:
                refuse(f"{R.path}: no PLAN.json")
            M[f"machine_{k}"] = dict(R=R, plan=plan)
        notice.append("no draw: the expected plans are each root's own PLAN.json (test mode, no draw=)")
    if campaign and template_rule is None:
        refuse("campaign mode: no expected plans")
    seen = {}
    for k, m in M.items():
        if m["R"] is None:
            continue
        check_folders(m["R"], m["plan"])
        if not m["R"].finished:
            notice.append(f"root not finished: {k}")
        for name, g, s in home_instances(m["plan"]):
            if (m["R"].path / name / "status.json").exists():
                if (g, s) in seen:
                    refuse(f"the home instance {g} {s} is in more than one root: {seen[(g, s)]} and {k}")
                seen[(g, s)] = k
    if rehearsal == "1":
        notice.insert(0, "REHEARSAL: not the campaign; its outcomes count for no claim")
    before = sums_of(roots)
    out.mkdir(parents=True, exist_ok=True)
    build = kernel_library(out)
    res = layer_seals(M, times, build, th, campaign, template_rule, out)
    res = layer_stage_n_seal_log(res, M, th)
    res = layer_thresholds(res, tf, th)
    res = layer_record_seal_log(res, M)
    res = layer_duplicates(res, M, controls)
    res = layer_d4(res, M)
    res = layer_counts(res, sizes if "draw" in kw else None)
    after = sums_of(roots)
    if after != before:
        refuse(f"a root's SHA256SUMS changed during the analysis: {before} -> {after}")
    detail = {}
    for k, m in M.items():
        R = m["R"]
        if R is None:
            detail[k] = dict(root=None)
            continue
        rr = R.json("RESULT.json") if R.finished else R.json("RESULT_INSTANCES.json") if R.instances_done else None
        detail[k] = dict(root=str(R.path), finished=R.finished, instances_done=R.instances_done,
                         job_errors=(rr or {}).get("job_errors"), stopped_for_disk=(rr or {}).get("stopped_for_disk"),
                         files_verified=len(R.verified), files_read=len(R.reads),
                         files_read_unmanifested=sorted(x for x in R.reads if x not in R.verified))
    pre = "REHEARSAL: " if rehearsal == "1" else ""
    for g, v in res["groups"].items():                    # A8 and the rehearsal, in the verdict lines
        note = ((res.get("d4_audit") or {}).get("groups") or {}).get(g, {}).get("note")
        for lv in ("K0", "K3"):
            v[lv]["verdict"] = pre + v[lv]["verdict"] + (f" ({note})" if note else "")
    res["family"] = {lv: pre + x for lv, x in res["family"].items()}
    res.update(format=FORMAT, analysis_sha256=sha(__file__),
               mode=("REHEARSAL " if rehearsal == "1" else "") + ("CAMPAIGN" if campaign else "TEST"),
               NOTICE=notice, draw=draw_info, machines_detail=detail, tips=tips,
               unmanifested_rule=UNMANIFESTED, own_check_rule=dict(prefix="failed: ", simulator_end=list(SIMULATOR_END)),
               stage_d_script_rule=RULE10, kernel_sources_sha256=CP.KERNEL_SOURCES, root_drivers=drivers,
               roots_sha256sums=dict(before=before, after=after), pins=pc)
    (out / "RESULTS.json").write_bytes(canon(res))
    listed = [out / "RESULTS.json"] + sorted((out / "activity").glob("*.json")) if (out / "activity").exists() else [out / "RESULTS.json"]
    (out / "SHA256SUMS").write_text("".join(f"{sha(p)}  {p.relative_to(out)}\n" for p in listed))
    print(json.dumps(dict(results_sha256=sha(out / "RESULTS.json"), mode=res["mode"], notice=notice,
                          counts={g: {lv: {k: (x[k]["n"] if isinstance(x[k], dict) else x[k]) for k in ("counted",) + ROWS}
                                      for lv, x in v.items()} for g, v in res["counts"].items()}), indent=1))
    return True


if __name__ == "__main__":
    if len(sys.argv) < 4:
        sys.exit(__doc__)
    sys.exit(0 if main(*sys.argv[1:]) else 1)
