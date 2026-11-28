"""The campaign driver: one file, in place of the chain campaign_run.py … campaign_run17.py (the owner's decision,
relayed 2026-11-26). No new feature. The measuring code is called unchanged, each step a subprocess:
- stage_d6.py (deck, D, seal);
- indeck_noise4.py → the kit's invinst.indeck (the inverter gate);
- sealpush2.py (the seal push);
- controls4.py (stage N, U);
- compare_d2.py (the comparisons).
trace_extract.py, seal.py, spec.py and the envchecks are imported as libraries. No module attribute is reassigned at
run time, there is no subclass, and every plan or template value is read once (`Plan`). A missing value is a refusal:
there is no default.

  campaign.py launch MODE TEMPLATE PLAN OUTROOT     the checks, then `run` detached (setsid nohup); returns its pid
  campaign.py run    MODE TEMPLATE PLAN OUTROOT     the run itself (what launch and resume start), in the foreground
  campaign.py resume MODE TEMPLATE PLAN OUTROOT     `run` detached on an existing OUTROOT, after a stop
  campaign.py steps  MODE TEMPLATE PLAN OUTROOT room=yes|no eligible=yes|no
                                                    no-run mode: every step of every instance as JSON lines (argv,
                                                    cwd, env additions, expected outputs, time limit, guard, cores)
  campaign.py check  MODE TEMPLATE PLAN             the template and plan checks alone, as JSON
  campaign.py wait   OUTROOT [seconds<=590]         exit 0 when the run has ended, 3 while it runs
  campaign.py status OUTROOT

MODE is `campaign` or `test`:
- **campaign:** TEMPLATE must be campaign_template.json with the frozen sha256 (FROZEN_TEMPLATE_SHA256), every file
  of FREEZE_PINS.json must match its sha256 (campaign.py, analysis.py and the template among them), and this tree must
  be clean: no changed tracked file and no untracked .py or .json. Otherwise nothing starts. The pins' check is
  recorded in TEMPLATE_CHECK.json in both modes.
- **test:** any other template (a test template), never the frozen one. Every output then says TEST: ENV.json,
  RESULT.json, every status.json and DONE carry "mode": "TEST". analysis.py refuses such roots.

ENV.json and RESULT.json record this file's sha256 and the template's.

THE PLAN. The template's keys, equal to the template's values, plus the per-machine keys of plan_split3.py: what,
groups, U_groups, remote_duplicates (with home_machine, home_branch, home_instance), controls ({"duplicate": {}}: no
same-machine duplicate in the campaign), keep_raw, and seal_push.branch. Refused:
- a missing key, an extra key, or a different value;
- a malformed per-machine part;
- a tree that is not a clean worktree of this repository at its commit;
- a K3 budget whose sha256 differs.

THE STEPS of an instance, in OUTROOT/<TAG>_<seed>/:
- deck      stage_d6.py deck
- inverters front groups only: indeck_noise4.py (the kit's gate, the noise4 K3 budget); inv/K3_BUDGET.json ok
- D         stage_d6.py run (solo=1 when the seed is in groups[g].d4_audit); the kernel is the last word on Cell.Valid
- seal      stage_d6.py seal
- sealpush  sealpush2.py push (one at a time per machine)
- N0, C0    controls4.py stagen round 0, then compare_d2.py noiseless
- N<n>, C<n> for n = 1..rounds, only with room at K3, each round a job of its own
Before every N<n>:
- seal_push.json must say pushed true, with a 40-hex commit;
- the round waits until seal_push_delay_s after the push;
- N<n>/SEAL_LOG.json is written.
After an agreeing C<n>:
- the extract (trace_extract.py) is written first;
- then the raw is deleted, except N0 of a keep_raw instance.

The raw is kept whenever the comparison is not "agrees", when the extract fails, for U when U fails, and for every
duplicate.

PER MACHINE:
- **U**, per group of U_groups: once every instance of the group has ended its chain, U runs on the first instance in
  seed order that is eligible at K0 (controls4.py untrained).
- **The remote duplicates**, after the instances, one after the other. Each waits for its home's SEALS.txt line on
  home_branch, polling every duplicate_wait.interval_s for at most limit_s. It then fetches and checks the seal folder,
  runs N0, and compares.

THE DISK. launch refuses below disk_launch_gb free. During the run, below disk_guard_gb:
- no step, U or duplicate starts: it is held, listed in RESULT.json stopped_for_disk, and a later run starts it;
- the comparisons C<n> are exempt, and only they (each start below the guard is logged in GUARD_EXEMPT.json).

TIME LIMITS: time_limits_s per kind. At the limit the child's process group is killed and the step is "timeout".

THE CHILDREN. `run` and `resume` refuse while an ngspice process runs, the OUTROOT's driver is alive, or any other
process names the OUTROOT on its command line (campaign.py wait and status excepted). On SIGTERM or
SIGINT the driver kills every running child's process group (logged in SIGNALS.json) and exits; those steps stay
"running" and become "interrupted" at the next run. A driver killed by SIGKILL cannot do this: its children are then
found by the ngspice refusal.

THE RESULT. Once every instance's chain, rounds and U have ended, and before any remote duplicate starts waiting:
RESULT_INSTANCES.json (the instances' part of RESULT.json), SHA256SUMS.instances and INSTANCES_DONE. A machine's
instance results therefore never depend on another machine's seal. RESULT.json, SHA256SUMS and DONE follow the
duplicates.

U takes no core of the budget (as in the chain).

THE RESUME RULE. A step found "running" when a run starts (started, never ended: the driver or the machine stopped)
becomes "interrupted". A step not done (failed, timeout, interrupted, refused) is never started again. Its instance
ends there: "not completed". `run` on an existing OUTROOT therefore only starts what never started.
"""
import concurrent.futures as cf
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import envcheck_layered3 as E3  # noqa: E402
import envcheck_layered4 as E4  # noqa: E402
import seal as sealmod  # noqa: E402
import spec as specmod  # noqa: E402
import trace_extract  # noqa: E402

PY = sys.executable
FROZEN_TEMPLATE = HERE / "campaign_template.json"
FROZEN_TEMPLATE_SHA256 = "02af33e0c79b3dbdc320d3dd4e0dab26374cbd00a79bc249fcf20631a3cce756"
PINS = HERE / "FREEZE_PINS.json"
MUST_BE_PINNED = ("research/layered-networks/campaign.py", "research/layered-networks/analysis.py",
                  "research/layered-networks/campaign_template.json")
PER_MACHINE = ("what", "groups", "U_groups", "remote_duplicates", "controls", "keep_raw")
BRANCH = re.compile(r"evidence/combined-seals-K\d{2}")
TEST_BRANCH = re.compile(r"evidence/(combined-seals|devtest-seals|devtest-seals2)-K\d{2}")   # test mode only: the test-phase seal logs
KINDS = ("deck", "inverters", "D", "seal", "N", "C", "U", "dup")
WAIT_MAX_S = 590
LEAN_DIR = HERE.parent / "learned-coincidence"
KERNEL_SOURCES = {
    "Target.lean": "da5db52c5f04caa7599360a1538a8de8d5d396a8fcc91c550702cba7715fc7e5",
    "TwoLayerTarget.lean": "eed817c647d8db83c4a2015ec89d756eaeb000acdb18a8b4922737604a8eccf6",
    "MonotoneTarget.lean": "779797babfdaebf5bd4aeddf0128f7703093fa3b5c5cac762565f914f7f016e0",
    "MonotoneSupport.lean": "52156bbeb384840c67a3323c8335d7f1d7497cdd0b544e4addec0e56543a1678",
    "MonotoneOneSidedTarget.lean": "a44f60699aba2563c0ea4ab6e139bac71ab095e54a58673829335d93d567c8f3",
    "LayeredMonotoneTarget.lean": "521fdfee3f06893a879a1990b6d0e319536039cfe6d2acb7a47254e573fb6dec",
    "MonotonePremiseTargets.lean": "674e6783c0e4cba994d628f58e5ee66f8199010c5d5c25fb2f04c9393d27f30f",
    "LayeredMonotoneCheckerTargets.lean": "81c29cdf0c953a6ae7ef424c25dfde858a52f6c40dfe65cd29c9cb9c3f4d1fe8",
    "MonotonePremiseSoundness.lean": "57653f1f9644f5722038478a3d8837aec048b48f9042f90f874d74693d03d40f",
    "MonotonePremiseCompletenessTargets.lean": "e18070717f4d142d37ce10c4a3b78fa76699d1e35aeab7abea794044e5f69b5a",
    "MonotonePremiseCompleteness.lean": "6820f1b6f015e257d8b248e30ac361bfc9868dea5e529b64e36874f0608443a4",
    "LayeredMonotoneCheckerProofs.lean": "4dedf666f31dde8c9476c73bfd0fc5472850c5defc13e25e4dd8a0c696201657",
}
KERNEL_MODULES = [m[:-5] for m in KERNEL_SOURCES]


class Refused(SystemExit):
    pass


# ================================================================================================ small helpers

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def sha_bytes(b):
    return hashlib.sha256(b).hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%fZ")


def parse_utc(t):
    t = t.rstrip("Z")
    for fmt in ("%Y-%m-%dT%H:%M:%S.%f", "%Y-%m-%dT%H:%M:%S"):
        try:
            return datetime.datetime.strptime(t[:26], fmt).replace(tzinfo=datetime.timezone.utc)
        except ValueError:
            pass
    raise ValueError(t)


def dumps(obj):
    return json.dumps(obj, indent=1, sort_keys=True) + "\n"


def git_head(tree):
    """(HEAD, clean). Clean: no tracked file changed, and no untracked .py or .json file anywhere in the tree."""
    head = subprocess.run(["git", "-C", str(tree), "rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()
    st = subprocess.run(["git", "-C", str(tree), "status", "--porcelain", "--untracked-files=all"],
                        capture_output=True, text=True, check=True).stdout.splitlines()
    dirty = [ln for ln in st if not ln.startswith("??") or ln.rstrip('"').endswith((".py", ".json"))]
    return head, not dirty


def pins_check():
    """Every file of FREEZE_PINS.json against its sha256, in this driver's own tree, and that tree clean."""
    top = Path(subprocess.run(["git", "-C", str(HERE), "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                              check=True).stdout.strip())
    pins = json.loads(PINS.read_text()) if PINS.exists() else {"groups": {}}
    files = {p: h for fs in pins["groups"].values() for p, h in fs.items()}
    bad = sorted(p for p, h in files.items() if not (top / p).is_file() or sha(top / p) != h)
    head, clean = git_head(HERE)
    return dict(pins_file=str(PINS.relative_to(top)), pins_sha256=sha(PINS) if PINS.exists() else None,
                pinned_files=len(files), mismatched=bad, not_pinned=sorted(set(MUST_BE_PINNED) - set(files)),
                tree_commit=head, tree_clean=clean)


def pins_refusal(pc):
    """The reason campaign mode refuses this tree, or None."""
    why = []
    if pc["mismatched"]:
        why.append(f"pinned files differ from FREEZE_PINS.json: {pc['mismatched'][:5]}")
    if pc["not_pinned"]:
        why.append(f"not in FREEZE_PINS.json: {pc['not_pinned']}")
    if not pc["tree_clean"]:
        why.append(f"the tree at {pc['tree_commit'][:12]} is not clean (a changed tracked file, or an untracked .py/.json)")
    return "; ".join(why) or None


CHILDREN, CHILD_LOCK = set(), threading.RLock()  # the process groups of the running children; re-entrant, because
#   the signal handler runs in the main thread, which may hold the lock in run_child when the signal arrives


def on_signal(root):
    """SIGTERM or SIGINT to the driver: kill every running child's process group, log it, and exit. The steps they ran
    stay "running" in their status, and the next run records them "interrupted"."""
    def handler(signum, frame):
        with CHILD_LOCK:
            pids = sorted(CHILDREN)
            for pid in pids:
                try:
                    os.killpg(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
        try:
            f = Path(root) / "SIGNALS.json"
            log = json.loads(f.read_text()) if f.exists() else []
            log.append(dict(signal=signal.Signals(signum).name, at=now(), killed_process_groups=pids))
            f.write_text(dumps(log))
        finally:
            os._exit(128 + signum)
    return handler


def processes_on(root):
    """Live processes whose command line names OUTROOT (a child of a stopped driver), other than this process, its
    parent (the launch or resume that started it) and campaign.py's own wait and status."""
    me = {os.getpid(), os.getppid()}
    out = []
    for line in subprocess.run(["pgrep", "-af", re.escape(str(root)) + "([/ ]|$)"], capture_output=True, text=True).stdout.splitlines():
        pid, _, cmd = line.partition(" ")
        if int(pid) in me or re.search(r"campaign\.py (wait|status) ", cmd) or cmd.startswith("pgrep "):
            continue
        out.append(dict(pid=int(pid), cmd=cmd[:200]))
    return out


def ngspice_running():
    """Live ngspice processes. A zombie (state Z: killed, not yet reaped by init) does not count: it runs nothing."""
    ps = subprocess.run(["ps", "-eo", "stat=,comm="], capture_output=True, text=True).stdout.splitlines()
    return sum(1 for ln in ps if ln.split()[1:2] == ["ngspice"] and not ln.split()[0].startswith("Z"))


def run_child(argv, cwd, log, timeout):
    """One child process, in its own session. Returns its exit code, its CPU seconds (user + system of the child and
    every descendant it waited for, from wait4) and whether it was killed at the time limit."""
    with Path(log).open("w") as fh:
        with CHILD_LOCK:
            p = subprocess.Popen([str(a) for a in argv], cwd=cwd, stdout=fh, stderr=subprocess.STDOUT, env=dict(os.environ),
                                 start_new_session=True)
            CHILDREN.add(p.pid)
        killed = threading.Event()

        def kill():
            killed.set()
            try:
                os.killpg(p.pid, 9)
            except ProcessLookupError:
                pass
        timer = threading.Timer(timeout, kill)
        timer.start()
        _, status, ru = os.wait4(p.pid, 0)
        timer.cancel()
        with CHILD_LOCK:
            CHILDREN.discard(p.pid)
        rc = os.waitstatus_to_exitcode(status)
    return rc, round(ru.ru_utime + ru.ru_stime, 1), killed.is_set()


# ================================================================================================ template and plan

def load_template(mode, path):
    if mode not in ("campaign", "test"):
        raise Refused(f"refused: mode {mode!r} is neither campaign nor test")
    b = Path(path).read_bytes()
    h = sha_bytes(b)
    if mode == "campaign" and h != FROZEN_TEMPLATE_SHA256:
        raise Refused(f"refused: campaign mode needs the frozen template {FROZEN_TEMPLATE_SHA256[:12]}, not {h[:12]}")
    if mode == "test" and h == FROZEN_TEMPLATE_SHA256:
        raise Refused("refused: test mode needs a test template, not the frozen one")
    t = json.loads(b)
    need = {"allow_dry_seal", "cores", "disk_guard_gb", "disk_launch_gb", "duplicate_wait", "k3_budget_sha256",
            "kit_commit", "noise_commit", "overlay", "rounds", "seal_push", "seal_push_delay_s", "stage_d_script",
            "stagen", "testError_rule", "time_limits_s", "what"}
    if set(t) != need:
        raise Refused(f"refused: template keys {sorted(set(t) ^ need)} missing or extra")
    if t["stage_d_script"] != "stage_d6.py" or t["stagen"] != "controls4" or t["allow_dry_seal"] is not False:
        raise Refused("refused: this driver runs stage_d6.py, controls4 and no dry seal only")
    if set(t["time_limits_s"]) != set(KINDS) or set(t["duplicate_wait"]) != {"interval_s", "limit_s"}:
        raise Refused("refused: time_limits_s or duplicate_wait incomplete")
    if set(t["seal_push"]) != {"remote", "dry"} or t["seal_push"]["dry"] is not False:
        raise Refused("refused: seal_push must be {remote, dry: false}")
    return t, dict(mode="CAMPAIGN" if mode == "campaign" else "TEST", template=str(Path(path).resolve()),
                   template_sha256=h, driver_sha256=sha(__file__))


def check_plan(plan, t, mode):
    """The plan against the template: a list of reasons (empty: it agrees). Campaign mode accepts only the campaign's
    seal-log branches, evidence/combined-seals-K<nn>; test mode also evidence/devtest-seals-K<nn>
    and evidence/devtest-seals2-K<nn> (the second test-phase run: a seal is append-only)."""
    bad = []
    branches = BRANCH if mode == "campaign" else TEST_BRANCH
    for k in sorted(t):
        if k == "what":
            continue
        if k not in plan:
            bad.append(f"missing key {k}")
        elif k == "seal_push":
            sp = {x: y for x, y in (plan[k] or {}).items() if x != "branch"}
            if sp != t[k]:
                bad.append(f"seal_push {sp} differs from the template's {t[k]}")
        elif plan[k] != t[k]:
            bad.append(f"{k} is {plan[k]!r}, the template's is {t[k]!r}")
    for k in sorted(set(plan) - set(t) - set(PER_MACHINE)):
        bad.append(f"key {k} is not allowed")
    for k in sorted(set(PER_MACHINE) - {"what"} - set(plan)):
        bad.append(f"missing per-machine key {k}")
    branch = (plan.get("seal_push") or {}).get("branch")
    if not branches.fullmatch(str(branch)):
        bad.append(f"seal_push.branch {branch!r} is not {branches.pattern}")
    if plan.get("controls") != {"duplicate": {}}:
        bad.append("controls must be {\"duplicate\": {}} (no same-machine duplicate)")
    names = set()
    for g, v in (plan.get("groups") or {}).items():
        if set(v) != {"spec", "seeds", "d4_audit"}:
            bad.append(f"group {g}: keys {sorted(v)} are not spec, seeds, d4_audit")
            continue
        tag = specmod.load(HERE / v["spec"])["tag"]
        names |= {f"{tag}_{s}" for s in v["seeds"]}
        if set(v["d4_audit"]) - set(v["seeds"]):
            bad.append(f"{g}: d4_audit seeds not among its seeds")
    if set(plan.get("keep_raw") or []) - names:
        bad.append("keep_raw names an instance not in this plan")
    if set(plan.get("U_groups") or []) - set(plan.get("groups") or {}):
        bad.append("U_groups names a group not in this plan")
    for x in plan.get("remote_duplicates") or []:
        if set(x) != {"group", "spec", "seed", "home_machine", "home_branch", "home_instance"}:
            bad.append(f"remote duplicate {x.get('seed')}: keys {sorted(x)} (seal_log or seal_dir are not allowed)")
            continue
        inst = f"{specmod.load(HERE / x['spec'])['tag']}_{x['seed']}"
        if not branches.fullmatch(str(x["home_branch"])) or x["home_branch"] == branch or x["home_instance"] != inst:
            bad.append(f"remote duplicate {inst}: home_branch or home_instance wrong")
    return bad


def worktrees():
    out = subprocess.run(["git", "-C", str(HERE), "worktree", "list", "--porcelain"], capture_output=True, text=True,
                         check=True).stdout
    trees = []
    for block in out.strip().split("\n\n"):
        d = dict((ln.split(" ", 1) + [""])[:2] for ln in block.splitlines())
        if "worktree" in d and "HEAD" in d:
            trees.append((d["worktree"], d["HEAD"]))
    return sorted(trees)


def resolve_trees(plan):
    res = {}
    trees = worktrees()
    for key, ck in (("kit_tree", "kit_commit"), ("noise_tree", "noise_commit")):
        commit = plan[ck]
        if not re.fullmatch(r"[0-9a-f]{40}", commit):
            raise Refused(f"refused: {ck} {commit!r} is not a full commit hash")
        found = [p for p, h in trees if h == commit and git_head(p)[1]]
        if not found:
            raise Refused(f"refused: no clean worktree at {ck} {commit[:12]} (git worktree add --detach DIR {commit})")
        res[key] = found[0]
    budget = Path(res["noise_tree"]) / "research" / "layered-networks" / "noise4_budget.json"
    if not budget.exists() or sha(budget) != plan["k3_budget_sha256"]:
        raise Refused(f"refused: {budget} is not the template's k3_budget_sha256")
    return res


def check(mode, template_path, plan_path):
    t, campaign = load_template(mode, template_path)
    b = Path(plan_path).read_bytes()
    plan = json.loads(b)
    bad = check_plan(plan, t, mode)
    if bad:
        raise Refused("refused: the plan differs from the template: " + "; ".join(bad))
    pc = pins_check()
    if mode == "campaign" and pins_refusal(pc):
        raise Refused("refused: campaign mode: " + pins_refusal(pc))
    trees = resolve_trees(plan)
    tc = dict(campaign, plan_input_sha256=sha_bytes(b), trees=trees, k3_budget_sha256=t["k3_budget_sha256"], pins=pc,
              ok=True)
    return Plan(dict(plan, **trees), campaign), b, tc


class Plan:
    """Every value the run reads, read here once."""

    def __init__(self, p, campaign):
        self.raw = p
        self.campaign = campaign
        self.cores = int(p["cores"])
        self.guard_gb = float(p["disk_guard_gb"])
        self.launch_gb = float(p["disk_launch_gb"])
        self.wait_interval_s = int(p["duplicate_wait"]["interval_s"])
        self.wait_limit_s = int(p["duplicate_wait"]["limit_s"])
        self.overlay = p["overlay"]
        self.rounds = int(p["rounds"])
        self.remote = p["seal_push"]["remote"]
        self.branch = p["seal_push"]["branch"]
        self.delay_s = float(p["seal_push_delay_s"])
        self.rule = p["testError_rule"]
        self.limits = {k: float(v) for k, v in p["time_limits_s"].items()}
        self.kit_tree, self.noise_tree = Path(p["kit_tree"]), Path(p["noise_tree"])
        self.nz = self.noise_tree / "research" / "layered-networks"
        self.kit = self.kit_tree / "research" / "circuit" / "inverter" / "instances"
        self.budget = self.nz / "noise4_budget.json"
        self.groups = p["groups"]
        self.u_groups = set(p["U_groups"])
        self.keep_raw = set(p["keep_raw"])
        self.duplicates = [dict(x) for x in p["remote_duplicates"]]


def check_trees(plan_raw):
    out = {}
    for key, ck in (("noise_tree", "noise_commit"), ("kit_tree", "kit_commit")):
        if not plan_raw.get(key):
            continue
        head, clean = git_head(plan_raw[key])
        if not (head.startswith(plan_raw[ck]) and clean):
            raise Refused(f"refused: {key} is at {head} (clean {clean}), not the pinned {plan_raw[ck]}")
        out[key] = dict(path=str(plan_raw[key]), commit=head)
    out["stage_d_tree"] = dict(zip(("commit", "clean"), git_head(HERE)))
    return out


def inventory(plan_raw=None):
    up = subprocess.run(["uptime", "-s"], capture_output=True, text=True).stdout.strip()
    out = dict(uptime_s=up, nproc=os.cpu_count(), at=now())
    if plan_raw is not None:
        ng = subprocess.run(["sh", "-c", "readlink -f $(command -v ngspice)"], capture_output=True, text=True).stdout.strip()
        out.update(ngspice=ng, ngspice_sha256=hashlib.sha256(Path(ng).read_bytes()).hexdigest() if ng else None,
                   trees=check_trees(plan_raw))
    return json.dumps(out, indent=1, sort_keys=True) + "\n"


def free_gb(path):
    p = Path(path)
    while not p.exists():
        p = p.parent
    return shutil.disk_usage(p).free / 1e9


# ================================================================================================ the environment

def set_env(plan_raw, root, campaign):
    bad = [k for k, v in E4.checks().items() if not v["ok"]]
    if bad:
        raise Refused("refused: envcheck_layered4 fails: " + ", ".join(bad))
    e = E3.env(plan_raw)
    e["campaign"] = campaign
    f = root / "ENV.json"
    if f.exists():
        old = json.loads(f.read_text())
        if old["static_sha256"] != e["static_sha256"] or old.get("campaign") != campaign:
            raise Refused(f"refused: mixed environment in {root}: ENV.json static {old['static_sha256'][:12]} / "
                          f"{(old.get('campaign') or {}).get('mode')}, this machine now {e['static_sha256'][:12]} / "
                          f"{campaign['mode']}")
        rs = root / "ENV_RESUMES.json"
        log = json.loads(rs.read_text()) if rs.exists() else []
        log.append(dict(uptime_s=e["uptime_s"], static_sha256=e["static_sha256"]))
        rs.write_text(json.dumps(log, indent=1) + "\n")
    else:
        f.write_bytes(E3.E.canon(e))
    return sha(f)


def build_kernel(root):
    have = {f"{m}.lean": sha(LEAN_DIR / f"{m}.lean") for m in KERNEL_MODULES}
    bad = sorted(k for k in KERNEL_SOURCES if have[k] != KERNEL_SOURCES[k])
    if bad:
        raise Refused(f"refused: the kernel's Lean sources differ from the pinned ones: {bad}")
    build = Path(root) / "kernel_build"
    meta_f = build / "KERNEL_BUILD.json"
    r = E3.lean_resolution()                           # envcheck's resolver: the real toolchain binary, not elan's proxy
    if not r.get("path"):
        raise Refused("refused: no lean binary found")
    lean, lean_sha = r["path"], r["sha256"]
    if meta_f.exists():
        meta = json.loads(meta_f.read_text())
        if meta.get("sources_sha256") == KERNEL_SOURCES and meta.get("lean_binary_sha256") == lean_sha and \
                (build / "LayeredMonotoneCheckerProofs.olean").exists():
            return build
        shutil.rmtree(build)
    build.mkdir(parents=True)
    t0 = time.time()
    env = dict(os.environ, LEAN_PATH=str(build))
    for m in KERNEL_MODULES:
        p = subprocess.run([lean, "-o", str(build / f"{m}.olean"), f"{m}.lean"], cwd=LEAN_DIR, env=env,
                           capture_output=True, text=True, timeout=3600)
        if p.returncode:
            raise Refused(f"refused: the kernel library does not build ({m}): {(p.stdout + p.stderr)[-1500:]}")
    meta_f.write_text(dumps(dict(format="layered-kernel-build/1", sources_sha256=KERNEL_SOURCES,
                                 lean_binary_sha256=lean_sha, lean_binary=lean, lean_resolved_by=r.get("resolved_by"),
                                 modules=KERNEL_MODULES, seconds=round(time.time() - t0, 1))))
    return build


# ================================================================================================ the machine's state

class Budget:
    """At most `cores` cores in use; acquire(n) waits until n are free. Records the peak in use."""

    def __init__(self, cores):
        self.cores, self.used, self.peak = cores, 0, 0
        self.cv = threading.Condition()

    def acquire(self, n):
        n = min(n, self.cores)
        with self.cv:
            while self.used + n > self.cores:
                self.cv.wait()
            self.used += n
            self.peak = max(self.peak, self.used)
        return n

    def release(self, n):
        with self.cv:
            self.used -= n
            self.cv.notify_all()


class Machine:
    def __init__(self, plan, root, env_add):
        self.plan, self.root, self.env_add = plan, root, env_add
        self.budget = Budget(plan.cores)
        self.seal_lock = threading.Lock()
        self.lock = threading.Lock()
        self.held = []

    def guard(self, inst, step, kind):
        """(may start, free GB). Every kind is guarded but C, the comparisons (they delete raws)."""
        free = round(free_gb(self.root), 2)
        if free >= self.plan.guard_gb:
            return True, free
        if kind == "C":
            with self.lock:
                f = self.root / "GUARD_EXEMPT.json"
                log = json.loads(f.read_text()) if f.exists() else []
                log.append(dict(instance=inst, step=step, free_gb=free, guard_gb=self.plan.guard_gb))
                f.write_text(dumps(log))
            return True, free
        with self.lock:
            self.held.append(dict(instance=inst, step=step, free_gb=free))
        return False, free


# ================================================================================================ an instance

class Instance:
    def __init__(self, machine, group, seed):
        self.m, self.plan = machine, machine.plan
        self.group, self.seed = group, int(seed)
        self.spec_path = Path(self.plan.groups[group]["spec"])
        self.s = specmod.load(HERE / self.spec_path)
        self.audited = self.seed in self.plan.groups[group]["d4_audit"]
        self.dir = machine.root / f"{self.s['tag']}_{self.seed}"
        self.dir.mkdir(parents=True, exist_ok=True)
        self.status_path = self.dir / "status.json"
        self.lock = threading.Lock()
        self.status = json.loads(self.status_path.read_text()) if self.status_path.exists() else dict(
            tag=self.s["tag"], seed=self.seed, group=group, steps={})
        changed = False
        for st in self.status["steps"].values():               # started and never ended: interrupted, never rerun
            if st["status"] == "running":
                st.update(status="interrupted", why="found running at a resume (the driver or the machine stopped)",
                          found_at=now())
                changed = True
        sha_env = machine.env_add["LAYERED_ENV_SHA256"]
        have = self.status.get("env_sha256")
        if have and have != sha_env:
            raise Refused(f"refused: {self.dir.name} was run under ENV {have[:12]}, not {sha_env[:12]}")
        self.status["env_sha256"] = sha_env
        self.status["mode"] = self.plan.campaign["mode"]
        self.save()

    def save(self):
        with self.lock:
            tmp = self.status_path.with_suffix(".tmp")
            tmp.write_text(dumps(self.status))
            os.replace(tmp, self.status_path)

    def done(self, name):
        st = self.status["steps"].get(name)
        if not st or st["status"] != "done":
            return False
        for f, h in st["outputs"].items():
            if not (self.dir / f).exists() or sha(self.dir / f) != h:
                raise Refused(f"refused: {self.dir.name} step {name}: output {f} changed after it was recorded")
        return True

    # ---------------------------------------------------------------------------------------- one step
    def step(self, name, argv, outputs, kind, cwd, cores=1):
        if self.done(name):
            return True
        st = self.status["steps"].get(name)
        if st and st["status"] != "done":
            return False                                   # failed, timeout, interrupted or refused: never again
        if not self.m.guard(self.dir.name, name, kind)[0]:
            return False                                   # held: no status entry, a later run starts it
        got = self.m.budget.acquire(cores)
        try:
            t0 = time.time()
            rec = dict(argv=[str(a) for a in argv], started=now(), status="running")
            self.status["steps"][name] = rec
            self.save()
            rc, cpu, timed_out = run_child(argv, cwd, self.dir / f"{name}.log", self.plan.limits[kind])
            rec = dict(rec)
            if timed_out:
                rec.update(status="timeout", why=f"more than {self.plan.limits[kind]:g} s")
            else:
                missing = [f for f in outputs if not (self.dir / f).exists()]
                if rc == 0 and not missing:
                    rec.update(status="done", outputs={f: sha(self.dir / f) for f in outputs})
                else:
                    rec.update(status="failed", why=f"exit {rc}" + (f", missing {missing}" if missing else ""))
            rec.update(wall_s=round(time.time() - t0, 1), cpu_s=cpu, ended=now())
        finally:
            self.m.budget.release(got)
        rec["cores"] = got
        self.status["steps"][name] = rec
        self.save()
        return rec["status"] == "done"

    # ---------------------------------------------------------------------------------------- the steps' argv
    def steps_chain(self):
        """(name, argv, outputs, kind, cwd, cores) of deck .. sealpush."""
        d, sp, ov, seed, p = self.dir, HERE / self.spec_path, self.plan.overlay, self.seed, self.plan
        sd = HERE / "stage_d6.py"
        out = [("deck", [PY, "-B", sd, "deck", sp, d / "deck.spice", f"overlay={ov}"], ["deck.spice"], "deck", HERE, 1)]
        if self.s["front"]:
            out.append(("inverters", [PY, "-B", HERE / "indeck_noise4.py", p.kit, p.budget, d / "inv", "--deck",
                                      d / "deck.spice", "--seed", seed],
                        ["inv/inverter_gate.json", "inv/SHA256SUMS", "inv/K3_BUDGET.json"], "inverters", HERE,
                        self.s["m"]))
        inv = [f"inverters={d / 'inv' / 'inverter_gate.json'}"] if self.s["front"] else []
        solo = ["solo=1"] if self.audited else []
        out.append(("D", [PY, "-B", sd, "run", sp, d / "D", seed, f"overlay={ov}", f"rule={p.rule}", *inv, *solo],
                    ["D/record.json", "D/prediction.json"], "D", HERE, 1))
        out.append(("seal", [PY, "-B", sd, "seal", d / "seal", d / "D"], ["seal/SHA256SUMS", "seal/MANIFEST.json"],
                    "seal", HERE, 1))
        out.append(("sealpush", [PY, "-B", HERE / "sealpush2.py", "push", p.remote, p.branch, d.name, d / "seal",
                                 self.m.root / ".seal_log_work", d / "seal_push.json"], ["seal_push.json"], "seal", HERE, 1))
        return out

    def seal_log(self):
        """(commit, branch) of this instance's pushed seal, or None (a dry seal never counts)."""
        f = self.dir / "seal_push.json"
        if not f.exists():
            return None
        r = json.loads(f.read_text())
        ok = r.get("pushed") is True and re.fullmatch(r"[0-9a-f]{40}", r.get("commit") or "") and r.get("branch")
        return (r["commit"], r["branch"]) if ok else None

    def steps_round(self, n, seal=("", "")):
        d, sp, p = self.dir, HERE / self.spec_path, self.plan
        out = d / f"N{n}"
        commit, branch = seal
        stagen = [PY, "-B", p.nz / "controls4.py", "stagen", sp, out, self.seed, n, f"seal_log={commit}",
                  f"seal_branch={branch}", f"overlay={p.overlay}"]
        comp = [PY, "-B", HERE / "compare_d2.py", d / "seal", sp, out / "noisy_record.json",
                "noiseless" if n == 0 else "noisy", out / "comparison.json"]
        return [(f"N{n}", stagen, [f"N{n}/noisy_record.json", f"N{n}/trace.digest.json"], "N", p.nz, 1),
                (f"C{n}", comp, [f"N{n}/comparison.json"], "C", HERE, 1)]

    # ---------------------------------------------------------------------------------------- the chain and the rounds
    def chain(self):
        """deck .. C0. Returns room_K3 (the noisy rounds follow), or None when the chain stopped."""
        for name, argv, outs, kind, cwd, cores in self.steps_chain():
            ctx = self.m.seal_lock if name == "sealpush" else _Null()
            with ctx:
                if not self.step(name, argv, outs, kind, cwd, cores):
                    return None
            if name == "inverters" and not json.loads((self.dir / "inv" / "K3_BUDGET.json").read_text()).get("ok"):
                if "D" not in self.status["steps"]:          # no silent stop: the reason is in the status
                    self.status["steps"]["D"] = dict(status="refused", ended=now(),
                                                     why="inv/K3_BUDGET.json is not ok (the inverters' K3 budget)")
                    self.save()
                return None
        if not self.round(0):
            return None
        return json.loads((self.dir / "D" / "prediction.json").read_text())["room_K3"]

    def round(self, n):
        name = f"N{n}"
        seal = self.seal_log()
        if not self.done(name) and name not in self.status["steps"]:
            if seal is None:
                self.status["steps"][name] = dict(status="refused", why="no pushed seal-log commit (seal_push.json)",
                                                  ended=now())
                self.save()
                return False
            r = json.loads((self.dir / "seal_push.json").read_text())
            pushed_at = r.get("pushed_at_machine_utc")
            if pushed_at:
                wait = self.plan.delay_s - (parse_utc(now()) - parse_utc(pushed_at)).total_seconds()
                if wait > 0:
                    time.sleep(wait)
            (self.dir / name).mkdir(parents=True, exist_ok=True)
            (self.dir / name / "SEAL_LOG.json").write_text(dumps(dict(commit=r["commit"], branch=r.get("branch"),
                                                                      seal_sha256=r.get("seal_sha256"), line=r.get("line"),
                                                                      pushed=r.get("pushed"))))
        (nn, na, no, nk, nc, _), (cn, ca, co, ck, cc, _) = self.steps_round(n, seal or ("", ""))
        ok = self.step(nn, na, no, nk, nc) and self.step(cn, ca, co, ck, cc)
        if ok:
            after_comparison(self.dir / name, self.dir.name in self.plan.keep_raw)
        return ok

    def summary(self):
        d = self.dir
        out = dict(tag=self.s["tag"], seed=self.seed, group=self.group,
                   steps={k: v["status"] for k, v in self.status["steps"].items()})
        if (d / "D" / "prediction.json").exists():
            p = json.loads((d / "D" / "prediction.json").read_text())
            out.update(eligible_K0=p["eligible_K0"], room_K3=p["room_K3"], inverter_gate=p["inverter_gate"]["source"])
        out["verdicts"] = {f"C{n}": json.loads((d / f"N{n}" / "comparison.json").read_text())["verdict"]
                           for n in range(0, 4) if (d / f"N{n}" / "comparison.json").exists()}
        out["cpu_s"] = {k: v.get("cpu_s") for k, v in self.status["steps"].items()}
        out["wall_s"] = {k: v.get("wall_s") for k, v in self.status["steps"].items()}
        files = sorted(p for p in d.rglob("*.json") if p.name != "status.json" and "lean_build" not in p.parts)
        (d / "SHA256SUMS").write_text("".join(f"{sha(p)}  {p.relative_to(d)}\n" for p in files))
        st = self.status["steps"]
        w = lambda k: (st.get(k) or {}).get("wall_s") or 0
        chain = sum(w(k) for k in ("deck", "inverters", "D", "seal", "N0", "C0"))
        rounds = max([w(f"N{n}") + w(f"C{n}") for n in (1, 2, 3)] or [0])
        out["critical_path"] = dict(chain_s=round(chain, 1), longest_round_s=round(rounds, 1), total_s=round(chain + rounds, 1))
        return out


class _Null:
    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False


# ================================================================================================ raws

def drop(folder):
    raw, dig = Path(folder) / "trace.raw", Path(folder) / "trace.digest.json"
    if raw.exists() and dig.exists():
        raw.unlink()


def after_comparison(folder, keep):
    """After an agreeing or other completed comparison of a round: the extract first, then the raw rule."""
    folder = Path(folder)
    if (folder / "trace.raw").exists() and not (folder / "extract" / "extract.json").exists():
        try:
            trace_extract.extract(folder)
        except (SystemExit, Exception) as e:              # the whole trace is then kept
            (folder / "extract_failed.json").write_text(json.dumps(dict(ok=False, why=str(e)), indent=1) + "\n")
            return
    if keep and folder.name == "N0":
        return                                            # the original of a remote duplicate: its N0 raw is kept
    comp = folder / "comparison.json"
    if comp.exists() and json.loads(comp.read_text()).get("verdict") == "agrees":
        drop(folder)


# ================================================================================================ U

def untrained(m, inst):
    p = m.plan
    if inst.group not in p.u_groups:
        return dict(instance=inst.dir.name, ok=None, why="U of this group runs on another machine")
    d = m.root / f"U_{inst.dir.name}"
    res_path = d / "untrained.json"
    if res_path.exists():
        return json.loads(res_path.read_text())
    ok_disk, free = m.guard(d.name, "U", "U")
    if not ok_disk:
        return dict(instance=inst.dir.name, ok=None, held_for_disk=True,
                    why=f"held: {free} GB free, below the {p.guard_gb} GB guard")
    d.mkdir(exist_ok=True)
    s = inst.seal_log()
    commit, branch = s if s else ("", "")
    script = p.nz / "controls4.py"
    rc, cpu, to = run_child([PY, "-B", script, "untrained", HERE / inst.spec_path, d / "U", inst.seed,
                             f"seal_log={commit}", f"seal_branch={branch}", f"overlay={p.overlay}"], p.nz,
                            d / "U.log", p.limits["U"])           # as in the chain, U takes no core of the budget
    res = dict(instance=inst.dir.name, exit=rc, timed_out=to, cpu_s=cpu, seal_log=dict(commit=commit, branch=branch),
               tool=script.name)
    rec_path = d / "U" / "untrained_record.json"
    if rc == 0 and not to and rec_path.exists():
        rec = json.loads(rec_path.read_text())
        fired = [dict(slot=i, cell=f"c{r['layer']}_{r['index']}") for i in rec["tests"]
                 for r in rec["slots"][i]["reads"] if r["emission"] is not None]
        invf = [dict(slot=i, inverter=j) for i in rec["tests"] for j, v in enumerate(rec["slots"][i].get("inv", []))
                if v.get("emission") is not None]
        res.update(patterns=len(rec["tests"]), r_cell_fires=fired, inverter_fires_reported=invf, ok=not fired,
                   record_seal_log=rec.get("seal_log"))
    else:
        res["ok"] = False
    u_rec = json.loads(rec_path.read_text()) if rec_path.exists() else None
    holds = u_rec is not None and all(r["emission"] is None for i in u_rec.get("tests", [])
                                      for r in u_rec["slots"][i]["reads"])
    if holds:
        drop(d / "U")                                     # U's raw: dropped when U holds, kept when it fails
    res_path.write_text(dumps(res))
    return res


# ================================================================================================ the remote duplicate

def probe(remote, branch, inst):
    with tempfile.TemporaryDirectory() as g:
        run = lambda *a: subprocess.run(["git", "-C", g, *a], capture_output=True, text=True)
        run("init", "-q", "--bare")
        if run("fetch", "-q", str(remote), f"refs/heads/{branch}:refs/heads/{branch}").returncode:
            return None, None
        tip = run("rev-parse", f"refs/heads/{branch}").stdout.strip()
        s = run("show", f"{tip}:SEALS.txt")
        lines = [l for l in s.stdout.splitlines() if l.split() and l.split()[0] == inst] if not s.returncode else []
        return tip, (lines[-1] if lines else None)


def wait_for_seal(m, x, inst, log_path):
    t0 = time.time()
    log = dict(remote=str(m.plan.remote), branch=x["home_branch"], instance=inst, interval_s=m.plan.wait_interval_s,
               limit_s=m.plan.wait_limit_s, attempts=[])
    while True:
        tip, line = probe(m.plan.remote, x["home_branch"], inst)
        log["attempts"].append(dict(utc=now(), tip=tip, found=line is not None))
        found = line is not None
        waited = time.time() - t0
        if found or waited + m.plan.wait_interval_s > m.plan.wait_limit_s:
            log.update(found=found, commit=tip if found else None, line=line, waited_s=round(waited, 1))
            Path(log_path).write_text(dumps(log))
            return tip if found else None
        Path(log_path).write_text(dumps(log))
        time.sleep(m.plan.wait_interval_s)


def seal_log_line(remote, commit, branch, instance, want_sha):
    with tempfile.TemporaryDirectory() as g:
        run = lambda *a: subprocess.run(["git", "-C", g, *a], capture_output=True, text=True)
        run("init", "-q", "--bare")
        f = run("fetch", "-q", str(remote), f"refs/heads/{branch}:refs/heads/{branch}")
        if f.returncode:
            return False, f"fetch {branch}: {f.stderr.strip()[:200]}"
        if run("merge-base", "--is-ancestor", commit, f"refs/heads/{branch}").returncode:
            return False, f"commit {commit} is not on {branch}"
        s = run("show", f"{commit}:SEALS.txt")
        if s.returncode:
            return False, f"no SEALS.txt at {commit}"
        lines = [l.split() for l in s.stdout.splitlines() if l.split() and l.split()[0] == instance]
        if not lines:
            return False, f"no line for {instance} in SEALS.txt at {commit}"
        if lines[-1][1] != want_sha:
            return False, f"the log's seal sha256 {lines[-1][1][:12]} is not seal_dir's {want_sha[:12]}"
        return True, None


def fetch_seal(remote, branch, commit, instance, dest):
    """The seal folder seals/<instance>/ at COMMIT of BRANCH, fetched by name (sealpush2.fetch's rule)."""
    import sealpush2
    return sealpush2.fetch(remote, branch, commit, instance, dest)


def remote_duplicate(m, x):
    p = m.plan
    s = specmod.load(HERE / x["spec"])
    inst = f"{s['tag']}_{x['seed']}"
    d = m.root / f"DUPX_{inst}"
    d.mkdir(parents=True, exist_ok=True)
    res_path = d / "duplicate_here.json"
    if res_path.exists():
        return json.loads(res_path.read_text())
    commit = wait_for_seal(m, x, inst, d / "seal_wait.json")
    if commit is None:
        return dict(instance=inst, group=x["group"], ok=False, not_completed=True,
                    why=f"not completed: no SEALS.txt line for {inst} on {x['home_branch']} within {p.wait_limit_s} s")
    ok_disk, free = m.guard(d.name, "N0", "dup")
    if not ok_disk:
        return dict(instance=inst, group=x["group"], ok=False, not_completed=True, held_for_disk=True,
                    why=f"not completed: held, {free} GB free, below the {p.guard_gb} GB guard")
    branch = x["home_branch"]
    with tempfile.TemporaryDirectory() as t:
        sd = Path(t) / "seal"
        ok_fetch, why = fetch_seal(p.remote, branch, commit, inst, sd)
        (d / "seal_fetch.json").write_text(dumps(dict(remote=str(p.remote), branch=branch, commit=commit,
                                                      path=f"seals/{inst}", ok=ok_fetch, why=why)))
        argv = [PY, "-B", p.nz / "controls4.py", "stagen", HERE / x["spec"], d / "N0", x["seed"], 0,
                f"seal_log={commit}", f"seal_branch={branch}", f"overlay={p.overlay}"]
        got = m.budget.acquire(1)
        try:
            rc, cpu, to = run_child(argv, p.nz, d / "N0.log", p.limits["dup"])
        finally:
            m.budget.release(got)
        res = dict(instance=inst, group=x["group"], exit=rc, timed_out=to, cpu_s=cpu,
                   ok=rc == 0 and not to and (d / "N0" / "noisy_record.json").exists())
        res_path.write_text(dumps(res))
        chk = dict(instance=inst, seal_dir=str(sd) if ok_fetch else None, seal_log=[commit, branch])
        if not res["ok"]:
            chk.update(ok=False, why="the duplicate's N0 did not complete")
        elif not ok_fetch:
            chk.update(ok=False, why="no seal_dir or seal_log in PLAN remote_duplicates")
        else:
            try:
                verified = sd.is_dir() and sealmod.verify(sd, quiet=True)
            except SystemExit as e:
                verified = False
                chk["verify_error"] = str(e)
            want = sha(sd / "SHA256SUMS") if (sd / "SHA256SUMS").exists() else None
            ok, why2 = (seal_log_line(p.remote, commit, branch, inst, want) if verified and want
                        else (False, "seal.verify failed or no SHA256SUMS"))
            chk.update(ok=ok, why=why2, seal_sha256=want)
            if ok:
                if (d / "seal").exists():
                    shutil.rmtree(d / "seal")
                shutil.copytree(sd, d / "seal", symlinks=False)
                comp = [PY, "-B", HERE / "compare_d2.py", d / "seal", HERE / x["spec"], d / "N0" / "noisy_record.json",
                        "noiseless", d / "N0" / "comparison.json"]
                rc2, cpu2, to2 = run_child(comp, HERE, d / "C0.log", p.limits["C"])
                done = rc2 == 0 and not to2 and (d / "N0" / "comparison.json").exists()
                chk.update(compare=dict(exit=rc2, timed_out=to2, cpu_s=cpu2, written=done))
                if done:
                    chk["verdict"] = json.loads((d / "N0" / "comparison.json").read_text())["verdict"]
                chk["ok"] = done
        (d / "seal_check.json").write_text(dumps(chk))
    return res


# ================================================================================================ the run

def top_files(root):
    files = sorted(p for p in root.glob("*/SHA256SUMS")) + [root / "RESULT.json", root / "PLAN.json", root / "trees.json",
                                                            root / "RESULT_INSTANCES.json", root / "SHA256SUMS.instances"]
    files += sorted(root.glob("U_*/untrained.json")) + sorted(root.glob("DUPX_*/duplicate_here.json"))
    return [p for p in files if p.exists()]


def write_once(p, b):
    if p.exists():
        if p.read_bytes() != b:
            raise Refused(f"refused: {p} differs (OUTROOT was started with another plan or template)")
    else:
        p.write_bytes(b)


def cmd_run(mode, template_path, plan_path, root):
    plan, b, tc = check(mode, template_path, plan_path)
    root = Path(root).resolve()
    n = ngspice_running()
    if n:
        raise Refused(f"refused: {n} ngspice process(es) running (a child of a stopped driver?)")
    left = processes_on(root)
    if left:
        raise Refused(f"refused: processes still run on {root}: {left[:3]}")
    pf = root / "DRIVER_PID"
    if pf.exists():
        pid = int(pf.read_text().split()[0])
        if pid != os.getpid() and alive(pid):
            raise Refused(f"refused: the driver {pid} of {root} is still running")
    root.mkdir(parents=True, exist_ok=True)
    for sig in (signal.SIGTERM, signal.SIGINT):
        signal.signal(sig, on_signal(root))
    write_once(root / "PLAN_INPUT.json", b)
    write_once(root / "TEMPLATE_CHECK.json", dumps(tc).encode())
    write_once(root / "PLAN_RESOLVED.json", dumps(plan.raw).encode())
    write_once(root / "PLAN.json", dumps(plan.raw).encode())
    env_sha = set_env(plan.raw, root, plan.campaign)
    build = build_kernel(root)
    env_add = dict(LAYERED_ENV_SHA256=env_sha, LAYERED_KERNEL_BUILD=str(build))
    os.environ.update(env_add)                        # the children's environment: these two added, nothing else
    trees = check_trees(plan.raw)
    (root / "trees.json").write_text(dumps(trees))
    m = Machine(plan, root, env_add)
    insts = [Instance(m, g, seed) for g, gp in plan.groups.items() for seed in gp["seeds"]]
    controls, chain_done, errors = dict(U=[], duplicate=[]), set(), []
    with cf.ThreadPoolExecutor(max_workers=64) as ex:  # room for every job: the core budget is the limit
        live = {ex.submit(i.chain): ("chain", i) for i in insts}
        while live:
            done, _ = cf.wait(live, return_when=cf.FIRST_COMPLETED)
            for f in done:
                kind, i = live.pop(f)
                try:
                    r = f.result()
                except BaseException as e:             # reported, never retried; the other jobs go on
                    errors.append(dict(job=kind, instance=i.dir.name, error=repr(e)))
                    continue
                if kind == "chain":
                    chain_done.add(i.dir.name)
                    if r:
                        for n in range(1, plan.rounds + 1):
                            live[ex.submit(i.round, n)] = ("round", i)
                    group = [x for x in insts if x.group == i.group]
                    if all(x.dir.name in chain_done for x in group):
                        el = sorted((x for x in group if (x.dir / "D" / "prediction.json").exists() and
                                     json.loads((x.dir / "D" / "prediction.json").read_text())["eligible_K0"]),
                                    key=lambda x: x.seed)
                        if el:
                            live[ex.submit(untrained, m, el[0])] = ("U", el[0])
                elif kind == "U":
                    controls["U"].append(r)
    summ = [i.summary() for i in insts]
    groups = {}
    for s_ in summ:
        g = groups.setdefault(s_["group"], dict(instances=0, longest_instance_s=0))
        g["instances"] += 1
        g["longest_instance_s"] = max(g["longest_instance_s"], s_["critical_path"]["total_s"])
    controls["U"].sort(key=lambda x: x["instance"])
    # The instances' part of the result, written and hashed before any remote duplicate waits: it never depends on
    # another machine. RESULT.json repeats it at the end.
    part = dict(trees=trees, instances=summ, controls=controls, critical_path_per_group=groups, job_errors=errors,
                stopped_for_disk=list(m.held), campaign=plan.campaign)
    (root / "RESULT_INSTANCES.json").write_text(dumps(part))
    inst_files = sorted(p for p in root.glob("*/SHA256SUMS") if not p.parent.name.startswith("DUPX_"))
    inst_files += sorted(root.glob("U_*/untrained.json")) + [root / "RESULT_INSTANCES.json", root / "PLAN.json",
                                                              root / "trees.json"]
    (root / "SHA256SUMS.instances").write_text("".join(f"{sha(p)}  {p.relative_to(root)}\n" for p in inst_files))
    (root / "INSTANCES_DONE").write_text(f"{now()} {plan.campaign['mode']}\n")
    dups = [remote_duplicate(m, x) for x in plan.duplicates]
    for d in sorted(root.glob("DUPX_*")):
        files = sorted(p for p in d.rglob("*.json"))
        files += [p for p in (d / "N0" / "input.spice", d / "seal" / "SHA256SUMS") if p.exists()]
        (d / "SHA256SUMS").write_text("".join(f"{sha(p)}  {p.relative_to(d)}\n" for p in sorted(set(files))))
    result = dict(trees=trees, instances=summ, controls=controls, critical_path_per_group=groups, job_errors=errors,
                  core_budget=dict(cores=m.budget.cores, peak_in_use=m.budget.peak, written="after every job"),
                  end_held_until_every_job=True, remote_duplicates=dups, stopped_for_disk=m.held,
                  campaign=plan.campaign)
    (root / "RESULT.json").write_text(dumps(result))
    (root / "SHA256SUMS").write_text("".join(f"{sha(p)}  {p.relative_to(root)}\n" for p in top_files(root)))
    (root / "INVENTORY_END").write_text(inventory())
    (root / "DONE").write_text(f"{now()} {plan.campaign['mode']}\n")
    return True


def detach(mode, template_path, plan_path, root, logname):
    log = (root / logname).open("w")
    p = subprocess.Popen(["nohup", PY, "-B", str(HERE / "campaign.py"), "run", mode, str(Path(template_path).resolve()),
                          str(Path(plan_path).resolve()), str(root)], stdout=log, stderr=subprocess.STDOUT,
                         stdin=subprocess.DEVNULL, start_new_session=True, cwd=HERE)
    (root / "DRIVER_PID").write_text(f"{p.pid}\n")
    with (root / "DRIVER_PIDS.log").open("a") as fh:
        fh.write(f"{now()} {p.pid} {logname}\n")
    print(f"launched pid {p.pid}")
    return True


def cmd_launch(mode, template_path, plan_path, root):
    plan, b, tc = check(mode, template_path, plan_path)      # refused before anything is written
    have = free_gb(root)
    if have < plan.launch_gb:
        raise Refused(f"refused: {have:.1f} GB free at launch, {plan.launch_gb:g} GB needed (disk_launch_gb)")
    bad = [k for k, v in E4.checks().items() if not v["ok"]]
    if bad:
        raise Refused("refused: envcheck_layered4 fails: " + ", ".join(bad))
    root = Path(root).resolve()
    n = ngspice_running()
    if n:
        raise Refused(f"refused: {n} ngspice process(es) running")
    if root.exists() and any(root.iterdir()):
        raise Refused(f"refused: {root} exists and is not empty (no run folders before a launch)")
    root.mkdir(parents=True, exist_ok=True)
    (root / "INVENTORY_START").write_text(inventory(json.loads(b)))
    (root / "DISK_AT_LAUNCH.json").write_text(json.dumps(dict(free_gb=round(have, 2), required_gb=plan.launch_gb)) + "\n")
    return detach(mode, template_path, plan_path, root, "driver.log")


def cmd_resume(mode, template_path, plan_path, root):
    """A detached `run` on an existing OUTROOT, after a stop. Same refusals as `run` (another driver alive, ngspice
    running); a DONE of the earlier run is moved aside so that `wait` waits for this one."""
    check(mode, template_path, plan_path)
    root = Path(root).resolve()
    if not (root / "PLAN_INPUT.json").exists():
        raise Refused(f"refused: {root} was never launched (no PLAN_INPUT.json)")
    pf = root / "DRIVER_PID"
    if pf.exists() and alive(int(pf.read_text().split()[0])):
        raise Refused(f"refused: the driver {pf.read_text().split()[0]} of {root} is still running")
    n = ngspice_running()
    if n:
        raise Refused(f"refused: {n} ngspice process(es) running (a child of a stopped driver?)")
    left = processes_on(root)
    if left:
        raise Refused(f"refused: processes still run on {root}: {left[:3]}")
    k = len(list(root.glob("driver_resume_*.log"))) + 1
    if (root / "DONE").exists():
        os.replace(root / "DONE", root / f"DONE.before_resume_{k}")
    return detach(mode, template_path, plan_path, root, f"driver_resume_{k}.log")


def cmd_steps(mode, template_path, plan_path, root, *rest):
    """No-run mode: every step of every instance, as the run would start it, without running anything. The room and
    eligibility that stage D would decide are given (room=yes|no, eligible=yes|no)."""
    kw = dict(a.split("=", 1) for a in rest)
    room, eligible = kw["room"] == "yes", kw["eligible"] == "yes"
    plan, b, tc = check(mode, template_path, plan_path)
    root = Path(root).resolve()
    env_add = ["LAYERED_ENV_SHA256", "LAYERED_KERNEL_BUILD"]
    m = Machine.__new__(Machine)
    m.plan, m.root = plan, root
    rows = []

    def row(inst, name, argv, outs, kind, cwd, cores):
        rows.append(dict(instance=inst, step=name, argv=[str(a) for a in argv], cwd=str(cwd), env_added=env_add,
                         outputs=outs, time_limit_s=plan.limits[kind], guarded=kind != "C", cores=cores))
    for g, gp in plan.groups.items():
        spec = specmod.load(HERE / gp["spec"])
        for seed in gp["seeds"]:
            i = Instance.__new__(Instance)
            i.m, i.plan, i.group, i.seed = m, plan, g, int(seed)
            i.spec_path, i.s, i.audited = Path(gp["spec"]), spec, int(seed) in gp["d4_audit"]
            i.dir = root / f"{spec['tag']}_{seed}"
            for st in i.steps_chain():
                row(i.dir.name, *st)
            for n in [0] + (list(range(1, plan.rounds + 1)) if room else []):
                for st in i.steps_round(n, ("<seal commit>", plan.branch)):
                    row(i.dir.name, *st)
        if g in plan.u_groups and eligible:
            seed = sorted(gp["seeds"])[0]
            d = root / f"U_{spec['tag']}_{seed}"
            rows.append(dict(instance=d.name, step="U", argv=[str(a) for a in [
                PY, "-B", plan.nz / "controls4.py", "untrained", HERE / gp["spec"], d / "U", seed,
                f"seal_log=<seal commit>", f"seal_branch={plan.branch}", f"overlay={plan.overlay}"]],
                cwd=str(plan.nz), env_added=env_add, outputs=["U/untrained_record.json"],
                time_limit_s=plan.limits["U"], guarded=True, cores=0))
    for x in plan.duplicates:
        s = specmod.load(HERE / x["spec"])
        d = root / f"DUPX_{s['tag']}_{x['seed']}"
        rows.append(dict(instance=d.name, step="N0", argv=[str(a) for a in [
            PY, "-B", plan.nz / "controls4.py", "stagen", HERE / x["spec"], d / "N0", x["seed"], 0,
            "seal_log=<home seal commit>", f"seal_branch={x['home_branch']}", f"overlay={plan.overlay}"]],
            cwd=str(plan.nz), env_added=env_add, outputs=["N0/noisy_record.json"], time_limit_s=plan.limits["dup"],
            guarded=True, cores=1))
        rows.append(dict(instance=d.name, step="C0", argv=[str(a) for a in [
            PY, "-B", HERE / "compare_d2.py", d / "seal", HERE / x["spec"], d / "N0" / "noisy_record.json", "noiseless",
            d / "N0" / "comparison.json"]], cwd=str(HERE), env_added=env_add, outputs=["N0/comparison.json"],
            time_limit_s=plan.limits["C"], guarded=False, cores=0))
    for r in rows:
        print(json.dumps(r, sort_keys=True))
    return True


def cmd_check(mode, template_path, plan_path):
    try:
        _, _, tc = check(mode, template_path, plan_path)
    except Refused as e:
        print(json.dumps(dict(ok=False, why=str(e))))
        return False
    print(json.dumps(tc, sort_keys=True))
    return True


def alive(pid):
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False


def cmd_status(root):
    for p in sorted(Path(root).glob("*/status.json")):
        st = json.loads(p.read_text())
        print(p.parent.name, {k: v["status"] for k, v in sorted(st["steps"].items())})


def cmd_wait(root, seconds=str(WAIT_MAX_S)):
    root = Path(root)
    limit = min(float(seconds), WAIT_MAX_S)
    pid = int((root / "DRIVER_PID").read_text())
    t0 = time.time()
    while time.time() - t0 < limit and alive(pid) and not (root / "DONE").exists():
        time.sleep(5)
    cmd_status(root)
    ended = (root / "DONE").exists() or not alive(pid)
    print("ENDED" if ended else "RUNNING", "DONE" if (root / "DONE").exists() else "",
          "INSTANCES_DONE" if (root / "INSTANCES_DONE").exists() else "")
    return ended


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c == "run" and len(a) == 4:
        sys.exit(0 if cmd_run(*a) else 1)
    elif c == "launch" and len(a) == 4:
        sys.exit(0 if cmd_launch(*a) else 1)
    elif c == "resume" and len(a) == 4:
        sys.exit(0 if cmd_resume(*a) else 1)
    elif c == "steps" and len(a) >= 4:
        sys.exit(0 if cmd_steps(*a) else 1)
    elif c == "check" and len(a) == 3:
        sys.exit(0 if cmd_check(*a) else 1)
    elif c == "wait":
        sys.exit(0 if cmd_wait(*a) else 3)
    elif c == "status":
        cmd_status(*a)
    else:
        sys.exit(__doc__)
