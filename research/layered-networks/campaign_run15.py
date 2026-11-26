"""campaign_run14.py with the remote duplicate waiting for its home's seal and the disk at launch (defects D2 and D3
of the final dry run, the owner's decisions, 2026-11-26). Development only. campaign_run14.py is kept as it is.

**The template.** TEMPLATE_CAMPAIGN_3.json, pinned here by its sha256. It is template 2 plus:
- `duplicate_wait`: {interval_s, limit_s} = {60, 21600};
- `disk_launch_gb`: 30.

The template check is campaign_run13's, against this template; a rehearsal `template=FILE` may differ in
seal_push.remote alone. Templates 1 and 2, and plans made from them, are refused.

**The remote duplicate, with no manual step (D2).** Every `remote_duplicates` entry must carry `home_branch` (written
by plan_split3.py): evidence/combined-seals-K<nn>, not this machine's own branch. It must also carry `home_instance`
<TAG>_<seed> and no `seal_log` or `seal_dir`. Otherwise the plan is refused. After this machine's own instances, each
duplicate:
1. **waits:** every interval_s it fetches the home branch by name from seal_push.remote and reads SEALS.txt at the
   branch's tip, until a line for the instance exists, for at most limit_s;
2. **then checks and runs, as campaign_run10 does:** the tip commit becomes its seal_log (in the plan's entry in
   memory, which stage N reads; the plan file is not changed), the seal folder is fetched
   from that commit, the SEALS.txt line and the folder are checked, and only then does N0 run;
3. **at the limit:** the duplicate is not completed (ok false, not_completed true, the reason), and nothing runs. A
   later `run` waits again.

Each attempt is logged in DUPX_<inst>/seal_wait.json: the time, the branch tip, and whether the line was found.

**Disk (D3).** launch refuses unless the OUTROOT's filesystem has at least disk_launch_gb (30) GB free. During the run,
the disk guard keeps disk_guard_gb (20) GB, as before: below it, no new step starts.

Everything else is campaign_run14's: the kernel at stage D, the trace extract, keep_raw N0 only.

  campaign_run15.py launch PLAN.json OUTROOT [jobs=4] [template=FILE]
  campaign_run15.py run    PLAN.json OUTROOT [jobs=4] [template=FILE]     (what launch starts)
  campaign_run15.py check  PLAN.json [template=FILE]
  campaign_run15.py wait | status ...
"""
import datetime
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run6 as C6  # noqa: E402
import campaign_run9 as C9  # noqa: E402
import campaign_run10 as C10  # noqa: E402
import campaign_run12 as C12  # noqa: E402
import campaign_run13 as C13  # noqa: E402
import campaign_run14 as C14  # noqa: E402
import spec as specmod  # noqa: E402

TEMPLATE = HERE / "TEMPLATE_CAMPAIGN_3.json"
TEMPLATE_SHA256 = "4963d696d8b951ce7641d05dae3ff4133bdd387f809597aff63b1e1b25f7a618"
Refused = C13.Refused
WAIT = dict(sleep=time.sleep, now=time.time)


def load_template(path=None):
    saved = C13.TEMPLATE, C13.TEMPLATE_SHA256
    C13.TEMPLATE, C13.TEMPLATE_SHA256 = TEMPLATE, TEMPLATE_SHA256
    try:
        t, tc = C13.load_template(path)
    finally:
        C13.TEMPLATE, C13.TEMPLATE_SHA256 = saved
    tc["driver"] = "campaign_run15.py"
    return t, tc


def check_duplicates(plan):
    bad = []
    own = (plan.get("seal_push") or {}).get("branch")
    for x in plan.get("remote_duplicates", []):
        s = specmod.load(HERE / x["spec"])
        inst = f"{s['tag']}_{x['seed']}"
        hb = x.get("home_branch")
        if not hb or not C13.BRANCH.fullmatch(str(hb)):
            bad.append(f"remote duplicate {inst}: no home_branch evidence/combined-seals-K<nn> (plan_split3.py)")
        elif hb == own:
            bad.append(f"remote duplicate {inst}: home_branch is this machine's own branch")
        if x.get("home_instance") != inst:
            bad.append(f"remote duplicate {inst}: home_instance {x.get('home_instance')!r}")
        for k in ("seal_log", "seal_dir"):
            if k in x:
                bad.append(f"remote duplicate {inst}: {k} is not allowed (campaign_run15 finds it)")
    return bad


def check(plan_path, template_path=None):
    template, tc = load_template(template_path)
    b = Path(plan_path).read_bytes()
    plan = json.loads(b)
    bad = C13.check_plan(plan, template) + check_duplicates(plan)
    if bad:
        raise Refused("refused: the plan differs from the template: " + "; ".join(bad))
    trees = C13.resolve_trees(plan, template)
    tc.update(plan_input_sha256=C13.sha_bytes(b), trees=trees, k3_budget_sha256=template["k3_budget_sha256"], ok=True)
    return plan, b, dict(plan, **trees), tc


# ------------------------------------------------------------------------------------------------ the waiting duplicate

def utc():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%fZ")


def probe(remote, branch, inst):
    """(tip, line) of the branch fetched by name: line is the instance's last SEALS.txt line, or None."""
    with tempfile.TemporaryDirectory() as g:
        run = lambda *a: subprocess.run(["git", "-C", g, *a], capture_output=True, text=True)
        run("init", "-q", "--bare")
        if run("fetch", "-q", str(remote), f"refs/heads/{branch}:refs/heads/{branch}").returncode:
            return None, None
        tip = run("rev-parse", f"refs/heads/{branch}").stdout.strip()
        s = run("show", f"{tip}:SEALS.txt")
        lines = [l for l in s.stdout.splitlines() if l.split() and l.split()[0] == inst] if not s.returncode else []
        return tip, (lines[-1] if lines else None)


def wait_for_seal(remote, branch, inst, interval, limit, log_path):
    t0 = WAIT["now"]()
    log = dict(remote=str(remote), branch=branch, instance=inst, interval_s=interval, limit_s=limit, attempts=[])
    while True:
        tip, line = probe(remote, branch, inst)
        log["attempts"].append(dict(utc=utc(), tip=tip, found=line is not None))
        found = line is not None
        waited = WAIT["now"]() - t0
        if found or waited + interval > limit:
            log.update(found=found, commit=tip if found else None, line=line, waited_s=round(waited, 1))
            Path(log_path).write_text(json.dumps(log, indent=1, sort_keys=True) + "\n")
            return tip if found else None
        Path(log_path).write_text(json.dumps(log, indent=1, sort_keys=True) + "\n")
        WAIT["sleep"](interval)


_c10_remote_duplicate = C10.remote_duplicate


def remote_duplicate(root, x, plan):
    s = specmod.load(HERE / x["spec"])
    inst = f"{s['tag']}_{x['seed']}"
    d = Path(root) / f"DUPX_{inst}"
    d.mkdir(parents=True, exist_ok=True)
    if (d / "duplicate_here.json").exists():
        return _c10_remote_duplicate(root, x, plan)        # already run: campaign_run4 returns its result
    w = plan["duplicate_wait"]
    commit = wait_for_seal(plan["seal_push"]["remote"], x["home_branch"], inst, int(w["interval_s"]), int(w["limit_s"]),
                           d / "seal_wait.json")
    if commit is None:
        return dict(instance=inst, group=x["group"], ok=False, not_completed=True,
                    why=f"not completed: no SEALS.txt line for {inst} on {x['home_branch']} within {w['limit_s']} s")
    found = [commit, x["home_branch"]]
    for pl in (plan, C6.PLAN):                             # stage N reads the seal log from the plan's entry
        for y in pl.get("remote_duplicates", []):
            if y["group"] == x["group"] and int(y["seed"]) == int(x["seed"]):
                y["seal_log"] = found
    return _c10_remote_duplicate(root, dict(x, seal_log=found), plan)


# ------------------------------------------------------------------------------------------------ run and launch

def free_gb(path):
    p = Path(path)
    while not p.exists():
        p = p.parent
    return shutil.disk_usage(p).free / 1e9


def cmd_run(plan_path, root, *rest):
    tpl, rest = C13.opts(rest)
    plan, b, resolved, tc = check(plan_path, tpl)
    root = Path(root).resolve()
    root.mkdir(parents=True, exist_ok=True)
    C13.write_once(root / "PLAN_INPUT.json", b)
    C13.write_once(root / "TEMPLATE_CHECK.json", (json.dumps(tc, indent=1, sort_keys=True) + "\n").encode())
    rp = root / "PLAN_RESOLVED.json"
    C13.write_once(rp, (json.dumps(resolved, indent=1, sort_keys=True) + "\n").encode())
    build, _ = C14.build_kernel(root)
    os.environ["LAYERED_KERNEL_BUILD"] = str(build)
    C9.drop_raw, C10.remote_duplicate = C14.drop_raw, remote_duplicate
    try:
        return C12.cmd_run(str(rp), str(root), *rest)
    finally:
        C9.drop_raw, C10.remote_duplicate = C14._c9_drop_raw, _c10_remote_duplicate


def cmd_launch(plan_path, root, *rest):
    tpl, _ = C13.opts(rest)
    plan, _, _, _ = check(plan_path, tpl)                    # refused before anything is written
    need = float(plan["disk_launch_gb"])
    have = free_gb(root)
    if have < need:
        raise Refused(f"refused: {have:.1f} GB free at launch, {need:g} GB needed (disk_launch_gb)")
    C12.refuse_unless_env()
    root = Path(root).resolve()
    n = subprocess.run(["pgrep", "-c", "ngspice"], capture_output=True, text=True).stdout.strip()
    if n not in ("", "0"):
        raise Refused(f"refused: {n} ngspice process(es) running")
    if root.exists() and any(root.iterdir()):
        raise Refused(f"refused: {root} exists and is not empty (no run folders before a launch)")
    root.mkdir(parents=True, exist_ok=True)
    (root / "INVENTORY_START").write_text(C2.inventory(plan))
    (root / "DISK_AT_LAUNCH.json").write_text(json.dumps(dict(free_gb=round(have, 2), required_gb=need)) + "\n")
    log = (root / "driver.log").open("w")
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run15.py"), "run", str(Path(plan_path).resolve()),
                          str(root), *rest], stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                         start_new_session=True, cwd=HERE)
    (root / "DRIVER_PID").write_text(f"{p.pid}\n")
    print(f"launched pid {p.pid}")
    return True


def cmd_check(plan_path, *rest):
    tpl, _ = C13.opts(rest)
    try:
        _, _, _, tc = check(plan_path, tpl)
    except Refused as e:
        print(json.dumps(dict(ok=False, why=str(e))))
        return False
    print(json.dumps(tc, sort_keys=True))
    return True


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c == "run":
        sys.exit(0 if cmd_run(*a) else 1)
    elif c == "launch":
        sys.exit(0 if cmd_launch(*a) else 1)
    elif c == "check":
        sys.exit(0 if cmd_check(*a) else 1)
    elif c == "wait":
        sys.exit(0 if C2.cmd_wait(*a) else 3)
    elif c == "status":
        C2.cmd_status(*a)
    else:
        sys.exit(__doc__)
