"""campaign_run12.py behind the pinned campaign template (the owner's item 2, relayed 2026-11-26). Development only.
campaign_run12.py and the earlier drivers are kept as they are.

**The template.** TEMPLATE_CAMPAIGN.json, pinned here by its sha256 (TEMPLATE_SHA256) and in FREEZE_PINS_2.json, holds
the fields every machine's plan shares. launch and run refuse, before anything is written, when the plan:
- lacks a key of the template, or gives a different value for one (seal_push is compared without its per-machine
  `branch`);
- has a key outside the template and outside the per-machine keys of plan_split2.py (PER_MACHINE). So `save_ref_round`,
  `steps_until`, `k3_budget` and the tree paths `kit_tree` / `noise_tree` are refused;
- has a malformed per-machine part: seal_push.branch not evidence/combined-seals-K<nn>, a keep_raw entry that is not an
  instance of this plan, or a d4_audit seed that is not among its group's seeds.

**Trees by commit.** The plan gives kit_commit and noise_commit only (full hashes). Each tree is the clean worktree of
this repository whose HEAD is exactly that commit; with several, the first by path. None is a refusal. The inverter K3
budget is that noise tree's research/layered-networks/noise4_budget.json, and its sha256 must be the template's
k3_budget_sha256. The resolved plan (the input plus kit_tree and noise_tree) is OUTROOT/PLAN.json, through
campaign_run12; the input plan is kept byte for byte as OUTROOT/PLAN_INPUT.json and the check as TEMPLATE_CHECK.json.

**A rehearsal** may pass `template=FILE`. It is accepted only when FILE differs from the pinned template in
seal_push.remote alone (a local bare repository instead of GitHub). TEMPLATE_CHECK.json then records rehearsal true,
the file's sha256 and the difference.

  campaign_run13.py launch PLAN.json OUTROOT [jobs=4] [template=FILE]
  campaign_run13.py run    PLAN.json OUTROOT [jobs=4] [template=FILE]     (what launch starts)
  campaign_run13.py check  PLAN.json [template=FILE]                      the check alone, as JSON; exit 1 if refused
  campaign_run13.py wait | status ...                                     as campaign_run12.py
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run12 as C12  # noqa: E402
import spec as specmod  # noqa: E402

TEMPLATE = HERE / "TEMPLATE_CAMPAIGN.json"
TEMPLATE_SHA256 = "c812cc28fef38a36d8ea030ec94d2c0705d6bdbc398e495af2bb29c3dc1c5698"
PER_MACHINE = {"what", "groups", "U_groups", "remote_duplicates", "controls", "keep_raw"}   # set by plan_split2.py
BRANCH = re.compile(r"evidence/combined-seals-K\d{2}")


class Refused(SystemExit):
    pass


def sha_bytes(b):
    return hashlib.sha256(b).hexdigest()


def load_template(path=None):
    """(template, check): the pinned template, or a rehearsal one that differs from it in seal_push.remote only."""
    pinned_b = TEMPLATE.read_bytes()
    if sha_bytes(pinned_b) != TEMPLATE_SHA256:
        raise Refused(f"refused: {TEMPLATE.name} is {sha_bytes(pinned_b)[:12]}, not the pinned {TEMPLATE_SHA256[:12]}")
    pinned = json.loads(pinned_b)
    if path is None or Path(path).resolve() == TEMPLATE.resolve():
        return pinned, dict(template=TEMPLATE.name, template_sha256=TEMPLATE_SHA256, rehearsal=False)
    b = Path(path).read_bytes()
    t = json.loads(b)
    a = dict(pinned, seal_push=dict(pinned["seal_push"], remote=None), what=None)
    c = dict(t, seal_push=dict(t.get("seal_push") or {}, remote=None), what=None)
    if a != c:
        diff = sorted(k for k in set(a) | set(c) if a.get(k) != c.get(k))
        raise Refused(f"refused: template {path} differs from the pinned template beyond seal_push.remote: {diff}")
    return t, dict(template=str(path), template_sha256=sha_bytes(b), pinned_sha256=TEMPLATE_SHA256, rehearsal=True,
                   differs=dict(seal_push_remote=dict(pinned=pinned["seal_push"]["remote"], used=t["seal_push"]["remote"])))


def check_plan(plan, template):
    """The refusals, as a list of reasons (empty: the plan agrees with the template)."""
    bad = []
    for k in sorted(template):
        if k == "what":
            continue
        if k not in plan:
            bad.append(f"missing key {k}")
        elif k == "seal_push":
            sp = {x: y for x, y in (plan[k] or {}).items() if x != "branch"}
            if sp != template[k]:
                bad.append(f"seal_push {sp} differs from the template's {template[k]}")
        elif plan[k] != template[k]:
            bad.append(f"{k} is {plan[k]!r}, the template's is {template[k]!r}")
    for k in sorted(set(plan) - set(template) - PER_MACHINE):
        bad.append(f"key {k} is not allowed (neither in the template nor per machine)")
    for k in sorted(PER_MACHINE - {"what"} - set(plan)):
        bad.append(f"missing per-machine key {k}")
    if not BRANCH.fullmatch(str((plan.get("seal_push") or {}).get("branch"))):
        bad.append(f"seal_push.branch {(plan.get('seal_push') or {}).get('branch')!r} is not evidence/combined-seals-K<nn>")
    names = set()
    for g, v in (plan.get("groups") or {}).items():
        tag = specmod.load(HERE / v["spec"])["tag"]
        names |= {f"{tag}_{s}" for s in v.get("seeds", [])}
        extra = sorted(set(v.get("d4_audit", [])) - set(v.get("seeds", [])))
        if extra:
            bad.append(f"{g}: d4_audit seeds {extra} are not among its seeds")
    extra = sorted(set(plan.get("keep_raw") or []) - names)
    if extra:
        bad.append(f"keep_raw {extra} are not instances of this plan")
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


def resolve_trees(plan, template, trees=None):
    trees = worktrees() if trees is None else trees
    res = {}
    for key, ck in (("kit_tree", "kit_commit"), ("noise_tree", "noise_commit")):
        commit = plan[ck]
        if not re.fullmatch(r"[0-9a-f]{40}", commit):
            raise Refused(f"refused: {ck} {commit!r} is not a full commit hash")
        found = [p for p, h in trees if h == commit and CR.git_head(p)[1]]
        if not found:
            raise Refused(f"refused: no clean worktree at {ck} {commit[:12]} (git worktree add --detach DIR {commit})")
        res[key] = found[0]
    budget = Path(res["noise_tree"]) / "research" / "layered-networks" / "noise4_budget.json"
    if not budget.exists() or CR.sha(budget) != template["k3_budget_sha256"]:
        raise Refused(f"refused: {budget} is not the template's k3_budget_sha256 {template['k3_budget_sha256'][:12]}")
    return res


def check(plan_path, template_path=None):
    template, tc = load_template(template_path)
    b = Path(plan_path).read_bytes()
    plan = json.loads(b)
    bad = check_plan(plan, template)
    if bad:
        raise Refused("refused: the plan differs from the template: " + "; ".join(bad))
    trees = resolve_trees(plan, template)
    tc.update(plan_input_sha256=sha_bytes(b), trees=trees, k3_budget_sha256=template["k3_budget_sha256"], ok=True)
    return plan, b, dict(plan, **trees), tc


def opts(rest):
    kw = dict(a.split("=", 1) for a in rest if "=" in a)
    return kw.pop("template", None), [a for a in rest if not a.startswith("template=")]


def write_once(p, b):
    if p.exists():
        if p.read_bytes() != b:
            raise Refused(f"refused: {p} differs (OUTROOT was started with another plan or template)")
    else:
        p.write_bytes(b)


def cmd_run(plan_path, root, *rest):
    tpl, rest = opts(rest)
    plan, b, resolved, tc = check(plan_path, tpl)
    root = Path(root).resolve()
    root.mkdir(parents=True, exist_ok=True)
    write_once(root / "PLAN_INPUT.json", b)
    write_once(root / "TEMPLATE_CHECK.json", (json.dumps(tc, indent=1, sort_keys=True) + "\n").encode())
    rp = root / "PLAN_RESOLVED.json"
    write_once(rp, (json.dumps(resolved, indent=1, sort_keys=True) + "\n").encode())
    return C12.cmd_run(str(rp), str(root), *rest)


def cmd_launch(plan_path, root, *rest):
    tpl, _ = opts(rest)
    check(plan_path, tpl)                                    # refused before anything is written
    C12.refuse_unless_env()
    root = Path(root).resolve()
    n = subprocess.run(["pgrep", "-c", "ngspice"], capture_output=True, text=True).stdout.strip()
    if n not in ("", "0"):
        raise Refused(f"refused: {n} ngspice process(es) running")
    if root.exists() and any(root.iterdir()):
        raise Refused(f"refused: {root} exists and is not empty (no run folders before a launch)")
    plan = json.loads(Path(plan_path).read_text())
    root.mkdir(parents=True, exist_ok=True)
    (root / "INVENTORY_START").write_text(C2.inventory(plan))
    log = (root / "driver.log").open("w")
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run13.py"), "run", str(Path(plan_path).resolve()),
                          str(root), *rest], stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                         start_new_session=True, cwd=HERE)
    (root / "DRIVER_PID").write_text(f"{p.pid}\n")
    print(f"launched pid {p.pid}")
    return True


def cmd_check(plan_path, *rest):
    tpl, _ = opts(rest)
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
