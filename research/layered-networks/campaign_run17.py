"""campaign_run16.py with the comparison exemption bound at import, and U and the remote duplicates under the disk guard
(defects D4 and D5 of the end-to-end check of 2026-11-26, the owner's decision). Development only. campaign_run16.py
is kept as it is.

**D4: the recursion.** campaign_run16's exempt step called `C4.Instance.step`, a module attribute. At run time,
campaign_run5.cmd_run sets `C4.Instance` to campaign_run5's own Instance class, whose step campaign_run16 had replaced,
so the call came back to itself (RecursionError at every instance's C0). Here both are taken at import, before any
cmd_run can reassign a module attribute:
- the class whose step is patched: `_C5`, campaign_run5's Instance class;
- the step it falls back to: `_PARENT_STEP` = `_C5.__mro__[1].step`, campaign_run4's Instance.step.

No call goes through an attribute that a cmd_run reassigns.

**D5: U and the duplicates were not guarded.** campaign_run5's guard sits in Instance.step. The untrained control
(campaign_run7.untrained_with) and the remote duplicate (campaign_run4.remote_duplicate) run their child process
directly, so they were never guarded, although campaign_run16 and D3_DECISION.md said they were. Here:
- **U:** campaign_run7.untrained_with, captured at import, is replaced by a guarded version. Below the guard it does
  not run: it returns ok null, held_for_disk true, with the reason; it is listed in RESULT.json stopped_for_disk; and
  nothing is written, so a later run starts it.
- **The remote duplicate:** after its wait for the home's seal line (campaign_run15), and before its N0, it is held
  below the guard the same way. It is then not completed, with the reason, and a later run waits and starts it again.

**The rule** (TEMPLATE_CAMPAIGN_5.json: disk_launch_gb 40, disk_guard_gb 20):
- the comparisons C<n>, and only those, are exempt from the guard;
- every other step is guarded, and so are U and the duplicates.

**The template.** TEMPLATE_CAMPAIGN_5.json is template 4 plus `driver: campaign_run17.py`. campaign_run17 refuses
templates 1–4, and campaign_run16 refuses a plan made from template 5 (the key `driver` is not in template 4).

  campaign_run17.py launch | run | check | wait | status ...     as campaign_run16.py
"""
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import threading

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run5 as C5  # noqa: E402
import campaign_run7 as C7  # noqa: E402
import campaign_run9 as C9  # noqa: E402
import campaign_run10 as C10  # noqa: E402
import campaign_run12 as C12  # noqa: E402
import campaign_run13 as C13  # noqa: E402
import campaign_run14 as C14  # noqa: E402
import campaign_run15 as C15  # noqa: E402
import spec as specmod  # noqa: E402

TEMPLATE = HERE / "TEMPLATE_CAMPAIGN_5.json"
TEMPLATE_SHA256 = "fbf0c7cc020704ff45ed88ebeed322b53990c3abfee7b43b9cf4f0dc0d0f2df2"
Refused = C13.Refused
EXEMPT = re.compile(r"C\d+")
_LOCK = threading.Lock()

# Bound at import, before any cmd_run reassigns a module attribute (D4).
_C5 = C5.Instance                                  # campaign_run5's Instance class
_C5_STEP = _C5.step                                # its guarded step
_PARENT_STEP = _C5.__mro__[1].step                 # campaign_run4's Instance.step: the step without the guard
_C7_UNTRAINED = C7.untrained_with
_C9_DROP = C14._c9_drop_raw
_C10_DUP = C15._c10_remote_duplicate
assert _C5.__mro__[1].__module__ == "campaign_run4", _C5.__mro__


def load_template(path=None):
    saved = C13.TEMPLATE, C13.TEMPLATE_SHA256
    C13.TEMPLATE, C13.TEMPLATE_SHA256 = TEMPLATE, TEMPLATE_SHA256
    try:
        t, tc = C13.load_template(path)
    finally:
        C13.TEMPLATE, C13.TEMPLATE_SHA256 = saved
    tc["driver"] = "campaign_run17.py"
    return t, tc


def check(plan_path, template_path=None):
    template, tc = load_template(template_path)
    b = Path(plan_path).read_bytes()
    plan = json.loads(b)
    bad = C13.check_plan(plan, template) + C15.check_duplicates(plan)
    if bad:
        raise Refused("refused: the plan differs from the template: " + "; ".join(bad))
    trees = C13.resolve_trees(plan, template)
    tc.update(plan_input_sha256=C13.sha_bytes(b), trees=trees, k3_budget_sha256=template["k3_budget_sha256"], ok=True)
    return plan, b, dict(plan, **trees), tc


def log_exempt(inst, name, free):
    with _LOCK:
        f = Path(C5.STATE["root"]) / "GUARD_EXEMPT.json"
        log = json.loads(f.read_text()) if f.exists() else []
        log.append(dict(instance=inst, step=name, free_gb=free, guard_gb=C5.STATE["guard_gb"]))
        f.write_text(json.dumps(log, indent=1, sort_keys=True) + "\n")


def step(self, name, argv, outputs, kind, cwd=CR.HERE, env=None):
    if kind == "C" and EXEMPT.fullmatch(name):
        if self.done(name):
            return True
        ok, free = C5.disk_ok()
        if not ok:
            log_exempt(self.dir.name, name, free)
        return _PARENT_STEP(self, name, argv, outputs, kind, cwd, env)
    return _C5_STEP(self, name, argv, outputs, kind, cwd, env)


def untrained_with(root, inst, plan, script):
    d = Path(root) / f"U_{inst.dir.name}"
    if not (d / "untrained.json").exists():
        ok, free = C5.disk_ok()
        if not ok:
            C5.STATE["held"].append(dict(instance=d.name, step="U", free_gb=free))
            return dict(instance=inst.dir.name, ok=None, held_for_disk=True,
                        why=f"held: {free} GB free, below the {C5.STATE['guard_gb']} GB guard")
    return _C7_UNTRAINED(root, inst, plan, script)


def remote_duplicate(root, x, plan):
    s = specmod.load(HERE / x["spec"])
    inst = f"{s['tag']}_{x['seed']}"
    d = Path(root) / f"DUPX_{inst}"
    d.mkdir(parents=True, exist_ok=True)
    if (d / "duplicate_here.json").exists():
        return _C10_DUP(root, x, plan)
    w = plan["duplicate_wait"]
    commit = C15.wait_for_seal(plan["seal_push"]["remote"], x["home_branch"], inst, int(w["interval_s"]),
                               int(w["limit_s"]), d / "seal_wait.json")
    if commit is None:
        return dict(instance=inst, group=x["group"], ok=False, not_completed=True,
                    why=f"not completed: no SEALS.txt line for {inst} on {x['home_branch']} within {w['limit_s']} s")
    ok, free = C5.disk_ok()
    if not ok:
        C5.STATE["held"].append(dict(instance=d.name, step="N0", free_gb=free))
        return dict(instance=inst, group=x["group"], ok=False, not_completed=True, held_for_disk=True,
                    why=f"not completed: held, {free} GB free, below the {C5.STATE['guard_gb']} GB guard")
    found = [commit, x["home_branch"]]
    for pl in (plan, C15.C6.PLAN):                         # stage N reads the seal log from the plan's entry
        for y in pl.get("remote_duplicates", []):
            if y["group"] == x["group"] and int(y["seed"]) == int(x["seed"]):
                y["seal_log"] = found
    return _C10_DUP(root, dict(x, seal_log=found), plan)


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
    saved = C9.drop_raw, C10.remote_duplicate, C7.untrained_with
    C9.drop_raw, C10.remote_duplicate, C7.untrained_with = C14.drop_raw, remote_duplicate, untrained_with
    _C5.step = step
    try:
        return C12.cmd_run(str(rp), str(root), *rest)
    finally:
        C9.drop_raw, C10.remote_duplicate, C7.untrained_with = saved
        _C5.step = _C5_STEP


def cmd_launch(plan_path, root, *rest):
    tpl, _ = C13.opts(rest)
    plan, _, _, _ = check(plan_path, tpl)                    # refused before anything is written
    need = float(plan["disk_launch_gb"])
    have = C15.free_gb(root)
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
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run17.py"), "run", str(Path(plan_path).resolve()),
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
