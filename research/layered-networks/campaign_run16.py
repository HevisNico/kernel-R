"""campaign_run15.py with 40 GB at launch and the comparisons exempt from the disk guard (the owner's decision on D3,
relayed 2026-11-26). Development only. campaign_run15.py is kept as it is.

**The template.** TEMPLATE_CAMPAIGN_4.json, pinned here by its sha256. It is template 3 with:
- disk_launch_gb 40;
- disk_guard_exempt naming the comparisons;
- disk_guard_gb unchanged at 20.

The checks are campaign_run15's against this template: the shared fields, the trees by commit, and the remote duplicates
with their home branch. Templates 1–3, and plans made from them, are refused.

**The disk guard.**
- **Exempt:** the comparison steps C<n> (name C followed by digits, kind "C"), and only those. They start whatever the
  free space. Each comparison is followed by the deletion of its round's raw, once the comparison agrees and after the
  digest and the extract are written, so it frees disk and cannot be what fills it.
- **Each exempt start below the guard** is logged in OUTROOT/GUARD_EXEMPT.json: the step, the instance, the free space.
- **Still guarded,** as in campaign_run5: deck, inverters, stage D, seal, sealpush, the N rounds, U and the duplicates.
  Below disk_guard_gb they do not start, and RESULT.json lists them under stopped_for_disk.

**At launch:** at least disk_launch_gb (40) GB free, or the launch is refused before anything is written.

  campaign_run16.py launch PLAN.json OUTROOT [jobs=4] [template=FILE]
  campaign_run16.py run    PLAN.json OUTROOT [jobs=4] [template=FILE]     (what launch starts)
  campaign_run16.py check  PLAN.json [template=FILE]
  campaign_run16.py wait | status ...
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
import campaign_run4 as C4  # noqa: E402
import campaign_run5 as C5  # noqa: E402
import campaign_run9 as C9  # noqa: E402
import campaign_run10 as C10  # noqa: E402
import campaign_run12 as C12  # noqa: E402
import campaign_run13 as C13  # noqa: E402
import campaign_run14 as C14  # noqa: E402
import campaign_run15 as C15  # noqa: E402

TEMPLATE = HERE / "TEMPLATE_CAMPAIGN_4.json"
TEMPLATE_SHA256 = "703e8b8aed03c5769475392e96577931b2469ab0212e084d529988dbb8b393e0"
Refused = C13.Refused
EXEMPT = re.compile(r"C\d+")
_LOCK = threading.Lock()


def load_template(path=None):
    saved = C13.TEMPLATE, C13.TEMPLATE_SHA256
    C13.TEMPLATE, C13.TEMPLATE_SHA256 = TEMPLATE, TEMPLATE_SHA256
    try:
        t, tc = C13.load_template(path)
    finally:
        C13.TEMPLATE, C13.TEMPLATE_SHA256 = saved
    tc["driver"] = "campaign_run16.py"
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


# ------------------------------------------------------------------------------------------------ the guard's exemption

_c5_step = C5.Instance.step


def step(self, name, argv, outputs, kind, cwd=CR.HERE, env=None):
    if kind == "C" and EXEMPT.fullmatch(name):
        if self.done(name):
            return True
        ok, free = C5.disk_ok()
        if not ok:
            root = C5.STATE["root"]
            with _LOCK:
                f = Path(root) / "GUARD_EXEMPT.json"
                log = json.loads(f.read_text()) if f.exists() else []
                log.append(dict(instance=self.dir.name, step=name, free_gb=free, guard_gb=C5.STATE["guard_gb"]))
                f.write_text(json.dumps(log, indent=1, sort_keys=True) + "\n")
        return C4.Instance.step(self, name, argv, outputs, kind, cwd, env)   # campaign_run5's step without its guard
    return _c5_step(self, name, argv, outputs, kind, cwd, env)


# ------------------------------------------------------------------------------------------------ run and launch

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
    C9.drop_raw, C10.remote_duplicate, C5.Instance.step = C14.drop_raw, C15.remote_duplicate, step
    try:
        return C12.cmd_run(str(rp), str(root), *rest)
    finally:
        C9.drop_raw, C10.remote_duplicate, C5.Instance.step = C14._c9_drop_raw, C15._c10_remote_duplicate, _c5_step


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
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run16.py"), "run", str(Path(plan_path).resolve()),
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
