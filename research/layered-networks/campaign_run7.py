"""campaign_run6.py on controls4 / controls5 and the noise4 inverter budget (the coordinator's relay of 2026-11-25).
Development only. campaign_run6.py and the earlier drivers are kept as they are; the kit is unchanged.

What changes:
- **Stage N** (PLAN `stagen`: "controls4") runs `controls4.py stagen ... seal_log=... seal_branch=...`
  (research/layered-networks ee58b78 / 458bc7a).
  - It is controls3's sealed noise3 run, with the trace written. The step therefore requires noisy_record.json AND
    trace.digest.json, and each trace.raw is deleted by campaign_run5's rule (agrees: deleted; otherwise kept).
- **One round** (PLAN `save_ref_round`: n, for the dry run only) runs `controls5.py stagen ... save_ref=1`.
  - The trace then also holds each inverter's comparator reference.
  - The record carries `saved_ref` and is otherwise controls4's.
- **U and the duplicates** run under the same tool (controls4), with the seal logs of campaign_run6.
- **The inverter gate** (front-end groups) runs through indeck_noise4.py. The kit's unchanged gate then receives the
  K3 allowance of noise_tree/research/layered-networks/noise4_budget.json (PLAN `k3_budget`, by default that file).
  - K0 and the R cells are unchanged.
  - The step requires inv/K3_BUDGET.json with `ok: true`: every gate file records exactly that K3 allowance.

  campaign_run7.py launch | run | wait | status ...     as campaign_run6.py
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run5 as C5  # noqa: E402
import campaign_run6 as C6  # noqa: E402

TOOLS = ("controls3", "controls4")


def stagen_argv(plan, nz, sp, out, seed, n, ov):
    tool = plan.get("stagen", "controls2")
    if tool not in TOOLS:
        return C6._stagen_argv(plan, nz, sp, out, seed, n, ov)
    argv = C6.stagen_argv(dict(plan, stagen="controls3"), nz, sp, out, seed, n, ov)     # the seal arguments
    script = "controls4.py"
    extra = []
    if plan.get("save_ref_round") is not None and int(n) == int(plan["save_ref_round"]) and not Path(out).parent.name.startswith(("DUP_", "DUPX_")):
        script, extra = "controls5.py", ["save_ref=1"]
    if tool == "controls3":
        script, extra = "controls3.py", []
    argv[2] = nz / script
    return argv + extra


def untrained_with(root, inst, plan, script):
    d = Path(root) / f"U_{inst.dir.name}"
    res_path = d / "untrained.json"
    if res_path.exists():
        return json.loads(res_path.read_text())
    d.mkdir(exist_ok=True)
    s = C6.seal_of(inst.dir)
    commit, branch = s if s else ("", "")
    rc, cpu, to = CR.run_child([CR.PY, "-B", script, "untrained", HERE / inst.spec_path, d / "U", inst.seed,
                                f"seal_log={commit}", f"seal_branch={branch}",
                                f"overlay={plan.get('overlay', 'config_inverter_c5.json')}"], script.parent, d / "U.log",
                               CR.DEFAULT_TIMEOUT["U"])
    res = dict(instance=inst.dir.name, exit=rc, timed_out=to, cpu_s=cpu, seal_log=dict(commit=commit, branch=branch),
               tool=script.name)
    rec_path = d / "U" / "untrained_record.json"
    if rc == 0 and not to and rec_path.exists():
        rec = json.loads(rec_path.read_text())
        fired = [dict(slot=i, cell=f"c{r['layer']}_{r['index']}") for i in rec["tests"]
                 for r in rec["slots"][i]["reads"] if r["emission"] is not None]
        inv = [dict(slot=i, inverter=j) for i in rec["tests"] for j, v in enumerate(rec["slots"][i].get("inv", []))
               if v.get("emission") is not None]
        res.update(patterns=len(rec["tests"]), r_cell_fires=fired, inverter_fires_reported=inv, ok=not fired,
                   record_seal_log=rec.get("seal_log"))
    else:
        res["ok"] = False
    CR.drop_raw(d / "U")
    res_path.write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    return res


class Instance(C6.Instance):
    def step(self, name, argv, outputs, kind, cwd=HERE, env=None):
        plan = self.plan
        if name == "inverters":                            # the noise4 K3 budget, through the wrapper
            pkg = Path(plan["kit_tree"]) / "research" / "circuit" / "inverter" / "instances"
            budget = Path(plan.get("k3_budget") or Path(plan["noise_tree"]) / "research" / "layered-networks" / "noise4_budget.json")
            argv = [CR.PY, "-B", HERE / "indeck_noise4.py", pkg, budget, *argv[3:]]
            outputs = list(outputs) + ["inv/K3_BUDGET.json"]
            ok = super().step(name, argv, outputs, kind, HERE, env)
            if ok and not json.loads((self.dir / "inv" / "K3_BUDGET.json").read_text()).get("ok"):
                return False
            return ok
        if plan.get("stagen") == "controls4" and name.startswith("N") and name[1:].isdigit():
            outputs = list(outputs) + (["N%s/trace.digest.json" % name[1:]] if f"{name}/trace.digest.json" not in outputs else [])
        return super().step(name, argv, outputs, kind, cwd, env)


def cmd_run(plan_path, root, *rest):
    C6.PLAN.clear()
    C6.PLAN.update(json.loads(Path(plan_path).read_text()))
    saved = CR.untrained, CR.stagen_argv, C6.Instance, C5.Instance
    CR.untrained = lambda r, inst, p: untrained_with(r, inst, C6.PLAN, Path(C6.PLAN["noise_tree"]) / "research" / "layered-networks"
                                                     / ("controls4.py" if C6.PLAN.get("stagen") == "controls4" else "controls3.py"))
    CR.stagen_argv = lambda plan, nz, sp, out, seed, n, ov: stagen_argv(C6.PLAN, nz, sp, out, seed, n, ov)
    C5.Instance = Instance
    try:
        return C5.cmd_run(plan_path, root, *rest)
    finally:
        CR.untrained, CR.stagen_argv, C6.Instance, C5.Instance = saved


def cmd_launch(plan_path, root, *rest):
    import subprocess
    root = Path(root).resolve()
    n = subprocess.run(["pgrep", "-c", "ngspice"], capture_output=True, text=True).stdout.strip()
    if n not in ("", "0"):
        raise SystemExit(f"refused: {n} ngspice process(es) running")
    if root.exists() and any(root.iterdir()):
        raise SystemExit(f"refused: {root} exists and is not empty (no run folders before a launch)")
    plan = json.loads(Path(plan_path).read_text())
    root.mkdir(parents=True, exist_ok=True)
    (root / "INVENTORY_START").write_text(C2.inventory(plan))
    log = (root / "driver.log").open("w")
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run7.py"), "run", str(Path(plan_path).resolve()),
                          str(root), *rest], stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                         start_new_session=True, cwd=HERE)
    (root / "DRIVER_PID").write_text(f"{p.pid}\n")
    print(f"launched pid {p.pid}")
    return True


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c == "run":
        sys.exit(0 if cmd_run(*a) else 1)
    elif c == "launch":
        sys.exit(0 if cmd_launch(*a) else 1)
    elif c == "wait":
        sys.exit(0 if C2.cmd_wait(*a) else 3)
    elif c == "status":
        C2.cmd_status(*a)
    else:
        sys.exit(__doc__)
