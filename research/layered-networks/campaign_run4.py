"""campaign_run3.py with the seal push and the campaign's per-machine plan entries (PREDICTION draft, 2026-11-24).
Development only. campaign_run3.py is pushed and kept as it is.

Added to each instance's chain, between `seal` and `N0`:
  sealpush   sealpush.py push: one line (instance, seal sha256, UTC time) appended to the machine's log branch
             (PLAN `seal_push`: {"remote", "branch", "dry"}), pushed; output seal_push.json. Stage N starts only when
             this step is done; a failed push stops the instance there ("not sealed"). With "dry": true nothing is
             pushed and the analysis counts the instance as not sealed.
PLAN entries (written by plan_split.py):
  groups[g]["d4_audit"]   seeds whose stage D runs with its own solo scans (stage_d.py solo=1: the D4 audit)
  U_groups                the groups whose U control runs on this machine (default: every group of the plan)
  remote_duplicates       [{group, spec, seed}]: an instance of another machine whose N0 is run again here, in
                          OUTROOT/DUPX_<TAG>_<seed>/N0 (the duplicate on a second machine; the analysis compares the two)

  campaign_run4.py launch | run | wait | status ...     as campaign_run3.py
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run3 as C3  # noqa: E402
import spec as specmod  # noqa: E402


SEAL_LOCK = C3.threading.Lock()


class Instance(C3.Instance):
    def step(self, name, argv, outputs, kind, cwd=HERE, env=None):
        if name != "sealpush":
            return super().step(name, argv, outputs, kind, cwd, env)
        with SEAL_LOCK:                                 # one work clone and one branch per machine: one push at a time
            return super().step(name, argv, outputs, kind, cwd, env)

    def chain(self):
        s, d, plan, seed = self.s, self.dir, self.plan, self.seed
        ov = plan.get("overlay", "config_inverter_c5.json")
        sp = HERE / self.spec_path
        sd = HERE / plan.get("stage_d_script", "stage_d5.py")
        ok = self.step("deck", [CR.PY, "-B", sd, "deck", sp, d / "deck.spice", f"overlay={ov}"], ["deck.spice"], "deck")
        if ok and s["front"]:
            kit = Path(plan["kit_tree"]) / "research" / "circuit" / "inverter" / "instances"
            ok = self.step("inverters", [CR.PY, "-m", "invinst.indeck", d / "inv", "--deck", d / "deck.spice", "--seed", seed],
                           ["inv/inverter_gate.json", "inv/SHA256SUMS"], "inverters", cwd=kit)
        inv = [f"inverters={d / 'inv' / 'inverter_gate.json'}"] if s["front"] else []
        solo = ["solo=1"] if seed in plan["groups"][self.group].get("d4_audit", []) else []
        ok = ok and self.step("D", [CR.PY, "-B", sd, "run", sp, d / "D", seed, f"overlay={ov}",
                                    f"rule={plan.get('testError_rule', 'one-port')}", *inv, *solo],
                              ["D/record.json", "D/prediction.json"], "D")
        ok = ok and self.step("seal", [CR.PY, "-B", sd, "seal", d / "seal", d / "D"], ["seal/SHA256SUMS", "seal/MANIFEST.json"], "seal")
        sp_ = plan.get("seal_push")
        if sp_ is None:
            raise SystemExit("refused: the plan has no seal_push entry (stage N must follow a pushed seal)")
        ok = ok and self.step("sealpush", [CR.PY, "-B", HERE / "sealpush.py", "push", sp_["remote"], sp_["branch"], d.name,
                                           d / "seal", Path(self.dir).parent / ".seal_log_work", d / "seal_push.json",
                                           *(["dry=1"] if sp_.get("dry") else [])], ["seal_push.json"], "seal")
        ok = ok and self.round(0)
        if not ok:
            return None
        return json.loads((d / "D" / "prediction.json").read_text())["room_K3"]


def remote_duplicate(root, x, plan):
    """N0 of another machine's instance, here (the duplicate on a second machine)."""
    s = specmod.load(HERE / x["spec"])
    d = Path(root) / f"DUPX_{s['tag']}_{x['seed']}"
    d.mkdir(parents=True, exist_ok=True)
    res_path = d / "duplicate_here.json"
    if res_path.exists():
        return json.loads(res_path.read_text())
    nz = Path(plan["noise_tree"]) / "research" / "layered-networks"
    got = C3.BUDGET.acquire(1)
    try:
        rc, cpu, to = CR.run_child(CR.stagen_argv(plan, nz, HERE / x["spec"], d / "N0", x["seed"], 0,
                                                  plan.get("overlay", "config_inverter_c5.json")), nz, d / "N0.log", CR.DEFAULT_TIMEOUT["dup"])
    finally:
        C3.BUDGET.release(got)
    CR.drop_raw(d / "N0")
    res = dict(instance=f"{s['tag']}_{x['seed']}", group=x["group"], exit=rc, timed_out=to, cpu_s=cpu,
               ok=rc == 0 and not to and (d / "N0" / "noisy_record.json").exists())
    res_path.write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    return res


def cmd_run(plan_path, root, *rest):
    plan = json.loads(Path(plan_path).read_text())
    C3.Instance = Instance                     # campaign_run3.cmd_run installs C3.Instance into campaign_run2
    u_groups = set(plan.get("U_groups", plan["groups"]))
    untrained = CR.untrained
    CR.untrained = lambda r, inst, p: (untrained(r, inst, p) if inst.group in u_groups else
                                       dict(instance=inst.dir.name, ok=None, why="U of this group runs on another machine"))
    try:
        ok = C3.cmd_run(plan_path, root, *rest)
    finally:
        CR.untrained = untrained
    dups = [remote_duplicate(Path(root).resolve(), x, plan) for x in plan.get("remote_duplicates", [])]
    r = json.loads((Path(root) / "RESULT.json").read_text())
    r["remote_duplicates"] = dups
    (Path(root) / "RESULT.json").write_text(json.dumps(r, indent=1, sort_keys=True) + "\n")
    return ok


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
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run4.py"), "run", str(Path(plan_path).resolve()),
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
