"""campaign_run5.py on the controls' sealed stage-N entry point (controls3.py, noise3, research/layered-networks
3ce53cd). Development only. campaign_run5.py and the earlier drivers are kept as they are.

What changes (PLAN `stagen`: "controls3"):
- **Stage N** of every round: `controls3.py stagen SPEC OUT SEED ROUND seal_log=<commit> seal_branch=<branch>
  overlay=...`. That is noise3's run: the R-cell noise, the C5 inverters' budgeted noise, the skew slots.
  - The commit and branch are those of the instance's seal_push.json, which campaign_run5 has already checked
    (pushed, 40 hex) before stage N.
  - controls3 refuses (exit 2) without them and records them in noisy_record.json as `seal_log`.
- **The duplicates** (DUP_<inst>, DUPX_<inst>) pass the ORIGINAL instance's seal log, as controls3 expects for an
  identity rerun.
  - For a cross-machine duplicate, the original's seal log is not on this machine. PLAN
    `remote_duplicates[].seal_log` must give it. Without it, the duplicate is refused.
- **U**: `controls3.py untrained ... seal_log=<commit> seal_branch=<branch>` with the seal log of the instance it runs
  on. The record is untrained_record.json, with `seal_log`.
- **Outputs**: noise3's stage N writes noisy_record.json and no trace.raw or trace.digest.json (unlike controls2).
  - The step therefore requires only noisy_record.json.
  - The duplicate check then compares the records and input.spice, not the trace. That was reported to the controls'
    session.

  campaign_run6.py launch | run | wait | status ...     as campaign_run5.py
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run3 as C3  # noqa: E402
import campaign_run5 as C5  # noqa: E402

PLAN = {}


def seal_of(inst_dir):
    """(commit, branch) of an instance's pushed seal, or None."""
    f = Path(inst_dir) / "seal_push.json"
    if not f.exists():
        return None
    r = json.loads(f.read_text())
    ok = r.get("pushed") is True or (r.get("pushed") == "dry" and PLAN.get("allow_dry_seal"))
    return (r["commit"], r["branch"]) if ok and r.get("commit") and r.get("branch") else None


def original_dir(out):
    """The instance folder whose seal a stage-N folder runs under (a duplicate: the original's)."""
    inst = Path(out).parent
    for p in ("DUP_", "DUPX_"):
        if inst.name.startswith(p):
            return inst.parent / inst.name[len(p):]
    return inst


def stagen_argv(plan, nz, sp, out, seed, n, ov):
    if plan.get("stagen", "controls2") != "controls3":
        return _stagen_argv(plan, nz, sp, out, seed, n, ov)
    inst = Path(out).parent
    s = seal_of(original_dir(out))
    if s is None and inst.name.startswith("DUPX_"):
        x = next((x for x in plan.get("remote_duplicates", []) if f"_{x['seed']}" == inst.name[-len(str(x["seed"])) - 1:]), {})
        s = tuple(x["seal_log"]) if x.get("seal_log") else None
    commit, branch = s if s else ("", "")                   # controls3 refuses (exit 2) without a seal log
    return [CR.PY, "-B", nz / "controls3.py", "stagen", sp, out, seed, n, f"seal_log={commit}", f"seal_branch={branch}",
            f"overlay={ov}"]


_stagen_argv = CR.stagen_argv
_untrained = CR.untrained


def untrained(root, inst, plan):
    if plan.get("stagen", "controls2") != "controls3":
        return _untrained(root, inst, plan)
    d = Path(root) / f"U_{inst.dir.name}"
    res_path = d / "untrained.json"
    if res_path.exists():
        return json.loads(res_path.read_text())
    d.mkdir(exist_ok=True)
    nz = Path(plan["noise_tree"]) / "research" / "layered-networks"
    s = seal_of(inst.dir)
    commit, branch = s if s else ("", "")
    rc, cpu, to = CR.run_child([CR.PY, "-B", nz / "controls3.py", "untrained", HERE / inst.spec_path, d / "U", inst.seed,
                                f"seal_log={commit}", f"seal_branch={branch}",
                                f"overlay={plan.get('overlay', 'config_inverter_c5.json')}"], nz, d / "U.log", CR.DEFAULT_TIMEOUT["U"])
    res = dict(instance=inst.dir.name, exit=rc, timed_out=to, cpu_s=cpu, seal_log=dict(commit=commit, branch=branch))
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


class Instance(C5.Instance):
    def round(self, n):
        if self.plan.get("stagen", "controls2") != "controls3":
            return super().round(n)
        # campaign_run5's checks (pushed seal, SEAL_LOG.json, the delay), then controls3 through stagen_argv; the
        # stage-N step's outputs are noisy_record.json only (noise3 writes no trace digest)
        name = f"N{n}"
        if not self.done(name) and name not in self.status["steps"]:
            if not seal_of(self.dir):
                self.status["steps"][name] = dict(status="refused", why="no pushed seal-log commit (seal_push.json)",
                                                  ended=C2.now())
                self.save()
                return False
        return super().round(n)                        # stagen != "controls2": the step needs noisy_record.json only


def cmd_run(plan_path, root, *rest):
    PLAN.clear()
    PLAN.update(json.loads(Path(plan_path).read_text()))
    CR.untrained = untrained
    CR.stagen_argv = lambda plan, nz, sp, out, seed, n, ov: stagen_argv(PLAN, nz, sp, out, seed, n, ov)
    C5.Instance, saved_c5 = Instance, C5.Instance
    try:
        return C5.cmd_run(plan_path, root, *rest)
    finally:
        CR.untrained, CR.stagen_argv, C5.Instance = _untrained, _stagen_argv, saved_c5


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
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run6.py"), "run", str(Path(plan_path).resolve()),
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
