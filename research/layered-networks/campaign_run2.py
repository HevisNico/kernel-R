"""campaign_run.py with job-level scheduling and the machine-run discipline (plan steps 4 and 8). Development only.

campaign_run.py is pushed and kept as it is; its steps, commands, controls and checks are reused unchanged. Added:

1. **Scheduling.** Jobs, at most `jobs` (default 4) at a time:
   - per instance, the chain deck -> inverters -> D -> seal -> N0 -> C0 (each step needs the previous one);
   - once C0 is done and the instance has room at K3, its noisy rounds N1+C1, N2+C2, N3+C3 as three separate jobs,
     in parallel;
   - per group, once every instance of the group has finished its chain, U on the first eligible instance in seed
     order; the duplicate as soon as its instance's N0 is done.
   The kit's in-deck gate runs its inverters in parallel inside one job (XOR3: 2 processes), so a front-end job can
   briefly use one core more than its slot.
2. **No relaunch of a step that started.** Before a step runs, status.json records it as `running`. A step found
   `running` at a resume (the machine or the driver stopped during it) is marked `interrupted` and is never run again,
   like a failed one: a counted run is never relaunched (plan §9). Its instance is reported under that step.
3. **Stage D by `stage_d4.py`** (PLAN `stage_d_script`; default stage_d4.py: every mask read, the either cell's (1, 2)
   included; stage_d3.py misses it, the defect found by the dry run on ANDOR3 9805).
4. **The machine-run discipline.**
     campaign_run2.py launch PLAN.json OUTROOT [jobs=4]   checks that no ngspice runs (pgrep) and that OUTROOT does
                                                          not exist; writes OUTROOT/INVENTORY_START (uptime -s, nproc,
                                                          the ngspice sha256, the trees); starts `run` detached
                                                          (setsid nohup) and returns its pid
     campaign_run2.py wait OUTROOT [seconds<=590]         waits in the foreground at most that long; prints the steps'
                                                          status; exit 0 when the run has ended, 3 while it runs
     campaign_run2.py run PLAN.json OUTROOT [jobs=4]      the run itself (what `launch` starts), resumable
     campaign_run2.py status OUTROOT                      status.json of every instance, and the critical path per group
   `run` writes OUTROOT/INVENTORY_END (uptime -s) and OUTROOT/DONE when it ends. If `uptime -s` differs between the two,
   the machine restarted during the run: the report then comes from status.json, and nothing that started is run again.
"""
import concurrent.futures as cf
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import threading
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402

WAIT_MAX_S = 590


def now():
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


class Instance(CR.Instance):
    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.lock = threading.Lock()
        changed = False
        for name, st in self.status["steps"].items():          # a step that started and never ended
            if st["status"] == "running":
                st.update(status="interrupted", why="found running at a resume (the driver or the machine stopped)",
                          found_at=now())
                changed = True
        if changed:
            self.save()

    def save(self):
        with self.lock:
            super().save()

    def step(self, name, argv, outputs, kind, cwd=HERE, env=None):
        if self.done(name):
            return True
        st = self.status["steps"].get(name)
        if st and st["status"] != "done":
            return False                                       # failed, timed out or interrupted: never run again
        t0 = time.time()
        rec = dict(argv=[str(a) for a in argv], started=now(), status="running")
        self.status["steps"][name] = rec
        self.save()
        rc, cpu, timed_out = CR.run_child(argv, cwd, self.dir / f"{name}.log", self.timeouts[kind], env)
        rec = dict(rec)
        if timed_out:
            rec.update(status="timeout", why=f"more than {self.timeouts[kind]} s")
        else:
            missing = [f for f in outputs if not (self.dir / f).exists()]
            if rc == 0 and not missing:
                rec.update(status="done", outputs={f: CR.sha(self.dir / f) for f in outputs})
            else:
                rec.update(status="failed", why=f"exit {rc}" + (f", missing {missing}" if missing else ""))
        rec.update(wall_s=round(time.time() - t0, 1), cpu_s=cpu, ended=now())
        self.status["steps"][name] = rec
        self.save()
        return rec["status"] == "done"

    def chain(self):
        """deck .. C0. Returns room_K3 (True: the noisy rounds follow), or None when the chain stopped."""
        s, d, plan, seed = self.s, self.dir, self.plan, self.seed
        ov = plan.get("overlay", "config_inverter_c5.json")
        sp = HERE / self.spec_path
        ok = self.step("deck", [CR.PY, "-B", HERE / plan.get("stage_d_script", "stage_d4.py"), "deck", sp, d / "deck.spice", f"overlay={ov}"], ["deck.spice"], "deck")
        if ok and s["front"]:
            kit = Path(plan["kit_tree"]) / "research" / "circuit" / "inverter" / "instances"
            ok = self.step("inverters", [CR.PY, "-m", "invinst.indeck", d / "inv", "--deck", d / "deck.spice", "--seed", seed],
                           ["inv/inverter_gate.json", "inv/SHA256SUMS"], "inverters", cwd=kit)
        inv = [f"inverters={d / 'inv' / 'inverter_gate.json'}"] if s["front"] else []
        ok = ok and self.step("D", [CR.PY, "-B", HERE / plan.get("stage_d_script", "stage_d4.py"), "run", sp, d / "D", seed, f"overlay={ov}",
                                    f"rule={plan.get('testError_rule', 'one-port')}", *inv], ["D/record.json", "D/prediction.json"], "D")
        ok = ok and self.step("seal", [CR.PY, "-B", HERE / plan.get("stage_d_script", "stage_d4.py"), "seal", d / "seal", d / "D"],
                              ["seal/SHA256SUMS", "seal/MANIFEST.json"], "seal")
        ok = ok and self.round(0)
        if not ok:
            return None
        return json.loads((d / "D" / "prediction.json").read_text())["room_K3"]

    def round(self, n):
        d, plan = self.dir, self.plan
        ov = plan.get("overlay", "config_inverter_c5.json")
        sp = HERE / self.spec_path
        nz = Path(plan["noise_tree"]) / "research" / "layered-networks"
        outs = [f"N{n}/noisy_record.json"] + ([f"N{n}/trace.digest.json"] if plan.get("stagen", "controls2") == "controls2" else [])
        ok = self.step(f"N{n}", CR.stagen_argv(plan, nz, sp, d / f"N{n}", self.seed, n, ov), outs, "N", cwd=nz)
        ok = ok and self.step(f"C{n}", CR.compare_argv(d / "seal", sp, d / f"N{n}", n), [f"N{n}/comparison.json"], "C")
        if ok:
            CR.drop_raw(d / f"N{n}")
        return ok


def critical_path(inst):
    """The instance's wall time along its dependencies: the chain, then the longest noisy round."""
    st = inst.status["steps"]
    w = lambda k: (st.get(k) or {}).get("wall_s") or 0
    chain = sum(w(k) for k in ("deck", "inverters", "D", "seal", "N0", "C0"))
    rounds = max([w(f"N{n}") + w(f"C{n}") for n in (1, 2, 3)] or [0])
    return dict(chain_s=round(chain, 1), longest_round_s=round(rounds, 1), total_s=round(chain + rounds, 1))


def cmd_run(plan_path, root, *rest):
    kw = dict(a.split("=", 1) for a in rest)
    jobs = int(kw.get("jobs", 4))
    plan = json.loads(Path(plan_path).read_text())
    root = Path(root).resolve()
    root.mkdir(parents=True, exist_ok=True)
    trees = CR.check_trees(plan)
    plan_bytes = Path(plan_path).read_bytes()
    if (root / "PLAN.json").exists():
        assert (root / "PLAN.json").read_bytes() == plan_bytes, "refused: OUTROOT was started with another plan"
    else:
        (root / "PLAN.json").write_bytes(plan_bytes)
    (root / "trees.json").write_text(json.dumps(trees, indent=1, sort_keys=True) + "\n")
    insts = [Instance(root, g, gp["spec"], seed, plan) for g, gp in plan["groups"].items() for seed in gp["seeds"]]
    controls = dict(U=[], duplicate=[])
    room, chain_done, errors = {}, set(), []
    dup = (plan.get("controls") or {}).get("duplicate", {})
    with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
        live = {ex.submit(i.chain): ("chain", i) for i in insts}
        while live:
            done, _ = cf.wait(live, return_when=cf.FIRST_COMPLETED)
            for f in done:
                kind, i = live.pop(f)
                try:
                    r = f.result()
                except BaseException as e:                     # reported, never retried; the other jobs go on
                    errors.append(dict(job=kind, instance=i.dir.name, error=repr(e)))
                    continue
                if kind == "chain":
                    room[i.dir.name] = r
                    chain_done.add(i.dir.name)
                    if r:
                        for n in range(1, plan.get("rounds", 3) + 1):
                            live[ex.submit(i.round, n)] = ("round", i)
                    if dup.get(i.group) == i.seed and i.status["steps"].get("N0", {}).get("status") == "done":
                        live[ex.submit(CR.duplicate, root, i, plan)] = ("dup", i)
                    group = [x for x in insts if x.group == i.group]
                    if all(x.dir.name in chain_done for x in group):
                        el = sorted((x for x in group if (x.dir / "D" / "prediction.json").exists() and
                                     json.loads((x.dir / "D" / "prediction.json").read_text())["eligible_K0"]),
                                    key=lambda x: x.seed)
                        if el:
                            live[ex.submit(CR.untrained, root, el[0], plan)] = ("U", el[0])
                elif kind == "dup":
                    controls["duplicate"].append(r)
                elif kind == "U":
                    controls["U"].append(r)
    summ = [i.summary() for i in insts]
    for s_, i in zip(summ, insts):
        s_["critical_path"] = critical_path(i)
    groups = {}
    for i in insts:
        cp = critical_path(i)["total_s"]
        groups.setdefault(i.group, dict(instances=0, longest_instance_s=0))
        groups[i.group]["instances"] += 1
        groups[i.group]["longest_instance_s"] = max(groups[i.group]["longest_instance_s"], cp)
    controls["U"].sort(key=lambda x: x["instance"])
    controls["duplicate"].sort(key=lambda x: x["instance"])
    result = dict(trees=trees, instances=summ, controls=controls, critical_path_per_group=groups, job_errors=errors)
    (root / "RESULT.json").write_text(json.dumps(result, indent=1, sort_keys=True) + "\n")
    files = sorted(p for p in root.glob("*/SHA256SUMS")) + [root / "RESULT.json", root / "PLAN.json", root / "trees.json"]
    files += sorted(root.glob("DUP_*/duplicate.json")) + sorted(root.glob("U_*/untrained.json"))
    (root / "SHA256SUMS").write_text("".join(f"{CR.sha(p)}  {p.relative_to(root)}\n" for p in files))
    (root / "INVENTORY_END").write_text(inventory())
    (root / "DONE").write_text(now() + "\n")
    print(json.dumps(result, indent=1, sort_keys=True))
    return True


def inventory(plan=None):
    up = subprocess.run(["uptime", "-s"], capture_output=True, text=True).stdout.strip()
    out = dict(uptime_s=up, nproc=os.cpu_count(), at=now())
    if plan is not None:
        ng = subprocess.run(["sh", "-c", "readlink -f $(command -v ngspice)"], capture_output=True, text=True).stdout.strip()
        out.update(ngspice=ng, ngspice_sha256=hashlib.sha256(Path(ng).read_bytes()).hexdigest() if ng else None,
                   trees=CR.check_trees(plan))
    return json.dumps(out, indent=1, sort_keys=True) + "\n"


def cmd_launch(plan_path, root, *rest):
    root = Path(root).resolve()
    n = subprocess.run(["pgrep", "-c", "ngspice"], capture_output=True, text=True).stdout.strip()
    if n not in ("", "0"):
        raise SystemExit(f"refused: {n} ngspice process(es) running")
    if root.exists() and any(root.iterdir()):
        raise SystemExit(f"refused: {root} exists and is not empty (no run folders before a launch)")
    plan = json.loads(Path(plan_path).read_text())
    root.mkdir(parents=True, exist_ok=True)
    (root / "INVENTORY_START").write_text(inventory(plan))
    log = (root / "driver.log").open("w")
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run2.py"), "run", str(Path(plan_path).resolve()),
                          str(root), *rest], stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                         start_new_session=True, cwd=HERE)
    (root / "DRIVER_PID").write_text(f"{p.pid}\n")
    print(f"launched pid {p.pid}")
    return True


def alive(pid):
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False


def cmd_status(root):
    root = Path(root)
    for p in sorted(root.glob("*/status.json")):
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
    print("ENDED" if ended else "RUNNING", "DONE" if (root / "DONE").exists() else "")
    return ended


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c == "run":
        sys.exit(0 if cmd_run(*a) else 1)
    elif c == "launch":
        sys.exit(0 if cmd_launch(*a) else 1)
    elif c == "wait":
        sys.exit(0 if cmd_wait(*a) else 3)
    elif c == "status":
        cmd_status(*a)
    else:
        sys.exit(__doc__)
