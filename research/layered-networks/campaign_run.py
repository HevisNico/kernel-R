"""One campaign pipeline driver (CAMPAIGN_PLAN_DRAFT.md §2, §6, §10): every step of every instance, in order, with
jobs, timeouts, SHA256SUMS and a resumable status. Development only; nothing frozen.

  campaign_run.py run    PLAN.json OUTROOT [jobs=4]     run (or resume) every instance, then the controls
  campaign_run.py status OUTROOT                        the status of every instance and control
  campaign_run.py verify OUTROOT                        every SHA256SUMS under OUTROOT checked

Per instance (group, spec, seed), in OUTROOT/<TAG>_<seed>/, each step a subprocess with its own timeout:
  deck      stage_d.py deck: the deck text of stage D and stage N (deck.spice, its sha256)
  inverters front-end groups only: the kit's in-deck gate on deck.spice at the seed (inv/inverter_gate.json)
  D         stage_d.py run, with inverters=inv/inverter_gate.json (D/)
  seal      stage_d.py seal of this instance alone (seal/), written before any stage-N step starts
  N0        stage N without noise: noise2.py run SPEC N0 SEED 0 (N0/noisy_record.json)
  C0        compare_d.py seal/ against N0 (C0.json)
  N1..N3    only with room at K3: noise2.py rounds 1-3, noise seed 10 S + n; C1..C3 their comparisons
A step runs only when every earlier step is done. A failed or timed-out step stops its instance there; it is recorded
with its reason, never re-run automatically, and the instance is reported under that step (plan §9). `run` on an
existing OUTROOT resumes: a step marked done is kept when its output files still have their recorded sha256, else the
run refuses (an output changed after it was recorded).

Controls (plan §6), after the instances:
  U         per group, on its first eligible instance in seed order: the untrained run (PLAN `controls.U` command);
            the claim checked: no R-cell output fires on any pattern
  S         the shift slots are read from each stage-N record by compare_d.py (slots of kind `skew`)
  duplicate per group, one instance (PLAN `controls.duplicate`): its N0 again in a fresh folder; input.spice
            byte-identical and the record identical except its cost fields

PLAN.json:
  {"groups": {"NOT1": {"spec": "specs/not1.json", "seeds": [9801], "timeout_s": {"D": 1800, ...}}, ...},
   "overlay": "config_inverter_c5.json",
   "noise_tree": "<a checkout of research/layered-networks holding noise2.py, pinned by commit>",
   "noise_commit": "38a95c8...", "kit_tree": "<a checkout of research/inverter-instances>", "kit_commit": "d599300...",
   "rounds": 3,
   "controls": {"U": {"command": [...]} | null, "duplicate": {"NOT1": 9801, ...}}}
Both trees are checked at their pinned commit before anything runs (git rev-parse HEAD, clean tree).
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
import spec as specmod  # noqa: E402

PY = sys.executable
DEFAULT_TIMEOUT = dict(deck=120, inverters=3600, D=7200, seal=120, N=7200, C=300, U=3600, dup=7200)
COST_FIELDS = ("cost",)


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def git_head(tree):
    head = subprocess.run(["git", "-C", str(tree), "rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()
    dirty = subprocess.run(["git", "-C", str(tree), "status", "--porcelain", "--untracked-files=no"],
                           capture_output=True, text=True, check=True).stdout.strip()
    return head, not dirty


def check_trees(plan):
    out = {}
    for key, ck in (("noise_tree", "noise_commit"), ("kit_tree", "kit_commit")):
        if not plan.get(key):
            continue
        head, clean = git_head(plan[key])
        assert head.startswith(plan[ck]), f"{key} is at {head}, not the pinned {plan[ck]}"
        assert clean, f"{key} has local changes"
        out[key] = dict(path=str(plan[key]), commit=head)
    out["stage_d_tree"] = dict(zip(("commit", "clean"), git_head(HERE)))
    return out


class Instance:
    def __init__(self, root, group, spec_path, seed, plan):
        self.group, self.spec_path, self.seed, self.plan = group, Path(spec_path), int(seed), plan
        self.s = specmod.load(HERE / spec_path)
        self.dir = Path(root) / f"{self.s['tag']}_{self.seed}"
        self.dir.mkdir(parents=True, exist_ok=True)
        self.status_path = self.dir / "status.json"
        self.status = json.loads(self.status_path.read_text()) if self.status_path.exists() else dict(
            tag=self.s["tag"], seed=self.seed, group=group, steps={})
        self.timeouts = dict(DEFAULT_TIMEOUT, **plan["groups"][group].get("timeout_s", {}))

    def save(self):
        tmp = self.status_path.with_suffix(".tmp")
        tmp.write_text(json.dumps(self.status, indent=1, sort_keys=True) + "\n")
        os.replace(tmp, self.status_path)

    def done(self, step):
        st = self.status["steps"].get(step)
        if not st or st["status"] != "done":
            return False
        for f, h in st["outputs"].items():
            if not (self.dir / f).exists() or sha(self.dir / f) != h:
                raise SystemExit(f"refused: {self.dir.name} step {step}: output {f} changed after it was recorded")
        return True

    def step(self, name, argv, outputs, kind, cwd=HERE, env=None):
        """Run one step unless done. Returns True when done (now or before)."""
        if self.done(name):
            return True
        st = self.status["steps"].get(name)
        if st and st["status"] != "done":
            return False                                   # failed earlier: never re-run automatically
        t0 = time.time()
        log = self.dir / f"{name}.log"
        rec = dict(argv=[str(a) for a in argv], started=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
        rc, cpu, timed_out = run_child(argv, cwd, log, self.timeouts[kind], env)
        if timed_out:
            rec.update(status="timeout", why=f"more than {self.timeouts[kind]} s")
        else:
            missing = [f for f in outputs if not (self.dir / f).exists()]
            if rc == 0 and not missing:
                rec.update(status="done", outputs={f: sha(self.dir / f) for f in outputs})
            else:
                rec.update(status="failed", why=f"exit {rc}" + (f", missing {missing}" if missing else ""))
        rec.update(wall_s=round(time.time() - t0, 1), cpu_s=cpu)
        self.status["steps"][name] = rec
        self.save()
        return rec["status"] == "done"

    def pipeline(self):
        s, d, plan, seed = self.s, self.dir, self.plan, self.seed
        ov = plan.get("overlay", "config_inverter_c5.json")
        sp = HERE / self.spec_path
        ok = self.step("deck", [PY, "-B", HERE / "stage_d.py", "deck", sp, d / "deck.spice", f"overlay={ov}"], ["deck.spice"], "deck")
        if ok and s["front"]:
            kit = Path(plan["kit_tree"]) / "research" / "circuit" / "inverter" / "instances"
            ok = self.step("inverters", [PY, "-m", "invinst.indeck", d / "inv", "--deck", d / "deck.spice", "--seed", seed],
                           ["inv/inverter_gate.json", "inv/SHA256SUMS"], "inverters", cwd=kit)
        inv = [f"inverters={d / 'inv' / 'inverter_gate.json'}"] if s["front"] else []
        ok = ok and self.step("D", [PY, "-B", HERE / "stage_d.py", "run", sp, d / "D", seed, f"overlay={ov}", *inv],
                              ["D/record.json", "D/prediction.json"], "D")
        ok = ok and self.step("seal", [PY, "-B", HERE / "stage_d.py", "seal", d / "seal", d / "D"],
                              ["seal/SHA256SUMS", "seal/MANIFEST.json"], "seal")
        if not ok:
            return self.summary()
        pred = json.loads((d / "D" / "prediction.json").read_text())
        rounds = [0] + (list(range(1, plan.get("rounds", 3) + 1)) if pred["room_K3"] else [])
        nz = Path(plan["noise_tree"]) / "research" / "layered-networks"
        for n in rounds:
            ok = self.step(f"N{n}", [PY, "-B", nz / "noise2.py", "run", sp, d / f"N{n}", seed, n, f"overlay={ov}"],
                           [f"N{n}/noisy_record.json"], "N", cwd=nz)
            ok = ok and self.step(f"C{n}", [PY, "-B", HERE / "compare_d.py", d / "seal", sp, d / f"N{n}" / "noisy_record.json",
                                            "noiseless" if n == 0 else "noisy", d / f"C{n}.json"], [f"C{n}.json"], "C")
            if not ok:
                break
        return self.summary()

    def summary(self):
        d = self.dir
        out = dict(tag=self.s["tag"], seed=self.seed, group=self.group,
                   steps={k: v["status"] for k, v in self.status["steps"].items()})
        if (d / "D" / "prediction.json").exists():
            p = json.loads((d / "D" / "prediction.json").read_text())
            out.update(eligible_K0=p["eligible_K0"], room_K3=p["room_K3"], inverter_gate=p["inverter_gate"]["source"])
        out["verdicts"] = {f"C{n}": json.loads((d / f"C{n}.json").read_text())["verdict"]
                           for n in range(0, 4) if (d / f"C{n}.json").exists()}
        out["cpu_s"] = {k: v.get("cpu_s") for k, v in self.status["steps"].items()}
        out["wall_s"] = {k: v.get("wall_s") for k, v in self.status["steps"].items()}
        files = sorted(p for p in d.rglob("*.json") if p.name != "status.json" and "lean_build" not in p.parts)
        (d / "SHA256SUMS").write_text("".join(f"{sha(p)}  {p.relative_to(d)}\n" for p in files))
        return out


def run_child(argv, cwd, log, timeout, env=None):
    """One child process, its exit code, its CPU seconds (user + system of the child and every descendant it waited
    for, from wait4) and whether it was killed at the timeout."""
    with Path(log).open("w") as fh:
        p = subprocess.Popen([str(a) for a in argv], cwd=cwd, stdout=fh, stderr=subprocess.STDOUT,
                             env=dict(os.environ, **(env or {})), start_new_session=True)
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
        p.returncode = os.waitstatus_to_exitcode(status)
    return p.returncode, round(ru.ru_utime + ru.ru_stime, 1), killed.is_set()


# ------------------------------------------------------------------------------------------------ controls

def core(rec):
    rec = {k: v for k, v in rec.items() if k not in COST_FIELDS}
    return json.dumps(rec, sort_keys=True)


def duplicate(root, inst, plan):
    """The instance's N0 again, in OUTROOT/DUP_<TAG>_<seed>: input.spice byte-identical, the record identical except
    its cost fields."""
    d = Path(root) / f"DUP_{inst.dir.name}"
    d.mkdir(exist_ok=True)
    res_path = d / "duplicate.json"
    if res_path.exists():
        return json.loads(res_path.read_text())
    nz = Path(plan["noise_tree"]) / "research" / "layered-networks"
    t0 = time.time()
    rc, cpu, to = run_child([PY, "-B", nz / "noise2.py", "run", HERE / inst.spec_path, d / "N0", inst.seed, 0,
                             f"overlay={plan.get('overlay', 'config_inverter_c5.json')}"], nz, d / "N0.log", DEFAULT_TIMEOUT["dup"])
    a, b = inst.dir / "N0", d / "N0"
    res = dict(instance=inst.dir.name, exit=rc, timed_out=to, cpu_s=cpu, wall_s=round(time.time() - t0, 1))
    if rc == 0 and not to:
        ra, rb = (json.loads((x / "noisy_record.json").read_text()) for x in (a, b))
        res.update(input_spice_identical=(a / "input.spice").read_bytes() == (b / "input.spice").read_bytes(),
                   record_identical_except_cost=core(ra) == core(rb))
        res["ok"] = res["input_spice_identical"] and res["record_identical_except_cost"]
    else:
        res["ok"] = False
    res_path.write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    return res


def untrained(root, inst, plan):
    """Plan §6 U: the PLAN's command (the stage-N side's untrained run), then the check that no R-cell output fires
    on any of the 2^m patterns. The command template gets {spec}, {out}, {seed}, {overlay}."""
    cmd = (plan.get("controls") or {}).get("U")
    if not cmd:
        return dict(instance=inst.dir.name, ok=None, why="no U command in the plan (stage-N side not built yet)")
    d = Path(root) / f"U_{inst.dir.name}"
    res_path = d / "untrained.json"
    if res_path.exists():
        return json.loads(res_path.read_text())
    d.mkdir(exist_ok=True)
    nz = Path(plan["noise_tree"]) / "research" / "layered-networks"
    argv = [a.format(spec=HERE / inst.spec_path, out=d / "U", seed=inst.seed,
                     overlay=plan.get("overlay", "config_inverter_c5.json")) for a in cmd["command"]]
    rc, cpu, to = run_child(argv, nz, d / "U.log", DEFAULT_TIMEOUT["U"])
    res = dict(instance=inst.dir.name, exit=rc, timed_out=to, cpu_s=cpu)
    rec_path = d / "U" / cmd.get("record", "record.json")
    if rc == 0 and not to and rec_path.exists():
        rec = json.loads(rec_path.read_text())
        fired = [dict(slot=i, cell=f"c{r['layer']}_{r['index']}") for i in rec["tests"]
                 for r in rec["slots"][i]["reads"] if r["emission"] is not None]
        inv = [dict(slot=i, inverter=j) for i in rec["tests"] for j, v in enumerate(rec["slots"][i].get("inv", []))
               if v.get("emission") is not None]
        res.update(patterns=len(rec["tests"]), r_cell_fires=fired, inverter_fires_reported=inv, ok=not fired)
    else:
        res["ok"] = False
    res_path.write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    return res


# ------------------------------------------------------------------------------------------------ commands

def instances(plan, root):
    out = []
    for g, gp in plan["groups"].items():
        for seed in gp["seeds"]:
            out.append(Instance(root, g, gp["spec"], seed, plan))
    return out


def cmd_run(plan_path, root, *rest):
    kw = dict(a.split("=", 1) for a in rest)
    plan = json.loads(Path(plan_path).read_text())
    root = Path(root)
    root.mkdir(parents=True, exist_ok=True)
    trees = check_trees(plan)
    plan_bytes = Path(plan_path).read_bytes()
    if (root / "PLAN.json").exists():
        assert (root / "PLAN.json").read_bytes() == plan_bytes, "refused: OUTROOT was started with another plan"
    else:
        (root / "PLAN.json").write_bytes(plan_bytes)
    (root / "trees.json").write_text(json.dumps(trees, indent=1, sort_keys=True) + "\n")
    insts = instances(plan, root)
    with cf.ThreadPoolExecutor(max_workers=int(kw.get("jobs", 4))) as ex:
        summ = list(ex.map(lambda i: i.pipeline(), insts))
    controls = dict(U=[], duplicate=[])
    for g in plan["groups"]:
        el = [i for i, s_ in zip(insts, summ) if i.group == g and s_.get("eligible_K0")]
        if el:
            controls["U"].append(untrained(root, sorted(el, key=lambda i: i.seed)[0], plan))
        dup_seed = (plan.get("controls") or {}).get("duplicate", {}).get(g)
        if dup_seed is not None:
            i = next(i for i in insts if i.group == g and i.seed == dup_seed)
            if i.status["steps"].get("N0", {}).get("status") == "done":
                controls["duplicate"].append(duplicate(root, i, plan))
    result = dict(trees=trees, instances=summ, controls=controls)
    (root / "RESULT.json").write_text(json.dumps(result, indent=1, sort_keys=True) + "\n")
    files = sorted(p for p in root.glob("*/SHA256SUMS")) + [root / "RESULT.json", root / "PLAN.json", root / "trees.json"]
    files += sorted(root.glob("DUP_*/duplicate.json")) + sorted(root.glob("U_*/untrained.json"))
    (root / "SHA256SUMS").write_text("".join(f"{sha(p)}  {p.relative_to(root)}\n" for p in files))
    print(json.dumps(result, indent=1, sort_keys=True))
    return True


def cmd_status(root):
    for p in sorted(Path(root).glob("*/status.json")):
        st = json.loads(p.read_text())
        print(p.parent.name, {k: v["status"] for k, v in st["steps"].items()})


def cmd_verify(root):
    bad = []
    for sums in sorted(Path(root).rglob("SHA256SUMS")):
        if "lean_build" in sums.parts:
            continue
        for line in sums.read_text().splitlines():
            h, n = line.split("  ", 1)
            f = sums.parent / n
            if not f.exists() or sha(f) != h:
                bad.append(str(f))
    print("verified" if not bad else "BROKEN: " + ", ".join(bad))
    return not bad


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c == "run":
        sys.exit(0 if cmd_run(*a) else 1)
    elif c == "status":
        cmd_status(*a)
    elif c == "verify":
        sys.exit(0 if cmd_verify(*a) else 1)
    else:
        sys.exit(__doc__)
