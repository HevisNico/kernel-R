"""campaign_run8.py with the fixes of the pre-freeze dry run (owner's decisions, relayed 2026-11-25). Development only.
campaign_run8.py and the earlier drivers are kept as they are.

1. **The end of the machine (defects 1 and 6).**
   - campaign_run2 used to write INVENTORY_END and DONE (and `wait` then printed ENDED DONE) before campaign_run4 ran the
     remote duplicates, and campaign_run3's core_budget was written before them too.
   - Here campaign_run2's end is held: its RESULT.json and first SHA256SUMS are written, but not INVENTORY_END or DONE.
     Then every later job runs: campaign_run3's core budget, campaign_run4's remote duplicates, campaign_run5's
     stopped_for_disk.
   - After them: RESULT.json's `core_budget` is written again, with the peak over every job, remote duplicates
     included. Each DUPX_<inst> folder gets its own SHA256SUMS (every .json below it, N0/input.spice and its
     seal/SHA256SUMS). The top-level SHA256SUMS is written last over campaign_run8's list, which then includes
     DUPX_*/SHA256SUMS.
   - Only then are INVENTORY_END and DONE written. So `wait` prints ENDED DONE only after every job of the machine, and
     `campaign_run.py verify` covers the duplicate's files.
2. **The save_ref round (defect 2).** Before that round's trace.raw is deleted (campaign_run5's rule), ref_extract.py
   writes ROUND/ref/: the comparator vectors as a small raw file, a copy of the record, SHA256SUMS and ref.json. The
   comparator noise is then read from the root with tests/check_ref_level.py ROUND/ref. A failed extraction keeps the
   whole trace.raw and is recorded in ROUND/ref_extract.json.
3. **The remote duplicate's comparison (defect 3).** PLAN `remote_duplicates[]` takes `seal_dir`: a folder holding the
   original instance's seal (MANIFEST.json, SHA256SUMS, the sealed prediction). Before comparing:
   - the seal log is fetched from PLAN seal_push.remote: the branch of `seal_log`, by name;
   - the commit `seal_log` names must be on that branch;
   - its SEALS.txt must hold a line for the instance whose seal sha256 is the sha256 of seal_dir/SHA256SUMS;
   - seal.verify(seal_dir) must hold.
   Then seal_dir is copied to DUPX_<inst>/seal, and DUPX_<inst>/N0 is compared with campaign_run's own compare_argv
   (compare_d2.py, noiseless): the same comparison as the original's C0. The result is DUPX_<inst>/N0/comparison.json.
   Without seal_dir, or when a check fails, no comparison.json is written and DUPX_<inst>/seal_check.json says why.
4. **ENV.json (defect 5)** is written by envcheck_layered2.env (format layered-env/2): numpy's fingerprint covers its
   package files, not its install path.

  campaign_run9.py launch | run | wait | status ...     as campaign_run8.py
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import campaign_run as CR  # noqa: E402
import campaign_run2 as C2  # noqa: E402
import campaign_run3 as C3  # noqa: E402
import campaign_run4 as C4  # noqa: E402
import campaign_run5 as C5  # noqa: E402
import campaign_run8 as C8  # noqa: E402
import envcheck_layered2 as E2  # noqa: E402
import ref_extract  # noqa: E402
import seal as sealmod  # noqa: E402
import spec as specmod  # noqa: E402

PLAN = {}


class _Hold(Exception):
    """Raised in place of campaign_run2's INVENTORY_END: its end is held until every job of the machine has ended."""


# ------------------------------------------------------------------------------------------------ ENV (defect 5)

def set_env(plan, root):
    root = Path(root)
    root.mkdir(parents=True, exist_ok=True)
    e = E2.env(plan)
    f = root / "ENV.json"
    if f.exists():
        old = json.loads(f.read_text())
        if old["static_sha256"] != e["static_sha256"]:
            raise SystemExit(f"refused: mixed environment in {root}: ENV.json static {old['static_sha256'][:12]}, "
                             f"this machine now {e['static_sha256'][:12]}")
        rs = root / "ENV_RESUMES.json"
        log = json.loads(rs.read_text()) if rs.exists() else []
        log.append(dict(uptime_s=e["uptime_s"], static_sha256=e["static_sha256"]))
        rs.write_text(json.dumps(log, indent=1) + "\n")
    else:
        f.write_bytes(E2.E.canon(e))
    os.environ["LAYERED_ENV_SHA256"] = CR.sha(f)
    return os.environ["LAYERED_ENV_SHA256"]


# ------------------------------------------------------------------------------------------------ save_ref (defect 2)

_c5_drop_raw = C5.drop_raw


def save_ref_round(folder):
    folder = Path(folder)
    n = PLAN.get("save_ref_round")
    return (n is not None and folder.name == f"N{int(n)}" and not folder.parent.name.startswith(("DUP_", "DUPX_", "U_")))


def drop_raw(folder):
    folder = Path(folder)
    if save_ref_round(folder) and (folder / "trace.raw").exists() and not (folder / "ref" / "ref.json").exists():
        try:
            m = ref_extract.extract(folder)
            (folder / "ref_extract.json").write_text(json.dumps(dict(ok=True, size=m["extract"]["size"],
                                                                     sha256=m["extract"]["sha256"]), indent=1) + "\n")
        except (SystemExit, Exception) as e:          # the whole trace is then kept
            (folder / "ref_extract.json").write_text(json.dumps(dict(ok=False, why=str(e)), indent=1) + "\n")
            return
    return _c5_drop_raw(folder)


# ------------------------------------------------------------------------------------------------ remote duplicate (defect 3)

_c4_remote_duplicate = C4.remote_duplicate


def seal_log_line(remote, commit, branch, instance, want_sha):
    """(ok, why): the seal log branch, fetched by name, holds `commit`, and its SEALS.txt there has a line for
    `instance` with seal sha256 `want_sha`."""
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


def remote_duplicate(root, x, plan):
    res = _c4_remote_duplicate(root, x, plan)
    s = specmod.load(HERE / x["spec"])
    inst = f"{s['tag']}_{x['seed']}"
    d = Path(root) / f"DUPX_{inst}"
    chk = dict(instance=inst, seal_dir=x.get("seal_dir"), seal_log=x.get("seal_log"))
    if not res.get("ok"):
        chk.update(ok=False, why="the duplicate's N0 did not complete")
    elif (d / "N0" / "comparison.json").exists():
        return res
    elif not x.get("seal_dir") or not x.get("seal_log"):
        chk.update(ok=False, why="no seal_dir or seal_log in PLAN remote_duplicates")
    else:
        sd = Path(x["seal_dir"])
        commit, branch = x["seal_log"]
        try:
            verified = sd.is_dir() and sealmod.verify(sd, quiet=True)
        except SystemExit as e:
            verified = False
            chk["verify_error"] = str(e)
        want = CR.sha(sd / "SHA256SUMS") if (sd / "SHA256SUMS").exists() else None
        ok, why = (seal_log_line(plan["seal_push"]["remote"], commit, branch, inst, want) if verified and want
                   else (False, "seal.verify failed or no SHA256SUMS"))
        chk.update(ok=ok, why=why, seal_sha256=want)
        if ok:
            if (d / "seal").exists():
                shutil.rmtree(d / "seal")
            shutil.copytree(sd, d / "seal", symlinks=False)
            rc, cpu, to = CR.run_child(CR.compare_argv(d / "seal", HERE / x["spec"], d / "N0", 0), HERE, d / "C0.log",
                                       CR.DEFAULT_TIMEOUT["C"])
            done = rc == 0 and not to and (d / "N0" / "comparison.json").exists()
            chk.update(compare=dict(exit=rc, timed_out=to, cpu_s=cpu, written=done))
            if done:
                chk["verdict"] = json.loads((d / "N0" / "comparison.json").read_text())["verdict"]
            chk["ok"] = done
    (d / "seal_check.json").write_text(json.dumps(chk, indent=1, sort_keys=True) + "\n")
    return res


def dupx_sums(root):
    for d in sorted(Path(root).glob("DUPX_*")):
        files = sorted(p for p in d.rglob("*.json"))
        files += [p for p in (d / "N0" / "input.spice", d / "seal" / "SHA256SUMS") if p.exists()]
        (d / "SHA256SUMS").write_text("".join(f"{CR.sha(p)}  {p.relative_to(d)}\n" for p in sorted(set(files))))


# ------------------------------------------------------------------------------------------------ the run

def cmd_run(plan_path, root, *rest):
    PLAN.clear()
    PLAN.update(json.loads(Path(plan_path).read_text()))
    root = Path(root).resolve()
    held = dict(reached=False)
    orig = dict(c2_run=C2.cmd_run, inventory=C2.inventory, set_env=C3.set_env, c5_drop=C5.drop_raw,
                c4_dup=C4.remote_duplicate)

    def hold(*a_, **k_):
        raise _Hold()

    def c2_held(*a, **k):
        C2.inventory = hold
        try:
            return orig["c2_run"](*a, **k)
        except _Hold:
            held["reached"] = True
            return True
        finally:
            C2.inventory = orig["inventory"]

    C2.cmd_run, C3.set_env, C5.drop_raw, C4.remote_duplicate = c2_held, set_env, drop_raw, remote_duplicate
    try:
        ok = C8.cmd_run(plan_path, root, *rest)
    finally:
        C2.cmd_run, C2.inventory, C3.set_env = orig["c2_run"], orig["inventory"], orig["set_env"]
        C5.drop_raw, C4.remote_duplicate = orig["c5_drop"], orig["c4_dup"]
    if not held["reached"]:
        return ok
    r = json.loads((root / "RESULT.json").read_text())
    r["core_budget"] = dict(cores=C3.BUDGET.cores, peak_in_use=C3.BUDGET.peak, written="after every job")
    r["end_held_until_every_job"] = True
    (root / "RESULT.json").write_text(json.dumps(r, indent=1, sort_keys=True) + "\n")
    dupx_sums(root)
    C8.rewrite_top_sums(root)
    (root / "INVENTORY_END").write_text(C2.inventory())
    (root / "DONE").write_text(C2.now() + "\n")
    return ok


def cmd_launch(plan_path, root, *rest):
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
    p = subprocess.Popen(["nohup", CR.PY, "-B", str(HERE / "campaign_run9.py"), "run", str(Path(plan_path).resolve()),
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
