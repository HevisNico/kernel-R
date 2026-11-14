"""Execution of stage J on two machines, by the rules of ../AMENDMENT_2.md.

  python3 -I execute.py plan
  python3 -I execute.py launch --machine A --go      on machine A
  python3 -I execute.py launch --machine B --go      on machine B, once A has pushed the marker

Nothing starts without --go. The rules:

  - The split of the runs between the two machines is fixed here (SPLIT).
  - One marker, RUN_ATTEMPT_J.json, covers both machines. Machine A writes and pushes it before
    the first run; machine B refuses to start until it is on the branch. It names the attempt (1),
    the commit and the hash of the predictions, of the amendments and of the code.
  - Before a run starts, its name is pushed as started (results_j/NAME.started). A run found
    started and without a result when a machine comes back is recorded as lost (NAME.lost) and is
    never run again. A run that never started may proceed. A run that failed stays failed.
  - Each machine first runs the nominal cell of the schematic and compares it, byte for byte, with
    the committed result. If it differs, the machine runs nothing.
  - Results are pushed as each slice of at most four runs ends.

The runs themselves are those of j_stage.py, unchanged.
"""
import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent                                      # research/sky130-layout
sys.path.insert(0, str(HERE))                           # j_stage.py, also under python3 -I
STAGE = "J"
SPLIT = {"A": ["j1", "j4", "j5"], "B": ["j2", "j3", "j6"]}
SLICE = 4
PINNED = ["PREDICTION.md", "AMENDMENT_1.md", "AMENDMENT_2.md", "phase1/j_manifest.json", "phase1/execute.py",
          "phase1/j_statement.py"]
RULE = ("Pushed before the first run of the stage, once, for both machines. No second attempt. "
        "A run that started and left no result is lost and is never run again.")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def git(root, *args, check=True):
    p = subprocess.run(["git", "-C", str(root)] + list(args), capture_output=True, text=True)
    if check and p.returncode:
        raise RuntimeError(f"git {' '.join(args)}: {p.stderr.strip()}")
    return p.stdout.strip()


def branch(root):
    return git(root, "rev-parse", "--abbrev-ref", "HEAD")


def sync(root):
    b = branch(root)
    git(root, "fetch", "origin", b)
    git(root, "rebase", "FETCH_HEAD")


def publish(root, paths, message):
    """Commit the paths and push them. Returns only when the push has succeeded."""
    git(root, "add", "--", *[str(p) for p in paths])
    if not git(root, "status", "--porcelain", "--", *[str(p) for p in paths]):
        return
    git(root, "commit", "-q", "-m", message, "--", *[str(p) for p in paths])
    b = branch(root)
    for wait in (0, 2, 4, 8, 16, 32):
        time.sleep(wait)
        if subprocess.run(["git", "-C", str(root), "-c", "push.negotiate=true", "push", "origin", b],
                          capture_output=True).returncode == 0:
            return
        sync(root)
    raise RuntimeError("push refused six times: nothing is started")


def marker_content(root, machine):
    return dict(stage=STAGE, attempt=1, created_utc=now(), created_by_machine=machine,
                implementation_commit=git(root, "rev-parse", "HEAD"),
                sha256={p: digest(root / p) for p in PINNED}, split=SPLIT, rule=RULE)


def check_marker(root, marker):
    if marker.get("attempt") != 1 or marker.get("stage") != STAGE or marker.get("split") != SPLIT:
        raise RuntimeError("unexpected attempt marker")
    changed = [p for p in PINNED if digest(root / p) != marker["sha256"].get(p)]
    if changed:
        raise RuntimeError("changed since the attempt marker: " + ", ".join(changed))


def state(results, name):
    for kind in ("csv", "failed", "lost", "started"):
        if (results / f"{name}.{kind}").exists():
            return kind
    return "new"


def launch(machine, root=ROOT, run_one=None, preflight=None, verify=None, go=False):
    if not go:
        sys.exit(f"stage {STAGE} starts only on the owner's word: launch --machine {machine} --go")
    if machine not in SPLIT:
        sys.exit("machine is A or B")
    results = root / "phase1" / f"results_{STAGE.lower()}"
    marker_path = root / "phase1" / f"RUN_ATTEMPT_{STAGE}.json"
    sync(root)
    if git(root, "status", "--porcelain", "--", str(root)):
        sys.exit("the checkout is not clean")
    if verify:
        verify()
    if not marker_path.exists():
        if machine != "A":
            sys.exit("no attempt marker on the branch: machine A pushes it first")
        marker_path.write_text(json.dumps(marker_content(root, machine), indent=1) + "\n")
        publish(root, [marker_path], f"Stage {STAGE}: attempt marker, before the first run")
    marker = json.loads(marker_path.read_text())
    check_marker(root, marker)
    results.mkdir(exist_ok=True)

    pre = results / f"preflight_{machine}.json"
    if not pre.exists():
        pre.write_text(json.dumps(dict(machine=machine, host=platform.node(), **preflight()), indent=1) + "\n")
        publish(root, [pre], f"Stage {STAGE}: preflight of machine {machine}")
    if not json.loads(pre.read_text())["identical"]:
        sys.exit(f"machine {machine} does not reproduce the nominal run: it runs nothing")

    lost = []
    for name in SPLIT[machine]:
        if state(results, name) == "started":
            started = json.loads((results / f"{name}.started").read_text())
            (results / f"{name}.lost").write_text(json.dumps(dict(
                run=name, machine=machine, started_utc=started.get("started_utc"), found_utc=now(),
                reason="started, no result when the machine came back; never run again"), indent=1) + "\n")
            lost.append(results / f"{name}.lost")
    if lost:
        publish(root, lost, f"Stage {STAGE}, machine {machine}: {len(lost)} run(s) lost")

    pending = [n for n in SPLIT[machine] if state(results, n) == "new"]
    while pending:
        batch, pending = pending[:SLICE], pending[SLICE:]
        marks = []
        for name in batch:
            (results / f"{name}.started").write_text(json.dumps(dict(
                run=name, machine=machine, attempt=1, started_utc=now(), host=platform.node()), indent=1) + "\n")
            marks.append(results / f"{name}.started")
        publish(root, marks, f"Stage {STAGE}, machine {machine}: started {' '.join(batch)}")
        with ThreadPoolExecutor(SLICE) as ex:
            for line in ex.map(run_one, batch):
                print(line, flush=True)
        produced = [p for n in batch for p in results.glob(f"{n}.*") if p.suffix != ".started"]
        publish(root, produced, f"Stage {STAGE}, machine {machine}: results of {' '.join(batch)}")
    print({n: state(results, n) for n in SPLIT[machine]})


# ---- what a machine does for stage J

def stage_preflight():
    """The nominal cell of the schematic, by run.py as it is, against the committed result."""
    import j_stage
    d = HERE / "build" / "preflight"
    shutil.rmtree(d, ignore_errors=True)
    (d / "work").mkdir(parents=True)
    (d / "results").mkdir()
    for f in ("cell.spice", "blocks.spice", "run.py", "noise.json"):
        shutil.copy(j_stage.CIRCUIT / f, d / f)
    shutil.copy(j_stage.CIRCUIT / "spiceinit.txt", d / ".spiceinit")
    os.symlink(j_stage.MODELS, d / "pdk")
    started = time.time()
    p = subprocess.run([sys.executable, "-I", "run.py", "cell", "nom", "tt"], cwd=d, capture_output=True, text=True)
    out = d / "results" / "nom.csv"
    same = p.returncode == 0 and out.exists() and out.read_bytes() == (j_stage.CIRCUIT / "results" / "nom.csv").read_bytes()
    return dict(utc=now(), identical=same, wall_s=round(time.time() - started),
                csv_sha256=digest(out) if out.exists() else None,
                ngspice_sha256=digest(j_stage.NGSPICE), pdk_commit=j_stage.pdk_commit())


def stage_run(name):
    import j_stage
    return j_stage.one(next(r for r in j_stage.RUNS if r[0] == name))


if __name__ == "__main__":
    args = sys.argv[1:]
    if not args or args[0] == "plan":
        import j_stage
        assert sorted(SPLIT["A"] + SPLIT["B"]) == sorted(r[0] for r in j_stage.RUNS)
        for m in ("A", "B"):
            print("machine", m, ":", " ".join(SPLIT[m]))
    elif args[0] == "launch":
        import j_stage
        machine = args[args.index("--machine") + 1] if "--machine" in args else ""
        launch(machine, run_one=stage_run, preflight=stage_preflight, verify=j_stage.check_manifest, go="--go" in args)
    else:
        sys.exit(__doc__)
