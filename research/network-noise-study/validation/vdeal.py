"""Amendment 3: machine 5's 33 runs as one queue (DEAL_A3.md); each free machine takes the next run, four at a time.

  python vdeal.py RELEASED_TREE QUEUE_TREE WORK MACHINE

- RELEASED_TREE is a checkout of the GO commit of attempt 2 (341aac1, which adds only GO to 74e93b4).
- QUEUE_TREE is a checkout of the branch research/network-noise-study-validation-a3-queue, whose QUEUE.md lists the
  33 runs in the plan's order.

This script is orchestration. It imports vplan and vrun from RELEASED_TREE, makes amendment 2's checks there
(vplan.released, the environment and the inventory) and records them. Then each of its four workers takes the next
run of the queue: the first one with no `claims/<order>.json` on the queue branch. A claim is a commit adding that
file, pushed without force. If the push is refused (another machine claimed first), the local commit is dropped and
the next run is taken. The worker runs exactly the plan's command for the run (`vplan.command`), so the run keeps
its seed, round and position. Each run's machine, start and end times (UTC), exit code, wall time and peak memory
go to plan.log. The run's own JSON records its hashes and its machine.
"""
import datetime, json, os, re, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

BRANCH = "research/network-noise-study-validation-a3-queue"
LOCK = threading.Lock()


def git(tree, *a, check=True):
    p = subprocess.run(["git", "-C", str(tree), *a], capture_output=True, text=True)
    if check and p.returncode:
        raise RuntimeError(f"git {' '.join(a)}: {p.stderr[-500:]}")
    return p


def claim(qtree, machine):
    """The next unclaimed run of the queue, claimed for this machine; None when the queue is empty."""
    with LOCK:
        for _ in range(50):
            git(qtree, "fetch", "-q", "origin", BRANCH)
            git(qtree, "reset", "-q", "--hard", f"origin/{BRANCH}")
            rows = re.findall(r"^\| (\d+) \| `(\S+)` \|$", (Path(qtree) / "QUEUE.md").read_text(), re.M)
            taken = {p.stem for p in (Path(qtree) / "claims").glob("*.json")} if (Path(qtree) / "claims").exists() else set()
            free = [(o, n) for o, n in rows if o not in taken]
            if not free:
                return None
            order, name = free[0]
            (Path(qtree) / "claims").mkdir(exist_ok=True)
            t = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")
            (Path(qtree) / "claims" / f"{order}.json").write_text(json.dumps(dict(order=int(order), run=name, machine=int(machine), claimed_utc=t)) + "\n")
            git(qtree, "add", f"claims/{order}.json")
            git(qtree, "commit", "-q", "-m", f"Noise study, validation, amendment 3: machine {machine} takes run {order} ({name})")
            if git(qtree, "push", "-q", "origin", f"HEAD:{BRANCH}", check=False).returncode == 0:
                return name
            time.sleep(3)
        raise RuntimeError("could not claim a run after 50 attempts")


def main(tree, qtree, work, machine):
    val = Path(tree) / "research" / "network-noise-study" / "validation"
    sys.path.insert(0, str(val))
    import vplan
    Path(work).mkdir(parents=True, exist_ok=True)
    inv = vplan.inventory()
    inv.update(machine=int(machine), code=vplan.released(), amendment=3)
    (Path(work) / f"MACHINE_{machine}_A3.json").write_text(json.dumps(inv, indent=1) + "\n")
    assert inv["identical_to_reference"], "environment differs: nothing runs"
    assert inv["code"]["ok"] and inv["code"]["released_commit"] == "74e93b4c05d99a580e00d550f3b2a3c00de08bef", \
        "not on attempt 2's GO: nothing runs"
    os.environ["VAL_MACHINE"] = f"{machine} (amendment 3 rerun)"
    plan = {r[1]: r for r in vplan.runs()}
    log = open(Path(work) / "plan.log", "a")
    now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")

    def worker(_):
        while True:
            name = claim(qtree, machine)
            if name is None:
                return
            out, cmd = vplan.command(work, plan[name])
            t0, start = time.time(), now()
            with open(str(out) + ".stderr", "w") as fe:
                p = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=fe, text=True)
                _, status, ru = os.wait4(p.pid, 0)
            code = os.waitstatus_to_exitcode(status)
            print(f"{name} exit {code} {time.time() - t0:.0f} s peak {ru.ru_maxrss / 1024:.0f} MB start {start} end {now()} machine {machine}",
                  file=log, flush=True)
    with ThreadPoolExecutor(4) as ex:
        list(ex.map(worker, range(4)))
    print(f"done amendment 3 machine={machine}", file=log, flush=True)


if __name__ == "__main__":
    main(*sys.argv[1:5])
