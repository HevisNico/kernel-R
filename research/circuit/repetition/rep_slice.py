"""One slice of the repetitions: one repetition number, on the machine it belongs to.

  REP_MACHINE=A|B rep_slice.py REP [PRIVATE_REPOSITORY]

Runs the repetition, puts its reduced traces in one archive, pushes the archive to the private
repository (folder 09-repetition-traces/, branch sim/core-loop), reads it back from GitHub and compares
its SHA-256, removes the local traces, then commits and pushes the public results of the slice with the
name and the SHA-256 of the archive. Failed runs stay failed and are pushed as such.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import time

HERE = Path(__file__).resolve().parent
PUBLIC, PRIVATE = "research/circuit-repetition", "sim/core-loop"


def sh(args, cwd, check=True, capture=False):
    return subprocess.run(args, cwd=cwd, check=check, text=True, capture_output=capture)


def push(cwd, branch):
    """Push with a rebase on what the other machine pushed meanwhile."""
    for attempt in range(6):
        sh(["git", "pull", "-q", "--rebase", "origin", branch], cwd, check=False)
        if sh(["git", "push", "-q", "origin", f"HEAD:{branch}"], cwd, check=False).returncode == 0:
            return
        time.sleep(5 * (attempt + 1))
    raise SystemExit(f"push to {branch} failed")


def main():
    rep = int(sys.argv[1])
    private = Path(sys.argv[2] if len(sys.argv) > 2 else "/home/user/kernel-r-circuit")
    tag = f"rep{rep:02d}"
    status = sh([sys.executable, "-B", str(HERE / "rep_launch.py"), "repeat", str(rep)], HERE, check=False).returncode
    results, traces = HERE / "results" / "repeat" / tag, HERE / "traces" / "repeat" / tag
    names = sorted(p.stem for p in results.glob("*.json") if p.name != "ARCHIVE.json")
    archive = HERE / "work" / f"{tag}.tar"
    with tarfile.open(archive, "w") as tar:
        for n in names:
            tar.add(traces / f"{n}.npz", arcname=f"{tag}/{n}.npz")
    sha = hashlib.sha256(archive.read_bytes()).hexdigest()
    (private / "09-repetition-traces").mkdir(exist_ok=True)
    target = private / "09-repetition-traces" / archive.name
    target.write_bytes(archive.read_bytes())
    sh(["git", "add", str(target)], private)
    sh(["git", "commit", "-q", "-m", f"Repetition campaign: reduced traces of repetition {rep}\n\n"
        f"One archive, SHA-256 {sha}. The SHA-256 of each trace is in the public metadata of its run."], private)
    push(private, PRIVATE)
    commit = sh(["git", "rev-parse", "HEAD"], private, capture=True).stdout.strip()
    back = subprocess.run(["gh", "api", "-H", "Accept: application/vnd.github.raw",
                           f"repos/HevisNico/kernel-R-circuit/contents/09-repetition-traces/{archive.name}?ref={PRIVATE}"], capture_output=True)
    online = hashlib.sha256(back.stdout).hexdigest() if back.returncode == 0 else None
    if online != sha:
        raise SystemExit(f"{tag}: the archive read back from GitHub does not have the SHA-256 of the local one; local traces are kept")
    traces_sha = {n: json.loads((results / f"{n}.json").read_text())["trace_sha256"] for n in names}
    failed = sorted(p.stem for p in results.glob("*.failed"))
    (results / "ARCHIVE.json").write_text(json.dumps(dict(archive=f"09-repetition-traces/{archive.name}", repository="HevisNico/kernel-R-circuit",
                                                          branch=PRIVATE, commit=commit, sha256=sha, bytes=archive.stat().st_size,
                                                          read_back_from_github_sha256=online, traces=traces_sha, failed_runs=failed), indent=1) + "\n")
    for n in names:
        (traces / f"{n}.npz").unlink()
    archive.unlink()
    top = sh(["git", "rev-parse", "--show-toplevel"], HERE, capture=True).stdout.strip()
    sh(["git", "add", str(results)], top)
    sh(["git", "commit", "-q", "-m", f"Repetition campaign: repetition {rep}, {len(names)} runs done, {len(failed)} failed\n\n"
        f"Machine {os.environ.get('REP_MACHINE', 'A')}. Rows, charges and metadata as written by rep_run.py; reduced traces in the\n"
        f"archive {archive.name} of the private repository, SHA-256 checked on the copy read back from GitHub.\nNothing is analysed."], top)
    push(top, PUBLIC)
    print(tag, "pushed:", len(names), "runs done,", len(failed), "failed")
    return status


if __name__ == "__main__":
    sys.exit(main())
