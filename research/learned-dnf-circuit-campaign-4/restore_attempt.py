"""Campaign 4, amendment 8: rebuilds the rehearsal's attempt 2 (its work folder and its meta folder) from GitHub, for
the completion, on a machine where they no longer exist. Every file is checked; nothing is simulated.

    restore_attempt.py ATTEMPT_DIR META_DIR

From this checkout: `rehearsal/run-2/` (the files under 10 MB, the logs, the clone's bundles). From the branch
evidence/learned-dnf-circuit-campaign-4-rehearsal-run-2 (a partial fetch): the waveform files of 10 MB and more,
files above 100 MiB joined from their parts (PARTS.json). Checks: every big file against NOTE.md's SHA-256, every
collected file against its SURVIVORS.json, every evidence folder's files against the same list; the clone rebuilt on
3156ee4 with the rehearsal branch of its bundle, at the head its log names; the local remote's refs as recorded.
"""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = "research/learned-dnf-circuit-campaign-4"
RUN = HERE / "rehearsal" / "run-2"
BRANCH = "evidence/learned-dnf-circuit-campaign-4-rehearsal-run-2"
URL = "https://github.com/HevisNico/kernel-R"
RUNS_COMMIT = "3156ee40ab35dea396b6fa8785177b84b7667c76"


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def git(*args, cwd=None):
    return subprocess.run(["git", *map(str, args)], cwd=cwd, check=True, capture_output=True, text=True).stdout.strip()


def main():
    attempt, meta = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    assert not attempt.exists() and not meta.exists(), "the targets must not exist"
    big = {p: h for h, p in re.findall(r"^([0-9a-f]{64})  (\S+)$", (RUN / "NOTE.md").read_text(), flags=re.M)}
    assert len(big) == 132, len(big)
    # the files under 10 MB, as committed
    for p in sorted(RUN.rglob("*")):
        rel = p.relative_to(RUN)
        if p.is_file() and rel.parts[0] not in ("meta", "clone") and rel.name != "NOTE.md":
            (attempt / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(p, attempt / rel)
    shutil.copytree(RUN / "meta", meta)
    # the files of 10 MB and more, from the evidence branch
    ev = attempt.parent / (attempt.name + ".evidence-fetch")
    git("init", "-q", ev)
    git("-C", ev, "fetch", "-q", "--depth", "1", "--filter=blob:none", URL, BRANCH)
    git("-C", ev, "checkout", "-q", "FETCH_HEAD", "--", f"{BASE}/rehearsal/run-2")
    src = ev / BASE / "rehearsal" / "run-2"
    parts = json.loads((src / "PARTS.json").read_text())["files"]
    for rel, h in big.items():
        if rel in parts:
            data = b"".join((src / x["path"]).read_bytes() for x in parts[rel]["parts"])
            assert hashlib.sha256(data).hexdigest() == parts[rel]["sha256"] == h, rel
            (attempt / rel).parent.mkdir(parents=True, exist_ok=True)
            (attempt / rel).write_bytes(data)
            del data
            for x in parts[rel]["parts"]:
                (src / x["path"]).unlink()
        else:
            (attempt / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.move(src / rel, attempt / rel)           # moved, not copied: the files of 10 MB and more are 6.6 GB
        assert sha(attempt / rel) == h, rel
    shutil.rmtree(ev)
    # every collected folder against its SURVIVORS.json, and its evidence folder against the same list
    n = 0
    for col in sorted(attempt.glob("collected-*")):
        files = json.loads((col / "SURVIVORS.json").read_text())["files"]
        raw = attempt / col.name[len("collected-"):]
        for f in files:
            assert sha(col / f["path"]) == f["sha256"] and sha(raw / f["path"]) == f["sha256"], (col.name, f["path"])
            n += 1
        assert sum(1 for p in raw.rglob("*") if p.is_file()) == len(files), raw
        assert sum(1 for p in col.rglob("*") if p.is_file()) == len(files) + 1, col
    # the clone: 3156ee4, then the rehearsal branch of its bundle
    repo = attempt / "repo"
    git("clone", "-q", "--no-checkout", ROOT, repo)
    git("-C", repo, "fetch", "-q", RUN / "clone" / "rehearsal-branch.bundle", "rehearsal:rehearsal")
    git("-C", repo, "checkout", "-q", "rehearsal")
    head = (RUN / "clone" / "rehearsal-branch.log").read_text().split()[0]
    assert git("-C", repo, "rev-parse", "HEAD") == head and git("-C", repo, "merge-base", "HEAD", RUNS_COMMIT) == RUNS_COMMIT
    assert git("-C", repo, "status", "--porcelain") == ""
    for p in (RUN / "clone" / "files").rglob("*"):
        if p.is_file():
            assert p.read_bytes() == (repo / p.relative_to(RUN / "clone" / "files")).read_bytes(), p
    # the local remote and its claims
    remote = attempt / "remote.git"
    git("clone", "-q", "--bare", repo, remote)                     # its history (3156ee4, the rehearsal branch), then its claims
    git("-C", remote, "fetch", "-q", RUN / "clone" / "remote.bundle", "refs/*:refs/*")
    wanted = {l.split()[1] for l in (RUN / "clone" / "remote-refs.txt").read_text().splitlines()}
    for ref in git("-C", remote, "for-each-ref", "--format=%(refname)").splitlines():
        if ref not in wanted:
            git("-C", remote, "update-ref", "-d", ref)
    refs = git("-C", remote, "for-each-ref", "--format=%(objectname) %(refname)")
    assert refs == (RUN / "clone" / "remote-refs.txt").read_text().strip(), refs
    print(json.dumps(dict(restored=str(attempt), meta=str(meta), big_files=len(big), collected_files_checked=n, clone_head=head)))


if __name__ == "__main__":
    main()
