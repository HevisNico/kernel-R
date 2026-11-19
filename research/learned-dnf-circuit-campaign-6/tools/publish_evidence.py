"""Campaign 6: publish one machine's collected evidence of a stage on its own evidence branch, and verify it there.

  publish_evidence.py --collected DIR --repo REPO --base COMMIT --evidence-path PATH --branch BRANCH --message MSG
                      --work DIR [--remote NAME_OR_URL] [--extra SRC[=NAME] ...] [--expect-author NAME]

Outside the frozen set, used identically on machines a and b. Every step's result is checked in Python; the first
failure prints `REFUSED <reason>` and exits 1, and nothing is pushed unless steps 1 to 3 passed:
1. DIR is collect.py's output: every entry of DIR/COLLECTED.json (path, bytes, sha256) matches, and DIR holds no other
   file than those and COLLECTED.json.
2. A fresh worktree WORK at BASE gets PATH/ = DIR, every file above 100 MiB as consecutive parts of 90 000 000 bytes
   (`<file>.part-000`, ...) with one PATH/PARTS.json in campaign 4's shape; the whole file is not written. Each --extra
   file is copied to PATH/NAME (default: its own name), and must not collide with a collected path.
3. One commit on BASE with git's configured identity (user.name must equal --expect-author when given, and user.email
   must be set), touching only PATH/; every blob of the commit's PATH/ must be under 100 MiB.
4. `git push REMOTE <commit>:refs/heads/BRANCH`, no force; BRANCH must not exist on REMOTE before.
5. `git fetch REMOTE BRANCH`; FETCH_HEAD must equal the commit; every COLLECTED.json file is read back from FETCH_HEAD
   (reassembled from its parts when split) and must match its bytes and sha256; every PARTS.json part must match too;
   no whole file of a split entry may be in the tree.
6. One verdict line: `PUBLISHED-VERIFIED <commit> <tree>` (exit 0) or `REFUSED <reason>` (exit 1).
It deletes nothing: neither DIR, nor the run folder, nor WORK. Clearing a run folder stays a separate manual step,
taken only after PUBLISHED-VERIFIED.
"""
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

LIMIT = 100 * 1024 * 1024
PART = 90_000_000
RULE = "files above 100 MiB as consecutive parts of 90 000 000 bytes; their concatenation in order is the file"


class Refused(Exception):
    pass


def sha(b):
    return hashlib.sha256(b).hexdigest()


def git(repo, *args, check=True):
    r = subprocess.run(["git", "-C", str(repo), *args], capture_output=True)
    if check and r.returncode != 0:
        raise Refused(f"git {' '.join(args[:2])} failed: {r.stderr.decode(errors='replace').strip()[:300]}")
    return r


def check_collected(src):
    """Step 1."""
    if not (src / "COLLECTED.json").is_file():
        raise Refused(f"{src}/COLLECTED.json missing")
    collected = json.loads((src / "COLLECTED.json").read_text())
    files = collected.get("files")
    if not isinstance(files, list) or not files:
        raise Refused("COLLECTED.json lists no files")
    listed = {}
    for f in files:
        p = src / f["path"]
        if not p.is_file() or p.is_symlink():
            raise Refused(f"collected file missing: {f['path']}")
        data = p.read_bytes()
        if len(data) != f["bytes"] or sha(data) != f["sha256"]:
            raise Refused(f"collected file differs from COLLECTED.json: {f['path']}")
        listed[f["path"]] = f
    present = {x.relative_to(src).as_posix() for x in src.rglob("*") if x.is_file() or x.is_symlink()}
    extra = sorted(present - set(listed) - {"COLLECTED.json"})
    if extra:
        raise Refused(f"files not in COLLECTED.json: {extra[:5]}")
    return listed


def stage_tree(src, listed, dst, extras):
    """Step 2: write PATH/ in the worktree; returns PARTS.json's files mapping."""
    if dst.exists():
        raise Refused(f"{dst} exists in the worktree")
    parts = {}
    for rel in sorted(listed):
        data = (src / rel).read_bytes()
        out = dst / rel
        out.parent.mkdir(parents=True, exist_ok=True)
        if len(data) > LIMIT:
            entry = []
            for i in range(0, len(data), PART):
                chunk = data[i:i + PART]
                name = f"{rel}.part-{i // PART:03d}"
                (dst / name).write_bytes(chunk)
                entry.append({"path": name, "bytes": len(chunk), "sha256": sha(chunk)})
            parts[rel] = {"bytes": len(data), "sha256": sha(data), "parts": entry}
        else:
            out.write_bytes(data)
    shutil.copyfile(src / "COLLECTED.json", dst / "COLLECTED.json")
    if parts:
        (dst / "PARTS.json").write_text(json.dumps({"rule": RULE, "files": parts}, indent=1) + "\n")
    for spec in extras:
        s, _, name = spec.partition("=")
        s = Path(s)
        name = name or s.name
        if "/" in name or name in ("COLLECTED.json", "PARTS.json") or (dst / name).exists():
            raise Refused(f"extra file name not allowed or collides: {name}")
        if not s.is_file():
            raise Refused(f"extra file missing: {s}")
        shutil.copyfile(s, dst / name)
    big = sorted(x.relative_to(dst).as_posix() for x in dst.rglob("*") if x.is_file() and x.stat().st_size >= LIMIT)
    if big:
        raise Refused(f"files of 100 MiB or more in the evidence folder: {big}")
    return parts


def commit(work, base, path, message, expect_author):
    """Step 3."""
    name = git(work, "config", "user.name", check=False).stdout.decode().strip()
    email = git(work, "config", "user.email", check=False).stdout.decode().strip()
    if not name or not email:
        raise Refused("git identity not configured")
    if expect_author is not None and name != expect_author:
        raise Refused("git user.name is not the expected author")
    git(work, "add", "--", path)
    git(work, "commit", "-q", "-m", message)
    c = git(work, "rev-parse", "HEAD").stdout.decode().strip()
    if git(work, "rev-parse", "HEAD^").stdout.decode().strip() != base:
        raise Refused("the commit's parent is not BASE")
    touched = git(work, "diff", "--name-only", base, c).stdout.decode().split()
    outside = [p for p in touched if not p.startswith(path + "/")]
    if outside:
        raise Refused(f"the commit touches paths outside {path}/: {outside[:5]}")
    for line in git(work, "ls-tree", "-r", "-l", c, "--", path + "/").stdout.decode().splitlines():
        size = int(line.split()[3])
        if size >= LIMIT:
            raise Refused(f"a blob of 100 MiB or more: {line.split(chr(9))[1]}")
    return c


def verify(work, fetched, path, listed, parts):
    """Step 5's read-back."""
    tree = set(git(work, "ls-tree", "-r", "--name-only", fetched, "--", path + "/").stdout.decode().splitlines())
    for rel, f in listed.items():
        if rel in parts:
            if f"{path}/{rel}" in tree:
                raise Refused(f"the whole file of a split entry is in the pushed tree: {rel}")
            chunks = []
            for q in parts[rel]["parts"]:
                c = git(work, "show", f"{fetched}:{path}/{q['path']}").stdout
                if len(c) != q["bytes"] or sha(c) != q["sha256"]:
                    raise Refused(f"pushed part differs from PARTS.json: {q['path']}")
                chunks.append(c)
            data = b"".join(chunks)
        else:
            data = git(work, "show", f"{fetched}:{path}/{rel}").stdout
        if len(data) != f["bytes"] or sha(data) != f["sha256"]:
            raise Refused(f"pushed file differs from COLLECTED.json: {rel}")


def publish(a):
    src, work = Path(a.collected).resolve(), Path(a.work).resolve()
    listed = check_collected(src)                                                         # 1
    if work.exists():
        raise Refused(f"{work} exists")
    if git(a.repo, "ls-remote", "--heads", a.remote, a.branch).stdout.strip():
        raise Refused(f"branch {a.branch} already exists on {a.remote}")
    git(a.repo, "worktree", "add", "-q", "--detach", str(work), a.base)
    parts = stage_tree(src, listed, work / a.evidence_path, a.extra)                     # 2
    c = commit(work, a.base, a.evidence_path, a.message, a.expect_author)                # 3
    git(work, "push", a.remote, f"{c}:refs/heads/{a.branch}")                            # 4
    git(work, "fetch", "-q", a.remote, a.branch)                                         # 5
    fetched = git(work, "rev-parse", "FETCH_HEAD").stdout.decode().strip()
    if fetched != c:
        raise Refused(f"the fetched branch head {fetched} is not the pushed commit {c}")
    verify(work, fetched, a.evidence_path, listed, parts)
    return c, git(work, "rev-parse", c + "^{tree}").stdout.decode().strip()


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    for k in ("--collected", "--repo", "--base", "--evidence-path", "--branch", "--message", "--work"):
        p.add_argument(k, required=True)
    p.add_argument("--remote", default="origin")
    p.add_argument("--extra", action="append", default=[])
    p.add_argument("--expect-author")
    a = p.parse_args(argv)
    try:
        c, tree = publish(a)
    except Refused as e:
        print(f"REFUSED {e}")
        return 1
    print(f"PUBLISHED-VERIFIED {c} {tree}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
