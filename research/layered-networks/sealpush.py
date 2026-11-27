"""The seal push (PREDICTION draft, owner-approved 2026-11-24): after an instance's seal and BEFORE its stage N, one line
is appended to the machine's own log branch, pushed, and stage N starts only once the push has succeeded. Development
only; nothing here pushes unless a remote is given.

  sealpush.py push REMOTE BRANCH INSTANCE SEALDIR WORKDIR OUT.json [dry=1]
  sealpush.py times REMOTE BRANCH SOURCE OUT.json        the recorded push time of every commit of the branch

- **The line**: `<instance> <seal sha256> <UTC time>`, where the seal sha256 is the sha256 of SEALDIR/SHA256SUMS
  (which covers the instance's sealed prediction and MANIFEST.json) and the time is the machine's UTC clock when the
  line is written.
- **The log**: the file SEALS.txt on BRANCH (`evidence/combined-seals-K<nn>`, one branch per machine), one commit per
  line. It is append-only: the new file must start with the remote's current file, byte for byte. The push is a plain
  `git push REMOTE HEAD:refs/heads/BRANCH`: no force; a rejected push is a failure.
- **Success** means the push exited 0 and `git ls-remote` then shows the branch at the new commit. OUT.json records the
  line, the commit and the result.
- **Failure** writes OUT.json with `pushed: false` and the reason, and exits 1. The pipeline then does not start
  stage N, and the instance is "not sealed".
- **dry=1**: everything is done in WORKDIR (the line, the commit) except the push. `pushed` is "dry", which the pipeline
  treats as not sealed for counting. It is meant for tests and the dry run.

**The push time** (`times`): the time the remote **received** each push, not the commit date (which the machine
sets).
- **SOURCE github**: GitHub's repository activity API, `GET /repos/{owner}/{repo}/activity?ref=refs/heads/BRANCH&
  activity_type=push` (via `gh api`). Each push has `after` (the new commit) and `timestamp`, GitHub's own record of
  the push.
- **SOURCE lsremote:<LOG>** (fallback when the activity API cannot be reached): the coordinator's timestamped
  ls-remote log (seal_watch.py). Each commit's first-seen time is an upper bound of its push time.
- **SOURCE bare** (tests, and the dry run): a local bare repository whose `post-receive` hook (`install_hook`) appends
  `<new sha> <ref> <UTC time>` to push_times.log as the push is received. This is the same notion: the server's clock
  at reception.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
LOG = "SEALS.txt"


def utc():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%fZ")


def git(*a, cwd=None, check=True):
    r = subprocess.run(["git", *a], cwd=cwd, capture_output=True, text=True)
    if check and r.returncode:
        raise RuntimeError(f"git {' '.join(a)}: {r.stderr.strip()[-500:]}")
    return r


def seal_sha(sealdir):
    return hashlib.sha256((Path(sealdir) / "SHA256SUMS").read_bytes()).hexdigest()


def push(remote, branch, instance, sealdir, work, out, dry=False):
    work, out = Path(work), Path(out)
    res = dict(remote=str(remote), branch=branch, instance=instance, pushed=False)
    try:
        import seal as sealmod
        try:
            ok = sealmod.verify(sealdir, quiet=True)
        except Exception as e:                          # a malformed manifest makes seal.verify raise
            ok, why = False, repr(e)
        if not ok:
            raise RuntimeError("the seal does not verify")
        h = seal_sha(sealdir)
        if not (work / ".git").exists():
            work.mkdir(parents=True, exist_ok=True)
            git("init", "-q", cwd=work)
        have = git("ls-remote", str(remote), f"refs/heads/{branch}", cwd=work).stdout.split()
        if have:
            git("fetch", "-q", str(remote), f"refs/heads/{branch}", cwd=work)   # by name
            git("checkout", "-q", "-B", branch, "FETCH_HEAD", cwd=work)
            before = (work / LOG).read_bytes() if (work / LOG).exists() else b""
        else:
            git("checkout", "-q", "--orphan", branch, cwd=work, check=False)
            git("rm", "-rq", "--cached", ".", cwd=work, check=False)
            before = b""
        line = f"{instance} {h} {utc()}\n"
        (work / LOG).write_bytes(before + line.encode())
        assert (work / LOG).read_bytes().startswith(before), "the log is append-only"
        git("add", LOG, cwd=work)
        git("commit", "-q", "-m", f"seal {instance}", cwd=work)
        head = git("rev-parse", "HEAD", cwd=work).stdout.strip()
        res.update(line=line.rstrip("\n"), seal_sha256=h, commit=head, previous=have[0] if have else None)
        if dry:
            res["pushed"] = "dry"
        else:
            r = git("push", "-q", str(remote), f"HEAD:refs/heads/{branch}", cwd=work, check=False)
            if r.returncode:
                raise RuntimeError("push rejected: " + r.stderr.strip()[-300:])
            now = git("ls-remote", str(remote), f"refs/heads/{branch}", cwd=work).stdout.split()
            if not now or now[0] != head:
                raise RuntimeError(f"after the push the branch is at {now[:1]}, not {head}")
            res.update(pushed=True, pushed_at_machine_utc=utc())
    except Exception as e:                                  # reported; the pipeline does not start stage N
        res.update(pushed=False, why=str(e))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    return res["pushed"] is True or (dry and res["pushed"] == "dry")


HOOK = """#!/bin/sh
# post-receive: the server's own record of when each push arrived (UTC), for sealpush.times SOURCE bare
while read old new ref; do
  echo "$new $ref $(date -u +%Y-%m-%dT%H:%M:%S.%NZ)" >> "$GIT_DIR/push_times.log"
done
"""


def install_hook(bare):
    h = Path(bare) / "hooks" / "post-receive"
    h.write_text(HOOK)
    h.chmod(0o755)


GITHUB_PUSH_TYPES = ("push", "branch_creation")   # GitHub records the push that creates a branch as branch_creation


def activity_pages(text):
    """The items of every page `gh api --paginate` printed: one JSON array per page, concatenated with or without
    whitespace between them, parsed one after the other (not by joining the text)."""
    dec, items, i = json.JSONDecoder(), [], 0
    while True:
        while i < len(text) and text[i].isspace():
            i += 1
        if i == len(text):
            return items
        page, i = dec.raw_decode(text, i)
        if not isinstance(page, list):
            raise ValueError(f"an activity page is not a list: {type(page).__name__}")
        items += page


def github_times(items):
    """{commit sha: push time} from the repository activity API's items for one ref. Only a push (activity_type push)
    or the push that created the branch (branch_creation) counts: never force_push, branch_deletion, or any other
    type. The time is the one of the push that made the commit the branch tip (`after`)."""
    return {x["after"]: x["timestamp"] for x in items if x.get("activity_type") in GITHUB_PUSH_TYPES}


def times(remote, branch, source):
    """{commit sha: UTC time the remote received the push that made it the branch tip}."""
    if source == "bare":
        log = Path(remote) / "push_times.log"
        out = {}
        for line in log.read_text().splitlines() if log.exists() else []:
            sha, ref, t = line.split()
            if ref == f"refs/heads/{branch}":
                out.setdefault(sha, t[:26] + "Z" if len(t) > 27 else t)
        return out
    if str(source).startswith("lsremote:"):          # the coordinator's ls-remote log (seal_watch.py): first-seen times
        import seal_watch
        return seal_watch.times(str(source).split(":", 1)[1], branch)
    if source == "github":
        owner_repo = str(remote).rstrip("/").removesuffix(".git").split("github.com/")[-1]
        r = subprocess.run(["gh", "api", "-X", "GET", f"repos/{owner_repo}/activity", "-f", f"ref=refs/heads/{branch}",
                            "-f", "per_page=100", "--paginate"], capture_output=True, text=True, check=True)
        return github_times(activity_pages(r.stdout))
    raise ValueError(source)


def log_lines(remote, branch, work):
    """The branch's SEALS.txt, line by line, with the commit that added each line (first-parent history)."""
    work = Path(work)
    if not (work / ".git").exists():
        work.mkdir(parents=True, exist_ok=True)
        git("init", "-q", cwd=work)
    git("fetch", "-q", str(remote), f"refs/heads/{branch}", cwd=work)
    commits = git("rev-list", "--first-parent", "--reverse", "FETCH_HEAD", cwd=work).stdout.split()
    out, prev = [], b""
    for c in commits:
        cur = git("show", f"{c}:{LOG}", cwd=work).stdout.encode()
        assert cur.startswith(prev), f"{c}: the seal log was rewritten, not appended to"
        for line in cur[len(prev):].decode().splitlines():
            inst, h, t = line.split()
            out.append(dict(instance=inst, seal_sha256=h, machine_utc=t, commit=c))
        prev = cur
    return out


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c == "push":
        remote, branch, inst, sealdir, work, out, *f = a
        sys.exit(0 if push(remote, branch, inst, sealdir, work, out, dry="dry=1" in f) else 1)
    elif c == "times":
        remote, branch, source, out = a
        Path(out).write_text(json.dumps(times(remote, branch, source), indent=1, sort_keys=True) + "\n")
    else:
        sys.exit(__doc__)
