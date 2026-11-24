"""The coordinator's timestamped ls-remote log of every seal branch (fallback push-time source, 2026-11-24).
Development only.

  seal_watch.py watch REMOTE LOG [interval=20] [stop=FILE]    poll until FILE exists (or forever)
  seal_watch.py once REMOTE LOG                               one poll

Each poll runs `git ls-remote REMOTE refs/heads/evidence/combined-seals-*` and appends a line
`<UTC time> <ref> <sha>` for every (ref, sha) pair not seen before, so each branch tip appears once, at the first
poll that saw it.
- The first-seen time is an UPPER bound of the push time: the push happened at or before it.
- So "first seen before stage N started" implies "pushed before stage N started". The check is conservative; its
  resolution is the polling interval.
- The coordinator commits and pushes LOG during the campaign: the log's own GitHub history then fixes its lines in time.
analyze3 reads it with `times=lsremote:<LOG>` (sealpush.times).
"""
import datetime
from pathlib import Path
import subprocess
import sys
import time

PATTERN = "refs/heads/evidence/combined-seals-*"


def utc():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%fZ")


def seen(log):
    out = set()
    if Path(log).exists():
        for line in Path(log).read_text().splitlines():
            t, ref, sha = line.split()
            out.add((ref, sha))
    return out


def poll(remote, log):
    r = subprocess.run(["git", "ls-remote", str(remote), PATTERN], capture_output=True, text=True)
    if r.returncode:
        return 0
    have, n, t = seen(log), 0, utc()
    with Path(log).open("a") as f:
        for line in r.stdout.splitlines():
            sha, ref = line.split()
            if (ref, sha) not in have:
                f.write(f"{t} {ref} {sha}\n")
                n += 1
    return n


def times(log, branch):
    """{sha: first-seen UTC} for refs/heads/<branch>."""
    out = {}
    for line in Path(log).read_text().splitlines() if Path(log).exists() else []:
        t, ref, sha = line.split()
        if ref == f"refs/heads/{branch}":
            out.setdefault(sha, t)
    return out


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c == "once":
        print(poll(a[0], a[1]))
    elif c == "watch":
        remote, log, *rest = a
        kw = dict(x.split("=", 1) for x in rest)
        while not (kw.get("stop") and Path(kw["stop"]).exists()):
            poll(remote, log)
            time.sleep(float(kw.get("interval", 20)))
    else:
        sys.exit(__doc__)
