"""sealpush.py with the sealed prediction folder pushed in the same commit as the log line (the owner's decision,
relayed 2026-11-25). Development only. sealpush.py is kept as it is.

At sealpush time machine A appends its line to SEALS.txt, as sealpush.py does. In the same commit it adds the whole
seal folder under seals/<instance>/: every file SEALDIR/SHA256SUMS lists, and SHA256SUMS itself, byte for byte.
- **Append-only.** SEALS.txt must start with the remote's current file, byte for byte. Every file already on the
  branch must be unchanged. The commit may only add files, which is checked on the commit's own diff against its
  parent before the push.
- **seals/<instance>/ must not exist on the branch already**: a second seal of one instance is refused.
- The push is plain (no force), and its success is checked with ls-remote, as in sealpush.py. Stage N starts only
  after it succeeds.

Machine B (campaign_run10's remote duplicate) fetches the branch by name and checks three things before comparing:
- the commit is on the branch;
- SEALS.txt there has the instance's line with the sha256 of seals/<instance>/SHA256SUMS;
- seal.verify holds on that folder.

  sealpush2.py push REMOTE BRANCH INSTANCE SEALDIR WORKDIR OUT.json [dry=1]
  sealpush2.py fetch REMOTE BRANCH COMMIT INSTANCE DEST      writes DEST (the seal folder at COMMIT), prints its files
  sealpush2.py times REMOTE BRANCH SOURCE OUT.json            as sealpush.py
"""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import sealpush as SP  # noqa: E402

PREFIX = "seals"


def seal_files(sealdir):
    sealdir = Path(sealdir)
    names = [l.split("  ", 1)[1] for l in (sealdir / "SHA256SUMS").read_text().splitlines()]
    return sorted(set(names)) + ["SHA256SUMS"]


def push(remote, branch, instance, sealdir, work, out, dry=False):
    work, out, sealdir = Path(work), Path(out), Path(sealdir)
    res = dict(remote=str(remote), branch=branch, instance=instance, pushed=False, with_seal_folder=True)
    try:
        import seal as sealmod
        try:
            ok = sealmod.verify(sealdir, quiet=True)
        except Exception as e:
            ok = False
            res["verify_error"] = repr(e)
        if not ok:
            raise RuntimeError("the seal does not verify")
        h = SP.seal_sha(sealdir)
        if not (work / ".git").exists():
            work.mkdir(parents=True, exist_ok=True)
            SP.git("init", "-q", cwd=work)
        have = SP.git("ls-remote", str(remote), f"refs/heads/{branch}", cwd=work).stdout.split()
        if have:
            SP.git("fetch", "-q", str(remote), f"refs/heads/{branch}", cwd=work)          # by name
            SP.git("checkout", "-q", "-f", "-B", branch, "FETCH_HEAD", cwd=work)
            SP.git("clean", "-qfdx", cwd=work)
            before = (work / SP.LOG).read_bytes() if (work / SP.LOG).exists() else b""
        else:
            SP.git("checkout", "-q", "--orphan", branch, cwd=work, check=False)
            SP.git("rm", "-rq", "--cached", ".", cwd=work, check=False)
            before = b""
        dest = work / PREFIX / instance
        if dest.exists():
            raise RuntimeError(f"{PREFIX}/{instance} is already on {branch}: a second seal is refused")
        dest.mkdir(parents=True)
        files = seal_files(sealdir)
        for n in files:
            (dest / n).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(sealdir / n, dest / n)
        line = f"{instance} {h} {SP.utc()}\n"
        (work / SP.LOG).write_bytes(before + line.encode())
        assert (work / SP.LOG).read_bytes().startswith(before), "the log is append-only"
        SP.git("add", SP.LOG, f"{PREFIX}/{instance}", cwd=work)
        SP.git("commit", "-q", "-m", f"seal {instance}", cwd=work)
        head = SP.git("rev-parse", "HEAD", cwd=work).stdout.strip()
        if have:                                           # only additions, and SEALS.txt appended
            diff = SP.git("diff", "--name-status", f"{have[0]}..{head}", cwd=work).stdout.split("\n")
            bad = [d for d in diff if d and not d.startswith("A\t") and d != f"M\t{SP.LOG}"]
            if bad:
                raise RuntimeError(f"the commit changes files already on the branch: {bad[:3]}")
        size = sum((dest / n).stat().st_size for n in files)
        res.update(line=line.rstrip("\n"), seal_sha256=h, commit=head, previous=have[0] if have else None,
                   seal_folder=dict(path=f"{PREFIX}/{instance}", files=len(files), bytes=size))
        if dry:
            res["pushed"] = "dry"
        else:
            t0 = SP.utc()
            r = SP.git("push", "-q", str(remote), f"HEAD:refs/heads/{branch}", cwd=work, check=False)
            if r.returncode:
                raise RuntimeError("push rejected: " + r.stderr.strip()[-300:])
            now = SP.git("ls-remote", str(remote), f"refs/heads/{branch}", cwd=work).stdout.split()
            if not now or now[0] != head:
                raise RuntimeError(f"after the push the branch is at {now[:1]}, not {head}")
            res.update(pushed=True, push_started_machine_utc=t0, pushed_at_machine_utc=SP.utc())
    except Exception as e:
        res.update(pushed=False, why=str(e))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    return res["pushed"] is True or (dry and res["pushed"] == "dry")


def fetch(remote, branch, commit, instance, dest):
    """The seal folder seals/<instance>/ at COMMIT of BRANCH, fetched by name. Returns (ok, why)."""
    dest = Path(dest)
    with tempfile.TemporaryDirectory() as g:
        run = lambda *a: subprocess.run(["git", "-C", g, *a], capture_output=True)
        run("init", "-q", "--bare")
        f = run("fetch", "-q", str(remote), f"refs/heads/{branch}:refs/heads/{branch}")
        if f.returncode:
            return False, f"fetch {branch}: {f.stderr.decode(errors='replace').strip()[:200]}"
        if run("merge-base", "--is-ancestor", commit, f"refs/heads/{branch}").returncode:
            return False, f"commit {commit} is not on {branch}"
        ls = run("ls-tree", "-r", "--name-only", commit, f"{PREFIX}/{instance}/")
        names = [n for n in ls.stdout.decode().splitlines() if n]
        if not names:
            return False, f"no {PREFIX}/{instance}/ at {commit}"
        dest.mkdir(parents=True, exist_ok=True)
        for n in names:
            b = run("show", f"{commit}:{n}")
            if b.returncode:
                return False, f"cannot read {n} at {commit}"
            p = dest / n[len(PREFIX) + len(instance) + 2:]
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(b.stdout)
    return True, None


if __name__ == "__main__":
    c, *a = sys.argv[1:] or ["help"]
    if c == "push":
        kw = dict(x.split("=", 1) for x in a[6:])
        sys.exit(0 if push(*a[:6], dry=kw.get("dry") == "1") else 1)
    elif c == "fetch":
        ok, why = fetch(*a)
        print("fetched" if ok else f"refused: {why}")
        sys.exit(0 if ok else 1)
    elif c == "times":
        sys.argv = [str(HERE / "sealpush.py")] + sys.argv[1:]
        import runpy
        runpy.run_path(str(HERE / "sealpush.py"), run_name="__main__")
    else:
        sys.exit(__doc__)
