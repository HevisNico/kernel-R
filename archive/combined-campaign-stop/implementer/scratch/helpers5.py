def ls_heads_of(scan):
    """The `git ls-remote --heads` text a scan's refs stand for (refs/remotes/origin/X at T -> `T\trefs/heads/X`)."""
    return "".join(f"{v['tip']}\trefs/heads/{n[len('refs/remotes/origin/'):]}\n"
                   for n, v in sorted(scan["refs"].items()) if n != "HEAD")


def authentic_record(scan_bytes, F, verify_lsremote=None, scan_lsremote=None, **inputs):
    """The four files of an authentic [block verify-scan] record for the scan `scan_bytes` under the freeze F: VERIFY.txt
    the success line, both inventories the scan's own, VERIFY_INPUTS.txt (format /2) with the pinned code sha256
    (FREEZE_PINS.json), both scan sha256, the inventories' sha256, git and Python versions. `inputs` overrides a key."""
    import hashlib
    sha_b = lambda b: hashlib.sha256(b).hexdigest()
    hs = sha_b(scan_bytes)
    inv = ls_heads_of(json.loads(scan_bytes))
    vl = (verify_lsremote if verify_lsremote is not None else inv).encode()
    sl = (scan_lsremote if scan_lsremote is not None else inv).encode()
    pins = {p: h for fs in json.loads((HERE / "FREEZE_PINS.json").read_text())["groups"].values() for p, h in fs.items()}
    kv = dict(format="layered-scan-verify-inputs/2", freeze_commit=F,
              draw_seeds_py_sha256=pins["research/layered-networks/draw_seeds.py"],
              analysis_py_sha256=pins["research/layered-networks/analysis.py"],
              scan_to_verify_sha256=hs, reproduced_scan_sha256=hs, verify_lsremote_sha256=sha_b(vl),
              scan_lsremote_sha256=sha_b(sl), git_version="git version 2.43.0", python_version="3.13.18")
    kv.update(inputs)
    return {"VERIFY.txt": f"the scan is reproduced scan_sha256 {hs} VS {hs}\n".encode(),
            "VERIFY_INPUTS.txt": "".join(f"{k} {v}\n" for k, v in kv.items()).encode(),
            "VERIFY_LSREMOTE.txt": vl, "SCAN_LSREMOTE.txt": sl}


def twin_activity(bare, items):
    """GitHub's activity for the record branch, on a LOCAL twin (analysis.record_activity reads it there)."""
    d = Path(bare) / "ACTIVITY"
    d.mkdir(exist_ok=True)
    (d / "evidence__combined-scan-verify.json").write_text(json.dumps(items, indent=1) + "\n")


def activity_item(kind, after, utc):
    return dict(activity_type=kind, after=after, before="0" * 40, ref="refs/heads/evidence/combined-scan-verify",
                timestamp=utc)


def publish_record(bare, files, folder, commits=1, created="2026-11-27T23:00:00Z"):
    """A scan verify record on the bare repository `bare`: evidence/combined-scan-verify, `commits` commits (single-use:
    one), the last holding `files` (name -> bytes), as [block verify-scan] pushes it; and, unless created is None, the
    twin's activity: one branch_creation of that commit at `created`. Returns the commit."""
    folder.mkdir(parents=True)
    G = lambda *a: subprocess.run(["git", *a], cwd=folder, capture_output=True, text=True, check=True)
    G("init", "-q")
    G("checkout", "-q", "--orphan", "evidence/combined-scan-verify")
    G("config", "user.name", "twin owner")
    G("config", "user.email", "twin-owner@invalid")
    for k in range(commits):
        if k < commits - 1:
            (folder / "EARLIER.txt").write_text(f"an earlier record {k}\n")
            G("add", "EARLIER.txt")
        else:
            for n, b in files.items():
                (folder / n).write_bytes(b)
            G("add", *files)
        G("commit", "-q", "-m", f"Scan verify (campaign) {k}")
    G("push", "-q", str(bare), "HEAD:refs/heads/evidence/combined-scan-verify")
    commit = subprocess.run(["git", "-C", str(folder), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    if created is not None:
        twin_activity(bare, [activity_item("branch_creation", commit, created)])
    return commit
