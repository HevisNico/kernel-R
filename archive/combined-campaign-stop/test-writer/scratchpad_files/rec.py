# The scan verify record (the implementer's interface at 7fa3693e): four files (VERIFY_FILES) on the single creation
# commit of evidence/combined-scan-verify. The AUTHENTIC record is made by the blocks themselves, on a fresh twin per
# case: [block second-scan] then [block verify-scan], verbatim, in a second-machine folder (their push goes to the
# twin). The record branch's history, which GitHub keeps, is the twin's ACTIVITY/<branch, "/" as "__">.json, written
# by the test (analysis.record_created reads it for a path remote). Doctored records are the authentic commit with
# files changed, amended (one commit still) and put on the twin by a local push.
# [block announce] reads the record from its literal https://github.com/HevisNico/kernel-R. Its git commands reach
# the twin by url.insteadOf; its two record reads (analysis.scan_verify_record and analysis.record_created) are given
# the twin's path by a usercustomize.py shim (TWIN_SHIM, nothing else replaced), so that no GitHub API is asked.
VERIFY_BRANCH = "evidence/combined-scan-verify"
GITHUB_URL = "https://github.com/HevisNico/kernel-R"
TWIN_SHIM = '''"""The defect tests' twin shim: analysis's two record reads on the GitHub URL go to the twin's path."""
import importlib.machinery, os, sys
TWIN, URL = os.environ["LAYERED_TWIN_REMOTE"], "https://github.com/HevisNico/kernel-R"


def patch(A):
    for name in ("scan_verify_record", "record_created"):
        f = getattr(A, name)

        def g(remote, *a, _f=f, _n=name, **k):
            if remote == URL:
                print(f"twin shim: {_n} reads {TWIN}", file=sys.stderr)
                remote = TWIN
            return _f(remote, *a, **k)
        setattr(A, name, g)


class Hook:
    def find_spec(self, name, path=None, target=None):
        if name != "analysis":
            return None
        sys.meta_path.remove(self)
        spec = importlib.machinery.PathFinder.find_spec(name, path)
        run = spec.loader.exec_module

        def exec_module(m):
            run(m)
            patch(m)
        spec.loader.exec_module = exec_module
        return spec


sys.meta_path.insert(0, Hook())
'''
OTHER_FREEZE = "da3d9b3b1f22b312eab3a4aaa67d06abf47f2c45"   # a real commit of this repository, not the tree's


def utc_of(t):
    import datetime
    return datetime.datetime.fromtimestamp(t, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def write_activity(bare, items):
    d = bare / "ACTIVITY"
    d.mkdir(exist_ok=True)
    (d / (VERIFY_BRANCH.replace("/", "__") + ".json")).write_text(json.dumps(items, indent=1) + "\n")


def creation(commit, t):
    return dict(activity_type="branch_creation", after=commit, before="0" * 40, ref=f"refs/heads/{VERIFY_BRANCH}",
                timestamp=utc_of(t))


def authentic_record(tmp, extra_vars=()):
    """A fresh twin with the authentic record pushed by [block verify-scan]. Returns (bare, env, hs, commit, obs)."""
    vb = vs_base(tmp)
    bare = tmp / "twin.git"
    shutil.copytree(vb["bare"], bare)
    env = twin_env(tmp, bare)
    m2 = tmp / "second_machine"
    m2.mkdir()
    dummy = lambda n, d: "0" * 64
    r2, o2 = bash_blocks(m2, env, ["second-scan"], dummy)
    (m2 / "SCAN_TO_VERIFY.json").write_bytes(vb["scan"])
    rv, ov = bash_blocks(m2, env, ["verify-scan"], dummy, extra_vars)
    got = subprocess.run(["git", "-C", str(bare), "rev-parse", "-q", "--verify", f"refs/heads/{VERIFY_BRANCH}"],
                         capture_output=True, text=True)
    commit = got.stdout.strip() if got.returncode == 0 else None
    return bare, env, hashlib.sha256(vb["scan"]).hexdigest(), commit, dict(second_scan=o2, verify=ov)


def rewrite_record(bare, tmp, edit):
    """The record commit with its files passed through edit({name: text}) -> {name: text or None (removed)}, amended
    (still one commit), pushed to the twin. Returns the new commit."""
    work = tmp / "record_edit"
    git("clone", "-q", "--branch", VERIFY_BRANCH, str(bare), str(work))
    files = {f.name: f.read_text() for f in work.iterdir() if f.is_file()}
    new = edit(dict(files))
    for n, t in new.items():
        if t is None:
            (work / n).unlink()
        elif t != files.get(n):
            (work / n).write_text(t)
    ident = ["-c", "user.name=defect test", "-c", "user.email=defect-test@localhost"]
    git("add", "-A", cwd=work)
    git(*ident, "commit", "-q", "--amend", "--no-edit", cwd=work)
    git("push", "-q", "--force", "origin", f"HEAD:refs/heads/{VERIFY_BRANCH}", cwd=work)
    return git("rev-parse", "HEAD", cwd=work).strip()


def inputs_edit(key, value):
    def edit(files):
        files["VERIFY_INPUTS.txt"] = "".join(f"{key} {value}\n" if ln.split(" ", 1)[0] == key else ln + "\n"
                                             for ln in files["VERIFY_INPUTS.txt"].splitlines())
        return files
    return edit


def lsremote_edit(name, key):
    """One branch line of the inventory `name` at the right name and another commit's sha (the sha of the twin's
    main), and the input key naming the new file's sha256, so that only the inventory check can refuse."""
    def edit(files):
        lines = files[name].splitlines()
        main = next(ln.split()[0] for ln in lines if ln.endswith("refs/heads/main"))
        i = next(i for i, ln in enumerate(lines) if not ln.endswith("refs/heads/main") and ln.split()[0] != main)
        lines[i] = main + "\t" + lines[i].split(None, 1)[1]
        files[name] = "\n".join(lines) + "\n"
        return inputs_edit(key, hashlib.sha256(files[name].encode()).hexdigest())(files)
    return edit


# kind: (what, the record's doctoring, its activity relative to its creation commit c at time t)
RECORD_KINDS = {
    None: "the authentic record (control): accepted",
    "absent": "no record branch (the owner's decisive case)",
    "other_hash": "the record naming another scan sha256 everywhere HS appears (the owner's decisive case)",
    "not_success": "the record's verdict rewritten to the failure verdict",
    "success_only": "(1) the record reduced to the single success line (VERIFY.txt alone)",
    "other_freeze": "(2) a complete record citing another freeze commit",
    "empty_freeze": "(2b) an empty F given to the read",
    "verify_lsremote_sha": "(3) VERIFY_LSREMOTE.txt with one branch at its right name and another sha",
    "scan_lsremote_sha": "(3b) the same in SCAN_LSREMOTE.txt",
    "problem_line": "(4) a PROBLEM line before the success line",
    "force_back": "(5) the branch force-pushed away and back onto its creation commit",
    "recreate": "(5b) the branch deleted and recreated on the same commit",
    "other_analysis_sha": "(6) VERIFY_INPUTS.txt naming another analysis.py sha256",
}
RECORD_ANALYSIS_ONLY = {
    "after": "the record created after the campaign announce",
    "same_time": "the record created at the announce's own push time (not strictly before)",
    "second_commit": "the record branch with a second commit on top of its creation commit",
}
RECORD_MESSAGE = {
    "absent": "the scan verify record evidence/combined-scan-verify is absent from",
    "other_hash": ("verified the scan", "is not exactly the success line"),
    "not_success": ("verdict is not success", "is not exactly the success line"),
    "success_only": ("has no VERIFY_INPUTS.txt at its creation commit", "has no VERIFY_LSREMOTE.txt at its creation",
                     "has no SCAN_LSREMOTE.txt at its creation"),
    "other_freeze": "the scan verify record cites the freeze",
    "empty_freeze": "the expected freeze commit '' is not a full 40-hex SHA",
    "verify_lsremote_sha": "VERIFY_LSREMOTE.txt is not the scan's inventory",
    "scan_lsremote_sha": "SCAN_LSREMOTE.txt is not the scan's inventory",
    "problem_line": "has a PROBLEM line",
    "force_back": "is not single-use: force_push in its activity",
    "recreate": "is not single-use: branch_deletion in its activity",
    "other_analysis_sha": "is not FREEZE_PINS.json's",
    "after": "not before the campaign announce",
    "same_time": "not before the campaign announce",
    "second_commit": "has 2 commits",
}
BLOCK_REFUSAL = "REFUSED: the published scan verify record (evidence/combined-scan-verify) does not verify HS ("


def doctor_record(tmp, kind, t_created):
    """The case's twin: the authentic record doctored by `kind`, and the twin's ACTIVITY. Returns (bare, env, hs,
    obs)."""
    bare, env, hs, c, obs = authentic_record(tmp)
    if c is None:
        return bare, env, hs, dict(obs, setup="verify-scan pushed no record")
    edit = {
        "other_hash": lambda f: {n: t.replace(hs, hashlib.sha256(b"another scan").hexdigest()) for n, t in f.items()},
        "not_success": lambda f: dict(f, **{"VERIFY.txt": f["VERIFY.txt"].replace(
            "the scan is reproduced", "THE SCAN IS NOT REPRODUCED: no announce, push nothing")}),
        "success_only": lambda f: {n: (t if n == "VERIFY.txt" else None) for n, t in f.items()},
        "other_freeze": inputs_edit("freeze_commit", OTHER_FREEZE),
        "verify_lsremote_sha": lsremote_edit("VERIFY_LSREMOTE.txt", "verify_lsremote_sha256"),
        "scan_lsremote_sha": lsremote_edit("SCAN_LSREMOTE.txt", "scan_lsremote_sha256"),
        "problem_line": lambda f: dict(f, **{"VERIFY.txt": "PROBLEM: a problem the verification found\n" + f["VERIFY.txt"]}),
        "other_analysis_sha": inputs_edit("analysis_py_sha256", hashlib.sha256(b"another analysis.py").hexdigest()),
    }.get(kind)
    if edit is not None:
        c = rewrite_record(bare, tmp, edit)
    items = [creation(c, t_created)]
    if kind == "absent":
        git("update-ref", "-d", f"refs/heads/{VERIFY_BRANCH}", cwd=bare)
        items = []
    elif kind == "force_back":
        other = git("rev-parse", "refs/heads/main", cwd=bare).strip()
        items += [dict(items[0], activity_type="force_push", after=other, before=c, timestamp=utc_of(t_created + 10)),
                  dict(items[0], activity_type="force_push", after=c, before=other, timestamp=utc_of(t_created + 20))]
    elif kind == "recreate":
        items += [dict(items[0], activity_type="branch_deletion", after="0" * 40, before=c, timestamp=utc_of(t_created + 10)),
                  dict(items[0], timestamp=utc_of(t_created + 20))]
    elif kind == "second_commit":
        work = tmp / "record_child"
        git("clone", "-q", "--branch", VERIFY_BRANCH, str(bare), str(work))
        (work / "NOTE.txt").write_text("a second commit\n")
        git("add", ".", cwd=work)
        git("-c", "user.name=defect test", "-c", "user.email=defect-test@localhost", "commit", "-q", "-m", "second",
            cwd=work)
        git("push", "-q", "origin", f"HEAD:refs/heads/{VERIFY_BRANCH}", cwd=work)
        tip = git("rev-parse", "HEAD", cwd=work).strip()
        items.append(dict(items[0], activity_type="push", after=tip, before=c, timestamp=utc_of(t_created + 10)))
    write_activity(bare, items)
    obs.update(record_commit=c, activity=[x["activity_type"] for x in items],
               record_files=sorted(git("ls-tree", "--name-only", f"refs/heads/{VERIFY_BRANCH}", cwd=bare).split())
               if kind != "absent" else [])
    return bare, env, hs, obs


def first_machine(tmp, hs_scan):
    """The first machine's folder: the twin's scan as EXCLUDED_SECOND_SCAN.json, the campaign list rebuilt by
    [block list]."""
    w, name, _ = list_case_files(tmp, "campaign", None)
    (w / "EXCLUDED_SECOND_SCAN.json").write_bytes(hs_scan)
    (w / name).unlink()
    bl = run_block(w, "list", {})
    assert bl["exit"] == 0, bl
    return w, name


RECORD_BLOCK_CONTROL = {}


def record_block_case(kind):
    """[block announce] (campaign) on the case's twin, H/HS/VS right. Exact: pushed, a /2 announce naming HS.
    Refused: exit 1, the block's REFUSED line, analysis's refusal (pinned), no announce folder, no announce ref on the
    twin. scan_byte: the scan copy with one byte changed after HS was kept."""
    def case(tmp, src):
        bare, env, hs, obs = doctor_record(tmp, kind if kind != "scan_byte" else None, time.time() - 3600)
        vb = vs_base(tmp)
        w, name = first_machine(tmp, vb["scan"])
        if kind == "scan_byte":
            b = bytearray((w / "EXCLUDED_SECOND_SCAN.json").read_bytes())
            i = b.index(b'"rule":"') + len(b'"rule":"')
            b[i] = ord("x") if b[i] != ord("x") else ord("y")
            (w / "EXCLUDED_SECOND_SCAN.json").write_bytes(bytes(b))
        shim = tmp / "twin_shim"
        shim.mkdir()
        (shim / "usercustomize.py").write_text(TWIN_SHIM)
        env = dict(env, PYTHONPATH=str(shim), LAYERED_TWIN_REMOTE=str(bare))
        fill = lambda n, d: sha(w / name) if n == "H" else hs if n in ("HS", "VS") else None
        ra, oa = bash_blocks(w, env, ["announce"], fill, ('F=""',) if kind == "empty_freeze" else ())
        pushed = subprocess.run(["git", "-C", str(bare), "rev-parse", "-q", "--verify", "refs/heads/evidence/combined-draw"],
                                capture_output=True).returncode == 0
        obs.update(announce=oa, kind=kind, HS=hs, expected=RECORD_KINDS.get(kind, kind),
                   announce_folder_made=(w / "announce_campaign").exists(), pushed_to_twin=pushed,
                   shim_lines=[x for x in oa.get("stderr", "").splitlines() if x.startswith("twin shim:")],
                   block_line=next((x for x in oa.get("stdout", "").splitlines() if "REFUSED" in x), None),
                   message=next((x for x in oa.get("stderr", "").splitlines() if x.startswith("refused:")), None))
        if ra is None:
            return False, obs
        if kind is None:
            ann = subprocess.run(["git", "-C", str(bare), "show", "refs/heads/evidence/combined-draw:DRAW_ANNOUNCE.txt"],
                                 capture_output=True, text=True).stdout
            obs["announce_pushed"] = ann
            RECORD_BLOCK_CONTROL["ok"] = ok = (ra.returncode == 0 and pushed and bool(obs["shim_lines"])
                                               and f"second_scan_sha256 {hs}\n" in ann and not oa["unknown_placeholders"])
            return ok, obs
        obs["control_passed"] = RECORD_BLOCK_CONTROL.get("ok", False)
        if kind == "scan_byte":
            obs["message"] = obs["block_line"]
            ok = ra.returncode != 0 and obs["block_line"] is not None
        else:
            ok = ra.returncode == 1 and (obs["block_line"] or "").startswith(BLOCK_REFUSAL)
        ok = ok and not obs["announce_folder_made"] and not pushed
        obs["refused_before_announce"] = ok
        return ok and obs["control_passed"], obs
    case.__name__ = f"case_record_block_{kind or 'exact'}"
    return case


RECORD_FUNC = \'\'\'import json, sys, tempfile, traceback
sys.path.insert(0, sys.argv[1])
import analysis as A
a = json.loads(sys.argv[2])
files = {k: (None if v is None else open(v, "rb").read()) for k, v in a["files"].items()}
ann = open(a["announce"], "rb").read()
A.announce_on_github = lambda branch, outdir, files_=None, **k: (a["commit"], ann, a["push_utc"], files)
A.freeze_time = lambda tree_commit, outdir: "2026-11-01T00:00:00Z"
A.verify_remote = lambda: a["record_remote"]
out = dict(reached="check_draw")
try:
    d, info, _ = A.check_draw(a["kw"], "campaign", tempfile.mkdtemp(), a["tree"])
    out.update(reached="accepted", refused=False, scan_verify=info.get("scan_verify"))
except A.Refused as e:
    tb = traceback.extract_tb(e.__traceback__)
    out.update(refused=True, message=str(e), stack=[f.name for f in tb])
print(json.dumps(out))
\'\'\'
RECORD_FUNC_CONTROL = {}
COMMIT_KINDS = {
    None: "the announce commit holds the announced EXCLUDED_PUBLISHED.json and EXCLUDED_SECOND_SCAN.json (control)",
    "no_scan": "the announce commit has no EXCLUDED_SECOND_SCAN.json: refused",
    "scan_differs": "the announce commit's EXCLUDED_SECOND_SCAN.json (announced) is not byte-equal to second_scan=: refused",
}


def record_analysis_run(tmp, kind=None, commit_kind=None):
    """check_draw(kw, "campaign", outdir, F) on its GitHub path: announce_on_github and freeze_time stand-ins (the
    announce commit's files), verify_remote the case's twin (record_created reads its ACTIVITY). The campaign's list is
    rebuilt from the twin's scan, the /2 announce names it; the record is created 1 h before the announce unless kind
    says otherwise. F is this tree's HEAD (the freeze the record cites), "" for empty_freeze."""
    import draw_seeds as DS
    vb = vs_base(tmp)
    w, name = first_machine(tmp, vb["scan"])
    scan = w / "EXCLUDED_SECOND_SCAN.json"
    eb = (w / name).read_bytes()
    files = {"EXCLUDED_PUBLISHED.json": str(w / name), "EXCLUDED_SECOND_SCAN.json": str(scan)}
    named = scan
    if commit_kind == "no_scan":
        files["EXCLUDED_SECOND_SCAN.json"] = None
    elif commit_kind == "scan_differs":
        other = w / "SCAN_IN_COMMIT.json"
        o = json.loads(scan.read_bytes())
        other.write_bytes(DS.canon(regen(o, o["seeds"] + [1000099])))
        files["EXCLUDED_SECOND_SCAN.json"] = named = other
    _, p, t0 = announced_draw(w, "CASE", ROUND_C, json.loads(eb), eb, CAMPAIGN_SIZES, "campaign",
                              "evidence/combined-draw", fmt=2, second_scan_sha256=sha(named))
    created = {"after": t0 + 60, "same_time": t0}.get(kind, t0 - 3600)
    bare, env, hs, obs = doctor_record(tmp, kind, created)
    d = json.loads(Path(p["draw"]).read_text())
    tree = "" if kind == "empty_freeze" else git("rev-parse", "HEAD", cwd=HERE).strip()
    kw = dict(draw=str(p["draw"]), excluded=str(w / name), **{SECOND_SCAN_ARG: str(scan)})
    r = subprocess.run([PY, "-B", "-c", RECORD_FUNC, str(HERE), json.dumps(dict(
        kw=kw, files={k: (None if v is None else str(v)) for k, v in files.items()}, announce=str(p["announce"]),
        commit=d["announce"]["commit"], push_utc=d["announce"]["push_utc"], record_remote=str(bare), tree=tree))],
        capture_output=True, text=True)
    try:
        res = json.loads(r.stdout.strip().splitlines()[-1])
    except (ValueError, IndexError):
        res = dict(crashed=True, stderr=r.stderr[-1500:])
    obs.update(HS=hs, announce_push=d["announce"]["push_utc"], record_created=utc_of(created), tree=tree, **res)
    return res, obs


def record_func_case(kind):
    def case(tmp, src):
        res, obs = record_analysis_run(tmp, kind)
        obs["expected"] = RECORD_KINDS.get(kind) or RECORD_ANALYSIS_ONLY.get(kind)
        if kind is None:
            RECORD_FUNC_CONTROL["ok"] = ok = res.get("reached") == "accepted" and bool(res.get("scan_verify"))
            return ok, obs
        obs["control_passed"] = RECORD_FUNC_CONTROL.get("ok", False)
        return res.get("refused") is True and obs["control_passed"], obs
    case.__name__ = f"case_record_analysis_{kind or 'exact'}"
    return case


COMMIT_CONTROL = {}


def announce_commit_case(kind):
    def case(tmp, src):
        res, obs = record_analysis_run(tmp, None, kind)
        obs["expected_check"] = COMMIT_KINDS[kind]
        if kind is None:
            COMMIT_CONTROL["ok"] = ok = res.get("reached") == "accepted"
            return ok, obs
        obs["control_passed"] = COMMIT_CONTROL.get("ok", False)
        return res.get("refused") is True and obs["control_passed"], obs
    case.__name__ = f"case_announce_commit_{kind or 'exact'}"
    return case


def case_verify_scan_empty_freeze(tmp, src):
    """(2b) [block verify-scan] with an empty F: refused before any record (no record branch on the twin)."""
    bare, env, hs, c, obs = authentic_record(tmp, ('F=""',))
    v = obs["verify"]
    obs["message"] = next((x for x in v.get("stdout", "").splitlines() if "REFUSED" in x), None)
    return v.get("exit") == 1 and c is None and (obs["message"] or "").startswith("REFUSED: F () is not"), obs


