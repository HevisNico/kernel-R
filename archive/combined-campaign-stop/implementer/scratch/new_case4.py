def case_scan_verify_record(w):
    """The published scan verify record is READ, not copied by hand (the owner's decision, (n)). On local twins of
    GitHub (bare repositories with main and, per case, a record branch evidence/combined-scan-verify made by
    publish_record), with the campaign stand-in inputs (EXCLUDED.json plus 3 integers as the scan, the campaign's list
    from [block list], both rehearsals):
    - [block announce] verbatim (campaign), every GitHub URL replaced by the case's twin, the local H, HS and VS all
      RIGHT (VS = HS): the owner's decisive cases, each refused before any commit (no announce_campaign repository, no
      announce ref on the twin): the record absent; the record verifying another hash; its VS another hash; its
      verdict not success; the record branch with two commits. The honest record: the announce is pushed (one commit,
      three files, a /2 announce).
    - analysis.check_scan_verify (analysis.py campaign's GitHub path), with verify_remote() the twin and
      activity_items() the record's activity as GitHub would give it: the honest record created before the announce
      accepted; refused, each with its own message: created after the announce, created at the same second, a
      force_push in its activity, a branch_deletion, its oldest item not the branch_creation of its commit, two
      commits, absent, another hash, not success.
    - check_draw's GitHub path (stand-ins for the announce read and the freeze time) reaches it: a record created
      after the announce refuses the campaign draw; rehearsal mode reads no record (a verify_remote that raises is
      never called)."""
    import datetime
    import hashlib
    A = load_analysis("analysis_scan_verify_record")
    C = campaign_inputs(w, "scan_verify_record", A)
    wd = C["wd"]
    checks, out, oks = [], {}, []
    sha_b = lambda b: hashlib.sha256(b).hexdigest()
    utc = lambda t: datetime.datetime.fromtimestamp(t, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    HS = C["scan_sha"]
    other = sha_b(b"another scan")
    GH = "https://github.com/HevisNico/kernel-R"

    def note(label, got, needle, target=ANALYSIS):
        out[label] = got
        oks.append(check(checks, label, got, needle, target, Path(target).exists()))

    def call(f, *a, **k):
        try:
            return "accepted: " + json.dumps(f(*a, **k), sort_keys=True, default=str)[:300]
        except SystemExit as e:
            return str(e)
    src = wd / "main_src"
    src.mkdir()
    G = lambda *a: subprocess.run(["git", *a], cwd=src, capture_output=True, text=True, check=True)
    G("init", "-q", "-b", "main")
    G("config", "user.name", "twin owner")
    G("config", "user.email", "twin-owner@invalid")
    (src / "README").write_text("main\n")
    G("add", ".")
    G("commit", "-q", "-m", "main")

    def twin(label, text=None, commits=1):
        bare = wd / f"twin_{label}.git"
        subprocess.run(["git", "init", "-q", "--bare", str(bare)], check=True)
        G("push", "-q", str(bare), "main")
        commit = publish_record(bare, text, wd / f"record_{label}", commits) if text is not None else None
        return bare, commit
    ok_text = f"the scan is reproduced scan_sha256 {HS} VS {HS}\n"
    records = [
        ("absent", None, 1, f"the scan verify record evidence/combined-scan-verify is absent from"),
        ("another hash", f"the scan is reproduced scan_sha256 {other} VS {other}\n", 1,
         f"the scan verify record evidence/combined-scan-verify verified the scan {other[:12]}, not {HS[:12]}"),
        ("its VS another hash", f"the scan is reproduced scan_sha256 {HS} VS {other}\n", 1,
         f"the scan verify record evidence/combined-scan-verify's reproduction VS {other[:12]} is not {HS[:12]}"),
        ("verdict not success", f"PROBLEM: the reproduced scan has sha256 {other}, not the scan's {HS}\n"
                                f"THE SCAN IS NOT REPRODUCED: no announce, push nothing scan_sha256 {HS} VS {HS}\n", 1,
         "the scan verify record evidence/combined-scan-verify's verdict is not success"),
        ("two commits", ok_text, 2, "the scan verify record evidence/combined-scan-verify has 2 commits"),
        ("honest", ok_text, 1, "announce pushed: evidence/combined-draw-recordtest")]
    camp_list = C["camp"]["list"]
    H = A.sha(camp_list)
    F = C["F"]
    for label, text, n, needle in records:
        bare, commit = twin(label.replace(" ", "_"), text, n)
        fd = wd / f"announce_{label.replace(' ', '_')}"
        fd.mkdir()
        shutil.copy(camp_list, fd / "EXCLUDED_SECOND.json")
        shutil.copy(wd / "EXCLUDED_SECOND_SCAN.json", fd / "EXCLUDED_SECOND_SCAN.json")
        b = freeze_block("announce")
        nurl = b.count(GH)
        b = b.replace(GH, str(bare))
        pre = (f"M=campaign B=evidence/combined-draw-recordtest R=x X=EXCLUDED_SECOND.json SIZES='NOT1=60 ANDOR3=32 XOR3=37' "
               f"H={H} S=EXCLUDED_SECOND_SCAN.json HS={HS} VS={HS}\n")
        r = subprocess.run(["bash", "-c", f"L={HERE}\nF={F}\nPY={PY}\npython() {{ \"$PY\" \"$@\"; }}\n" + pre + b], cwd=fd,
                           capture_output=True, text=True)
        txt = (r.stdout + r.stderr).strip()[-1500:]
        made = (fd / "announce_campaign").exists()
        refs = subprocess.run(["git", "--git-dir", str(bare), "for-each-ref", "--format=%(refname)",
                               "refs/heads/evidence/combined-draw-recordtest"], capture_output=True, text=True).stdout.split()
        out[f"announce twin URLs ({label})"] = nurl
        if label == "honest":
            files = subprocess.run(["git", "--git-dir", str(bare), "ls-tree", "--name-only", refs[0]], capture_output=True,
                                   text=True).stdout.split() if refs else []
            note("[block announce], the honest record: the announce pushed", f"rc {r.returncode}, files {files}: {txt}", needle, fd)
            oks.append(r.returncode == 0 and files == ["DRAW_ANNOUNCE.txt", "EXCLUDED_PUBLISHED.json", "EXCLUDED_SECOND_SCAN.json"])
        else:
            note(f"[block announce], local H/HS/VS right, the record {label}: refused before any commit",
                 f"rc {r.returncode}, announce_campaign exists {made}, twin refs {refs}: {txt}", needle, fd)
            oks.append(r.returncode != 0 and not made and not refs
                       and "REFUSED: the published scan verify record (evidence/combined-scan-verify) is absent, not a "
                           "success, or not HS" in txt)
    # ---- analysis.check_scan_verify, the GitHub path, on twins
    push = C["camp"]["push_utc"]                       # the campaign announce's push time (2026-11-28T00:00:00Z)
    t_push = int(datetime.datetime.strptime(push, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=datetime.timezone.utc).timestamp())
    saved = A.verify_remote, A.activity_items
    try:
        def run(label, bare, items, needle):
            A.verify_remote = lambda: str(bare)
            A.activity_items = lambda remote, branch, outdir: items
            note("analysis.check_scan_verify: " + label, call(A.check_scan_verify, HS, push, wd / "a_out"), needle)
        bare_ok, c_ok = twin("a_honest", ok_text)
        item = lambda kind, after, t: dict(activity_type=kind, after=after, before="0" * 40,
                                           ref="refs/heads/evidence/combined-scan-verify", timestamp=utc(t))
        run("the honest record, created before the announce: accepted", bare_ok,
            [item("branch_creation", c_ok, t_push - 3600)], f'"commit": "{c_ok}"')
        run("created after the announce: refused", bare_ok, [item("branch_creation", c_ok, t_push + 60)],
            f"the scan verify record evidence/combined-scan-verify was created at {utc(t_push + 60)}, not before the campaign announce")
        run("created at the announce's second: refused (strictly earlier)", bare_ok, [item("branch_creation", c_ok, t_push)],
            "not before the campaign announce")
        run("a force_push in its activity: refused", bare_ok,
            [item("branch_creation", c_ok, t_push - 3600), item("force_push", c_ok, t_push - 1800)],
            "the scan verify record evidence/combined-scan-verify is not single-use: force_push in its activity")
        run("a branch_deletion in its activity: refused", bare_ok,
            [item("branch_creation", c_ok, t_push - 3600), item("branch_deletion", c_ok, t_push - 1800)],
            "is not single-use: branch_deletion in its activity")
        run("its oldest item not the branch_creation of its commit: refused", bare_ok,
            [item("branch_creation", "f" * 40, t_push - 3600)],
            "the oldest activity item of the scan verify record evidence/combined-scan-verify is not the branch_creation")
        run("no activity: refused", bare_ok, [], "GitHub records no activity for the scan verify record")
        for label, text, n, needle in records[:5]:
            bare, commit = twin("a_" + label.replace(" ", "_"), text, n)
            run(f"the record {label}: refused", bare, [item("branch_creation", commit or "0" * 40, t_push - 3600)], needle)
        # ---- check_draw's GitHub path reaches it; rehearsal mode reads no record
        camp, lb, sb = C["camp"], C["camp"]["list"].read_bytes(), (wd / "EXCLUDED_SECOND_SCAN.json").read_bytes()
        s_ab, s_fr = A.announce_on_github, A.freeze_time
        try:
            A.announce_on_github = lambda branch, outdir, files=None: ("0" * 40, camp["announce"].read_bytes(), camp["push_utc"],
                                                                       {"EXCLUDED_PUBLISHED.json": lb, "EXCLUDED_SECOND_SCAN.json": sb})
            A.freeze_time = lambda tree_commit, outdir: "2026-01-01T00:00:00Z"
            A.verify_remote = lambda: str(bare_ok)
            for label, t, needle in (("the record created before the announce: accepted", t_push - 3600, '"scan_verify": {"branch": "evidence/combined-scan-verify"'),
                                     ("the record created after the announce: refused", t_push + 60, "not before the campaign announce")):
                A.activity_items = lambda remote, branch, outdir, t=t: [item("branch_creation", c_ok, t)]
                got = call(lambda: {k: v for k, v in A.check_draw(dict(draw=str(camp["draw_file"]), excluded=str(camp["list"]),
                                                                       second_scan=str(wd / "EXCLUDED_SECOND_SCAN.json")),
                                                                  "campaign", wd / "a_out", "x")[1].items() if k == "scan_verify"})
                note("check_draw (campaign, GitHub path): " + label, got, needle)
            r2 = C["r2"]
            A.announce_on_github = lambda branch, outdir, files=None: ("0" * 40, r2["announce"].read_bytes(), r2["push_utc"],
                                                                       {"EXCLUDED_PUBLISHED.json": r2["list"].read_bytes()})

            def boom():
                raise AssertionError("rehearsal mode read the scan verify record")
            A.verify_remote = boom
            got = call(lambda: sorted(A.check_draw(dict(draw=str(r2["draw_file"]), excluded=str(r2["list"])), "rehearsal",
                                                   wd / "a_out", "x")[1]))
            note("check_draw (rehearsal, GitHub path): no record read", got, "accepted: ")
            oks.append("scan_verify" not in got)
        finally:
            A.announce_on_github, A.freeze_time = s_ab, s_fr
    finally:
        A.verify_remote, A.activity_items = saved
    return all(oks), dict(checks=checks, results=out)
