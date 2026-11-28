def case_scan_verify_record(w):
    """The published scan verify record is READ, by ONE shared reader (analysis.scan_verify_record), in [block announce]
    and in analysis.py campaign (check_scan_verify), and its branch's history checked (analysis.record_created): the
    owner's decisions after review #3 (M1, L1, L2, L4). On local twins of GitHub (bare repositories with main, the
    record branch made by publish_record, and its activity in <twin>/ACTIVITY, which analysis.record_activity reads for
    a non-GitHub remote), with the campaign stand-in inputs (EXCLUDED.json plus 3 integers as the scan, the campaign's
    list from [block list]):
    - [block announce] verbatim (campaign), every GitHub URL replaced by the case's twin, the local H, HS and VS RIGHT:
      each case refused BEFORE any commit (no announce_campaign repository, no announce ref on the twin), with its own
      message: the record absent; reduced to the single success line (3 files absent); citing another freeze; one
      inventory branch with the right name and the wrong SHA; a PROBLEM line before the success line; the success line
      not alone; VERIFY.txt of another hash, VS another; the verdict not success; inputs of another scan, of another
      draw_seeds.py or analysis.py than FREEZE_PINS.json's, an inventory's listed sha256 not its file's, VERIFY_INPUTS.txt
      of the old format /1 (no git or Python version); two commits; the branch put back onto its first commit after a
      force push away and back, and after a deletion and a recreation (right content, wrong history); an empty F; a
      well-formed other F. The authentic record (control): the announce is pushed (one commit, three files, /2).
    - analysis.check_scan_verify (the GitHub path of analysis.py campaign, verify_remote() the twin): the authentic
      record, created before the announce, accepted; refused: created after the announce, or at its second; the two
      forbidden-move histories; two commits; and the same reader's refusals (3 files absent, another freeze, a wrong
      inventory SHA, a PROBLEM line, an empty F, another F).
    - check_draw's GitHub path (stand-ins for the announce read and the freeze time) reaches it, with the freeze from
      its tree_commit and the scan from the announce commit: a record created after the announce refuses; rehearsal
      mode reads no record."""
    import datetime
    import hashlib
    A = load_analysis("analysis_scan_verify_record")
    C = campaign_inputs(w, "scan_verify_record", A)
    wd = C["wd"]
    checks, out, oks = [], {}, []
    sha_b = lambda b: hashlib.sha256(b).hexdigest()
    utc = lambda t: datetime.datetime.fromtimestamp(t, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    HS = C["scan_sha"]
    F = C["F"]
    other = sha_b(b"another scan")
    otherF = "1" * 40
    GH = "https://github.com/HevisNico/kernel-R"
    scan_b = (wd / "EXCLUDED_SECOND_SCAN.json").read_bytes()

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
    auth = authentic_record(scan_b, F)
    inv = ls_heads_of(json.loads(scan_b))
    first = inv.splitlines()[0]
    wrong_inv = inv.replace(first, "f" * 40 + first[40:], 1)
    branch0 = first.split("refs/heads/")[1]
    t_created, t_push = "2026-11-27T23:00:00Z", C["camp"]["push_utc"]

    def twin(label, files=None, commits=1, history=None):
        """A twin of GitHub: main, and the record (files; commits; history: None = its one branch_creation, or a list of
        (kind, after-or-None for the record's commit, utc))."""
        bare = wd / f"twin_{label}.git"
        subprocess.run(["git", "init", "-q", "--bare", str(bare)], check=True)
        G("push", "-q", str(bare), "main")
        commit = None
        if files is not None:
            commit = publish_record(bare, files, wd / f"record_{label}", commits, created=t_created)
            if history is not None:
                twin_activity(bare, [activity_item(k, a or commit, u) for k, a, u in history])
        return bare, commit
    forced = [("branch_creation", None, t_created), ("force_push", "e" * 40, "2026-11-27T23:10:00Z"),
              ("force_push", None, "2026-11-27T23:20:00Z")]
    recreated = [("branch_creation", None, t_created), ("branch_deletion", "0" * 40, "2026-11-27T23:10:00Z"),
                 ("branch_creation", None, "2026-11-27T23:20:00Z")]
    R = "the scan verify record evidence/combined-scan-verify"
    cases = [   # label, files, commits, history, F, needle (after "refused: ")
        ("absent", None, 1, None, F, f"{R} is absent from"),
        ("(1) reduced to the single success line", {"VERIFY.txt": auth["VERIFY.txt"]}, 1, None, F,
         f"{R} has no VERIFY_INPUTS.txt at its creation commit"),
        ("(2) citing another freeze", authentic_record(scan_b, F, freeze_commit=otherF), 1, None, F,
         f"the scan verify record cites the freeze '{otherF}', not the expected {F}"),
        ("(3) one inventory branch with the right name and the wrong SHA", authentic_record(scan_b, F, verify_lsremote=wrong_inv),
         1, None, F, f"the scan verify record's VERIFY_LSREMOTE.txt is not the scan's inventory: branch {branch0} is at ffffffffffff"),
        ("(3b) the same in SCAN_LSREMOTE.txt", authentic_record(scan_b, F, scan_lsremote=wrong_inv), 1, None, F,
         f"the scan verify record's SCAN_LSREMOTE.txt is not the scan's inventory: branch {branch0} is at ffffffffffff"),
        ("(4) a PROBLEM line before the success line",
         dict(auth, **{"VERIFY.txt": b"PROBLEM: branch x is on the remote but not in the scan\n" + auth["VERIFY.txt"]}), 1, None, F,
         "the scan verify record's VERIFY.txt has a PROBLEM line"),
        ("the success line not alone", dict(auth, **{"VERIFY.txt": b"a note\n" + auth["VERIFY.txt"]}), 1, None, F,
         "the scan verify record's VERIFY.txt is not exactly the success line (2 lines)"),
        ("VERIFY.txt of another hash", dict(auth, **{"VERIFY.txt": f"the scan is reproduced scan_sha256 {other} VS {other}\n".encode()}),
         1, None, F, f"{R} verified the scan {other[:12]}, not {HS[:12]}"),
        ("VERIFY.txt's VS another", dict(auth, **{"VERIFY.txt": f"the scan is reproduced scan_sha256 {HS} VS {other}\n".encode()}),
         1, None, F, f"{R}'s reproduction VS {other[:12]} is not {HS[:12]}"),
        ("the verdict not success", dict(auth, **{"VERIFY.txt": f"THE SCAN IS NOT REPRODUCED: no announce, push nothing scan_sha256 {HS} VS {HS}\n".encode()}),
         1, None, F, "the scan verify record's verdict is not success"),
        ("the inputs of another scan", authentic_record(scan_b, F, reproduced_scan_sha256=other), 1, None, F,
         f"VERIFY_INPUTS.txt: reproduced_scan_sha256 {other[:12]} is not HS {HS[:12]}"),
        ("another analysis.py than FREEZE_PINS.json's", authentic_record(scan_b, F, analysis_py_sha256=other), 1, None, F,
         f"VERIFY_INPUTS.txt: analysis_py_sha256 {other[:12]} is not FREEZE_PINS.json's"),
        ("another draw_seeds.py than FREEZE_PINS.json's", authentic_record(scan_b, F, draw_seeds_py_sha256=other), 1, None, F,
         f"VERIFY_INPUTS.txt: draw_seeds_py_sha256 {other[:12]} is not FREEZE_PINS.json's"),
        ("an inventory's listed sha256 not its file's", authentic_record(scan_b, F, scan_lsremote_sha256=other), 1, None, F,
         "VERIFY_INPUTS.txt: scan_lsremote_sha256 is not the sha256 of its SCAN_LSREMOTE.txt"),
        ("VERIFY_INPUTS.txt of format /1, no versions",
         dict(auth, **{"VERIFY_INPUTS.txt": b"".join(ln + b"\n" for ln in auth["VERIFY_INPUTS.txt"].splitlines()
                                                      if not ln.startswith((b"git_version", b"python_version"))).replace(b"/2", b"/1")}),
         1, None, F, "the scan verify record's VERIFY_INPUTS.txt is not exactly the lines"),
        ("two commits", auth, 2, None, F, f"{R} has 2 commits"),
        ("(5) put back onto its first commit after a force push away and back", auth, 1, forced, F,
         f"{R} is not single-use: force_push in its activity"),
        ("(5b) put back after a deletion and a recreation", auth, 1, recreated, F,
         f"{R} is not single-use: branch_deletion in its activity"),
        ("(6) an empty F", auth, 1, None, "", "the expected freeze commit '' is not a full 40-hex SHA"),
        ("(6b) a well-formed other F", auth, 1, None, otherF, f"the scan verify record cites the freeze '{F}', not the expected {otherF}"),
        ("the authentic record (control)", auth, 1, None, F, "announce pushed: evidence/combined-draw-recordtest")]
    camp_list = C["camp"]["list"]
    H = A.sha(camp_list)
    for label, files, n, history, fv, needle in cases:
        tag = "".join(c if c.isalnum() else "_" for c in label)[:40]
        bare, commit = twin("b_" + tag, files, n, history)
        fd = wd / f"announce_{tag}"
        fd.mkdir()
        shutil.copy(camp_list, fd / "EXCLUDED_SECOND.json")
        shutil.copy(wd / "EXCLUDED_SECOND_SCAN.json", fd / "EXCLUDED_SECOND_SCAN.json")
        b = freeze_block("announce")
        out[f"announce twin URLs ({label})"] = b.count(GH)
        b = b.replace(GH, str(bare))
        pre = (f"M=campaign B=evidence/combined-draw-recordtest R=x X=EXCLUDED_SECOND.json SIZES='NOT1=60 ANDOR3=32 XOR3=37' "
               f"H={H} S=EXCLUDED_SECOND_SCAN.json HS={HS} VS={HS}\n")
        r = subprocess.run(["bash", "-c", f"L={HERE}\nF={fv}\nPY={PY}\npython() {{ \"$PY\" \"$@\"; }}\n" + pre + b], cwd=fd,
                           capture_output=True, text=True)
        txt = (r.stdout + r.stderr).strip()[-1500:]
        made = (fd / "announce_campaign").exists()
        refs = subprocess.run(["git", "--git-dir", str(bare), "for-each-ref", "--format=%(refname)",
                               "refs/heads/evidence/combined-draw-recordtest"], capture_output=True, text=True).stdout.split()
        if label.startswith("the authentic"):
            files_ = subprocess.run(["git", "--git-dir", str(bare), "ls-tree", "--name-only", refs[0]], capture_output=True,
                                    text=True).stdout.split() if refs else []
            note("[block announce]: " + label + ": the announce pushed", f"rc {r.returncode}, files {files_}: {txt}", needle, fd)
            oks.append(r.returncode == 0 and files_ == ["DRAW_ANNOUNCE.txt", "EXCLUDED_PUBLISHED.json", "EXCLUDED_SECOND_SCAN.json"])
        else:
            note(f"[block announce], local H/HS/VS right, {label}: refused before any commit",
                 f"rc {r.returncode}, announce_campaign exists {made}, twin refs {refs}: {txt}", "refused: " + needle, fd)
            oks.append(r.returncode != 0 and not made and not refs and "REFUSED: the published scan verify record "
                       "(evidence/combined-scan-verify) does not verify HS" in txt)
    # ---- analysis.check_scan_verify (analysis.py campaign's GitHub path), verify_remote() the twin
    saved = A.verify_remote
    try:
        def run(label, bare, needle, freeze=F, push=t_push):
            A.verify_remote = lambda: str(bare)
            note("analysis.check_scan_verify: " + label, call(A.check_scan_verify, HS, push, wd / "a_out", scan_b, freeze), needle)
        bare_ok, c_ok = twin("a_authentic", auth)
        run("the authentic record, created before the announce: accepted", bare_ok, f'"commit": "{c_ok}", "created_utc": "{t_created}"')
        run("created after the announce: refused", bare_ok,
            f"{R} was created at {t_created}, not before the campaign announce (2026-11-27T22:00:00Z)", push="2026-11-27T22:00:00Z")
        run("created at the announce's second: refused (strictly earlier)", bare_ok, "not before the campaign announce", push=t_created)
        for label, files, n, history, fv, needle in cases:
            if label.startswith(("(1)", "(2)", "(3)", "(4)", "(5)", "(5b)", "(6)", "(6b)", "two commits", "absent")):
                tag = "".join(c if c.isalnum() else "_" for c in label)[:40]
                bare, commit = twin("a_" + tag, files, n, history)
                run(label + ": refused", bare, needle, freeze=fv)
        # ---- check_draw's GitHub path reaches it; rehearsal mode reads no record
        camp, lb = C["camp"], C["camp"]["list"].read_bytes()
        s_ab, s_fr = A.announce_on_github, A.freeze_time
        try:
            A.announce_on_github = lambda branch, outdir, files=None: ("0" * 40, camp["announce"].read_bytes(), camp["push_utc"],
                                                                       {"EXCLUDED_PUBLISHED.json": lb, "EXCLUDED_SECOND_SCAN.json": scan_b})
            A.freeze_time = lambda tree_commit, outdir: "2020-01-01T00:00:00Z"   # before both stand-in announces
            for label, history, needle in (("the record created before the announce: accepted", None,
                                            '"scan_verify": {"branch": "evidence/combined-scan-verify"'),
                                           ("the record created after the announce: refused",
                                            [("branch_creation", None, "2026-11-28T00:01:00Z")], "not before the campaign announce")):
                bare, commit = twin("d_" + label[:24].replace(" ", "_"), auth, 1, history)
                A.verify_remote = lambda bare=bare: str(bare)
                got = call(lambda: {k: v for k, v in A.check_draw(dict(draw=str(camp["draw_file"]), excluded=str(camp["list"]),
                                                                       second_scan=str(wd / "EXCLUDED_SECOND_SCAN.json")),
                                                                  "campaign", wd / "a_out", F)[1].items() if k == "scan_verify"})
                note("check_draw (campaign, GitHub path): " + label, got, needle)
            r2 = C["r2"]
            A.announce_on_github = lambda branch, outdir, files=None: ("0" * 40, r2["announce"].read_bytes(), r2["push_utc"],
                                                                       {"EXCLUDED_PUBLISHED.json": r2["list"].read_bytes()})

            def boom():
                raise AssertionError("rehearsal mode read the scan verify record")
            A.verify_remote = boom
            got = call(lambda: sorted(A.check_draw(dict(draw=str(r2["draw_file"]), excluded=str(r2["list"])), "rehearsal",
                                                   wd / "a_out", F)[1]))
            note("check_draw (rehearsal, GitHub path): no record read", got, "accepted: ")
            oks.append("scan_verify" not in got)
        finally:
            A.announce_on_github, A.freeze_time = s_ab, s_fr
    finally:
        A.verify_remote = saved
    return all(oks), dict(checks=checks, results=out)
