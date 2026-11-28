def load_analysis(name):
    import importlib.util
    spec = importlib.util.spec_from_file_location(name, ANALYSIS)
    A = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(Path(ANALYSIS).parent))
    spec.loader.exec_module(A)
    return A


def campaign_inputs(w, folder, A):
    """The campaign's offline inputs, as in exact_union_owner: rehearsal 1 as published, rehearsal 2's list from [block
    rehearsal2-list] verbatim, a stand-in rehearsal 2 on round 20000000 over it, a stand-in second scan (EXCLUDED.json
    plus 3 integers), the campaign's list from [block list] verbatim, and a campaign stand-in draw on round 34340412
    announced (/2) on it. Returns a dict of paths and values."""
    import hashlib
    import beacon_chain
    import beacon_verify
    import draw_seeds as D
    fx = HERE / "tests" / "fixtures" / "rehearsal1"
    wd = w.wd / folder
    shutil.rmtree(wd, ignore_errors=True)
    wd.mkdir()
    F = subprocess.run(["git", "-C", str(HERE), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    frz = json.loads((HERE / "EXCLUDED.json").read_text())
    sha_b = lambda b: hashlib.sha256(b).hexdigest()
    utc = lambda t: __import__("datetime").datetime.fromtimestamp(t, __import__("datetime").timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    def block(name):
        r = subprocess.run(["bash", "-c", f"L={HERE}\nF={F}\nPY={PY}\npython() {{ \"$PY\" \"$@\"; }}\n" + freeze_block(name)],
                           cwd=wd, capture_output=True, text=True)
        assert r.returncode == 0, r.stdout + r.stderr
    for src, dst in (("DRAW.json", "DRAW_REHEARSAL1.json"), ("EXCLUDED_PUBLISHED.json", "EXCLUDED_REHEARSAL1.json"),
                     ("DRAW_ANNOUNCE.txt", "ANNOUNCE_REHEARSAL1.txt")):
        shutil.copy(fx / src, wd / dst)
    block("rehearsal2-list")
    r2b = (wd / "EXCLUDED_REHEARSAL2.json").read_bytes()

    def announced(label, br, mode, sizes, list_bytes, scan_sha=None):
        t0 = beacon_verify.round_time(beacon_chain.QUICKNET, br["round"]) - beacon_verify.DELAY_S
        lf = wd / f"{label}_EXCLUDED.json"
        lf.write_bytes(list_bytes)
        fmt = A.ANNOUNCE_FORMAT_CAMPAIGN if mode == "campaign" else A.ANNOUNCE_FORMAT
        af = wd / f"{label}_ANNOUNCE.txt"
        af.write_text(f"format {fmt}\nmode {mode}\nexcluded_sha256 {sha_b(list_bytes)}\n"
                      + (f"second_scan_sha256 {scan_sha}\n" if scan_sha else "")
                      + "sizes " + " ".join(f"{g}={n}" for g, n in sizes.items()) + "\n")
        d = D.draw(br["randomness"], br["round"], json.loads(list_bytes), dict(sizes))
        df = wd / f"{label}_DRAW.json"
        df.write_bytes(D.canon(dict(d, beacon_round=br, announce=dict(branch=A.ANNOUNCE_BRANCH[mode], commit="0" * 40,
                                                                      push_utc=utc(t0)))))
        return dict(draw=d, draw_file=df, announce=af, list=lf, push_utc=utc(t0))
    br2 = dict(round=20000000, randomness="f39c98df5525968e6622e0c63edb3d1f9c5607cf780db78abdded36e4b3dba95",
               signature="96892582a33552a7b67ba44ef09c3ccd535bbebe760c93ecf45be8958d0c0f06390c6d19d7bf492eb806af7eef6b125c")
    r2 = announced("r2", br2, "rehearsal", A.DRAW_SIZES_REHEARSAL, r2b)
    shutil.copy(r2["draw_file"], wd / "DRAW_REHEARSAL.json")
    r1 = json.loads((fx / "DRAW.json").read_text())
    s12 = [s for d in (r1, r2["draw"]) for v in d["groups"].values() for s in v]
    taken = set(frz["seeds"]) | {x for s in s12 for x in [s] + [10 * s + j for j in range(4)]}
    new3 = [x for x in range(12000, 99999) if x not in taken][:3]
    sc = sorted(set(frz["seeds"]) | set(new3))
    (wd / "EXCLUDED_SECOND_SCAN.json").write_bytes(D.canon(dict(frz, seeds=sc, count=len(sc), seeds_sha256=sha_b(D.canon(sc)))))
    block("list")
    scan_sha = A.sha(wd / "EXCLUDED_SECOND_SCAN.json")
    camp = announced("camp", ROUND_34340412, "campaign", A.DRAW_SIZES, (wd / "EXCLUDED_SECOND.json").read_bytes(), scan_sha=scan_sha)
    kw = dict(rehearsal1_draw=str(wd / "DRAW_REHEARSAL1.json"), rehearsal1_excluded=str(wd / "EXCLUDED_REHEARSAL1.json"),
              rehearsal1_announce=str(wd / "ANNOUNCE_REHEARSAL1.txt"), rehearsal_draw=str(r2["draw_file"]),
              rehearsal_excluded=str(r2["list"]), rehearsal_announce=str(r2["announce"]),
              excluded=str(camp["list"]), second_scan=str(wd / "EXCLUDED_SECOND_SCAN.json"))
    (wd / "a_out").mkdir()
    return dict(wd=wd, F=F, frz=frz, kw=kw, camp=camp, r2=r2, scan_sha=scan_sha, new3=new3)


def case_scan_checks(w):
    """The review of a5ba132b (F1 level 1, F2, F3, O1), the owner's acceptance case 1, offline:
    - F1 level 1 (analysis.check_scan; and once through check_rehearsal_seeds, campaign mode): the stand-in scan (EXCLUDED.json
      plus 3 integers, canonical) is accepted; refused, each with its own message: count not the number of seeds
      (seeds_sha256 right), seeds_sha256 not the seeds', non-canonical bytes (the same content indented), a ref named
      twice (raw JSON), no HEAD entry, HEAD not main's tip, a seed that is a boolean, seeds unsorted, a seed twice,
      another format, another rule, a ref entry of another shape, a same_tree_as_scanned entry whose tip no ref
      scanned, no refs.
    - F2: campaign mode with a draw_info whose announce names no second_scan_sha256: refused; the same with
      pre_announce=True (the function argument [block check-list] uses): accepted; `analysis.py test ... pre_announce=True`
      refused as an unknown argument (no command-line key reaches it).
    - F3: second_scan= a missing file, a folder, not JSON: each refused naming the file; [block check-list] verbatim
      with EXCLUDED_SECOND_SCAN.json missing, and with it not JSON: "REFUSED: EXCLUDED_SECOND_SCAN.json is missing,
      unreadable or not JSON", no Python traceback.
    - O1 (analysis.check_announce_files, and once through check_draw's GitHub path with announce_on_github and
      freeze_time replaced by stand-ins returning the announce commit's files): the commit's EXCLUDED_PUBLISHED.json
      and EXCLUDED_SECOND_SCAN.json accepted when they have the announced sha256 and equal the excluded= and
      second_scan= files; refused, each with its own message, when one is missing from the commit, has another
      sha256 than the announced one, or differs from the file the analysis uses; rehearsal mode reads no scan."""
    import hashlib
    import draw_seeds as D
    A = load_analysis("analysis_scan_checks")
    C = campaign_inputs(w, "scan_checks", A)
    wd, frz = C["wd"], C["frz"]
    checks, out, oks = [], {}, []
    sha_b = lambda b: hashlib.sha256(b).hexdigest()

    def note(label, got, needle, target=ANALYSIS):
        out[label] = got
        oks.append(check(checks, label, got, needle, target, Path(target).exists()))

    def call(f, *a, **k):
        try:
            r = f(*a, **k)
            return "accepted" + ("" if r is None else ": " + json.dumps(r, sort_keys=True, default=str)[:300])
        except SystemExit as e:
            return str(e)
    good = (wd / "EXCLUDED_SECOND_SCAN.json").read_bytes()
    g = json.loads(good)
    canon = D.canon

    def recount(x):
        return dict(x, count=len(x["seeds"]), seeds_sha256=sha_b(canon(x["seeds"])))
    head_main = g["refs"]["HEAD"]["tip"]
    other = next(v["tip"] for n, v in g["refs"].items() if v["tip"] != head_main)
    first_ref = next(n for n in g["refs"] if n.startswith("refs/remotes/origin/"))
    dup = good.replace(b'"refs":{', b'"refs":{' + json.dumps(first_ref).encode() + b':' +
                       canon(g["refs"][first_ref]).strip() + b',', 1)
    variants = [
        ("the stand-in scan, canonical: accepted", good, "accepted"),
        ("count not the number of seeds", canon(dict(g, count=g["count"] + 1)), "count 16337 is not the number of seeds 16336"),
        ("seeds_sha256 not the seeds'", canon(dict(g, seeds_sha256="0" * 64)), "seeds_sha256 is not sha256 of its seeds"),
        ("non-canonical bytes", (json.dumps(g, indent=1, sort_keys=True) + "\n").encode(), "is not in canonical form"),
        ("a ref named twice", dup, f"names a key twice (a ref recorded twice, or a field): ['{first_ref}']"),
        ("no HEAD entry", canon(dict(g, refs={n: v for n, v in g["refs"].items() if n != "HEAD"})),
         "no HEAD entry (draw_seeds.scan always scans HEAD)"),
        ("HEAD not main's tip", canon(dict(g, refs=dict(g["refs"], HEAD=dict(tip=other, same_tree_as_scanned=True)))),
         "HEAD is not main's tip"),
        ("a boolean seed", canon(recount(dict(g, seeds=[True] + g["seeds"]))), "seeds are not a list of integers"),
        ("seeds unsorted", canon(recount(dict(g, seeds=g["seeds"][1:] + g["seeds"][:1]))), "seeds are not sorted and unique"),
        ("a seed twice", canon(recount(dict(g, seeds=sorted(g["seeds"] + g["seeds"][:1])))), "seeds are not sorted and unique"),
        ("another format", canon(dict(g, format="layered-excluded-seeds/2")), "is not draw_seeds.scan's 'layered-excluded-seeds/1'"),
        ("another rule", canon(dict(g, rule=g["rule"] + " ")), "its rule is not draw_seeds.scan's rule"),
        ("a ref entry of another shape", canon(dict(g, refs=dict(g["refs"], **{first_ref: dict(tip="x", numbers=1)}))),
         "refs not of draw_seeds.scan's shape"),
        ("a same_tree entry whose tip no ref scanned",
         canon(dict(g, refs=dict(g["refs"], **{"refs/remotes/origin/zz-extra": dict(tip="f" * 40, same_tree_as_scanned=True)}))),
         "refs marked same_tree_as_scanned whose tip no other ref scanned: ['refs/remotes/origin/zz-extra']"),
        ("no refs", canon(dict(g, refs={})), "no refs (draw_seeds.scan records every ref it scanned)")]
    for label, b, needle in variants:
        note("F1 level 1: " + label, call(A.check_scan, b, "S.json"), needle)
    # once through the analysis's campaign check (count wrong)
    bad = wd / "SCAN_bad_count.json"
    bad.write_bytes(canon(dict(g, count=g["count"] + 1)))
    info = dict(announce=dict(push_utc=C["camp"]["push_utc"], second_scan_sha256=A.sha(bad)))
    note("F1 level 1 through check_rehearsal_seeds (campaign): count not the number of seeds",
         call(A.check_rehearsal_seeds, dict(C["kw"], second_scan=str(bad)), info, wd / "a_out", None, False, "campaign"),
         f"second_scan= {bad}: count 16337 is not the number of seeds 16336", bad)
    # F2
    info0 = dict(announce=dict(push_utc=C["camp"]["push_utc"]))
    note("F2: campaign mode, the announce names no second_scan_sha256: refused",
         call(A.check_rehearsal_seeds, dict(C["kw"]), info0, wd / "a_out", None, False, "campaign"),
         "campaign mode: the campaign announce names no second_scan_sha256")
    note("F2: the same with pre_announce=True (the function argument only): accepted",
         call(A.check_rehearsal_seeds, dict(C["kw"]), info0, wd / "a_out", None, False, "campaign", pre_announce=True),
         "accepted: ")
    (wd / "empty_root").mkdir()
    r = sh(PY, "-B", ANALYSIS, "test", wd / "t_out", wd / "empty_root", "pre_announce=True")
    note("F2: no command-line key reaches pre_announce", f"rc {r.returncode}: {r.stdout}{r.stderr}",
         "refused: unknown argument 'pre_announce=True'")
    oks.append(r.returncode != 0)
    # F3
    info1 = dict(announce=dict(push_utc=C["camp"]["push_utc"], second_scan_sha256=C["scan_sha"]))
    (wd / "a_folder").mkdir()
    (wd / "not_json.json").write_bytes(b"{not json\n")
    for label, f, needle in (("a missing file", wd / "no_such_scan.json", f"second_scan= {wd / 'no_such_scan.json'} is missing or unreadable: No such file or directory"),
                             ("a folder", wd / "a_folder", f"second_scan= {wd / 'a_folder'} is missing or unreadable: Is a directory"),
                             ("not JSON", wd / "not_json.json", f"second_scan= {wd / 'not_json.json'} is not readable JSON")):
        got = call(A.check_rehearsal_seeds, dict(C["kw"], second_scan=str(f)), info1, wd / "a_out", None, False, "campaign")
        note("F3: second_scan= " + label + ": refused naming it", got, needle)
        oks.append("Traceback" not in got)
    for label, content in (("missing", None), ("not JSON", b"{not json\n")):
        fd = wd / f"checklist_{'missing' if content is None else 'notjson'}"
        fd.mkdir()
        shutil.copy(wd / "EXCLUDED_SECOND.json", fd / "EXCLUDED_SECOND.json")
        if content is not None:
            (fd / "EXCLUDED_SECOND_SCAN.json").write_bytes(content)
        r = subprocess.run(["bash", "-c", f"L={HERE}\nF={C['F']}\nPY={PY}\npython() {{ \"$PY\" \"$@\"; }}\n" + freeze_block("check-list")],
                           cwd=fd, capture_output=True, text=True)
        txt = r.stdout + r.stderr
        note(f"F3: [block check-list] verbatim, EXCLUDED_SECOND_SCAN.json {label}: an explicit refusal",
             f"rc {r.returncode}: {txt}", "REFUSED: EXCLUDED_SECOND_SCAN.json is missing, unreadable or not JSON:", fd)
        oks.append(r.returncode != 0 and "Traceback" not in txt)
    # O1
    lb, sb = C["camp"]["list"].read_bytes(), good
    Aan = dict(excluded_sha256=sha_b(lb), second_scan_sha256=sha_b(sb))
    kwf = dict(excluded=str(C["camp"]["list"]), second_scan=str(wd / "EXCLUDED_SECOND_SCAN.json"))
    other_list = wd / "OTHER_LIST.json"
    other_list.write_bytes(lb.replace(b"\n", b" \n"))
    other_scan = wd / "OTHER_SCAN.json"
    other_scan.write_bytes(sb.replace(b"\n", b" \n"))
    for label, at, kwx, mode, needle in (
            ("both files as announced and as used: accepted", {"EXCLUDED_PUBLISHED.json": lb, "EXCLUDED_SECOND_SCAN.json": sb}, kwf, "campaign", "accepted"),
            ("EXCLUDED_PUBLISHED.json missing from the commit", {"EXCLUDED_SECOND_SCAN.json": sb}, kwf, "campaign",
             "the announce commit has no EXCLUDED_PUBLISHED.json"),
            ("EXCLUDED_SECOND_SCAN.json missing from the commit", {"EXCLUDED_PUBLISHED.json": lb}, kwf, "campaign",
             "the announce commit has no EXCLUDED_SECOND_SCAN.json"),
            ("the commit's list with another sha256 than announced", {"EXCLUDED_PUBLISHED.json": lb + b" ", "EXCLUDED_SECOND_SCAN.json": sb}, kwf, "campaign",
             "the announce commit's EXCLUDED_PUBLISHED.json has sha256"),
            ("the commit's scan with another sha256 than announced", {"EXCLUDED_PUBLISHED.json": lb, "EXCLUDED_SECOND_SCAN.json": sb + b" "}, kwf, "campaign",
             "the announce commit's EXCLUDED_SECOND_SCAN.json has sha256"),
            ("excluded= not the commit's list", {"EXCLUDED_PUBLISHED.json": lb, "EXCLUDED_SECOND_SCAN.json": sb},
             dict(kwf, excluded=str(other_list)), "campaign", "the excluded= file is not byte-equal to the announce commit's EXCLUDED_PUBLISHED.json"),
            ("second_scan= not the commit's scan", {"EXCLUDED_PUBLISHED.json": lb, "EXCLUDED_SECOND_SCAN.json": sb},
             dict(kwf, second_scan=str(other_scan)), "campaign", "the second_scan= file is not byte-equal to the announce commit's EXCLUDED_SECOND_SCAN.json"),
            ("rehearsal mode reads no scan", {"EXCLUDED_PUBLISHED.json": lb}, dict(excluded=kwf["excluded"]), "rehearsal", "accepted")):
        note("O1: " + label, call(A.check_announce_files, at, Aan, kwx, mode), needle)
    # O1 through check_draw's GitHub path: announce_on_github and freeze_time replaced by stand-ins
    camp = C["camp"]
    ab = camp["announce"].read_bytes()
    saved = A.announce_on_github, A.freeze_time
    try:
        for label, at, needle in (
                ("check_draw (campaign, GitHub path): the commit's files as announced: accepted",
                 {"EXCLUDED_PUBLISHED.json": lb, "EXCLUDED_SECOND_SCAN.json": sb}, "accepted"),
                ("check_draw (campaign, GitHub path): the commit's scan differs from the announce: refused",
                 {"EXCLUDED_PUBLISHED.json": lb, "EXCLUDED_SECOND_SCAN.json": sb + b" "},
                 "the announce commit's EXCLUDED_SECOND_SCAN.json has sha256")):
            A.announce_on_github = lambda branch, outdir, files=None, at=at: ("0" * 40, ab, camp["push_utc"], at)
            A.freeze_time = lambda tree_commit, outdir: "2026-01-01T00:00:00Z"
            got = call(lambda: (A.check_draw(dict(draw=str(camp["draw_file"]), excluded=kwf["excluded"],
                                                  second_scan=kwf["second_scan"]), "campaign", wd / "a_out", "x")[1]["announce"]))
            note(label, got, needle)
    finally:
        A.announce_on_github, A.freeze_time = saved
    return all(oks), dict(checks=checks, results=out)


def case_verify_scan(w):
    """F1 level 2, the owner's acceptance case 2, on a LOCAL TWIN of the repository (a bare repository with five
    branches, two with seed lines, one at the same tip as another; HEAD = main), never GitHub's:
    - the first machine's scan: [block second-scan] verbatim, its GitHub URL replaced by the twin (the one twin);
    - a scan enriched with 3 arbitrary integers, count and seeds_sha256 recomputed (canonical; analysis.check_scan
      accepts it: level 1 cannot see it), given to the verifier as SCAN_TO_VERIFY.json; the verifier's own [block
      second-scan] in its own folder, then [block verify-scan] verbatim (its GitHub URLs replaced by the twin): it
      FAILS ("THE SCAN IS NOT REPRODUCED", the reproduced sha256 named), creates no record (no commit, no verify branch
      on the twin), before any announce; then [block announce] (campaign) with VS (the reproduction's sha256) and HS
      (the enriched scan's): refused "VS ... is not HS" before any commit (no announce_campaign repository);
    - the honest scan: [block verify-scan] passes, prints VS = HS, and publishes its record (one commit, the three
      files) on the twin's evidence/combined-scan-verify;
    - analysis.verify_scan on the inventory: a branch on the remote and not in the scan, in the scan and not on the
      remote, at another tip, and the scan's HEAD not main's tip: each named."""
    import hashlib
    import draw_seeds as D
    A = load_analysis("analysis_verify_scan")
    wd = w.wd / "verify_scan"
    shutil.rmtree(wd, ignore_errors=True)
    wd.mkdir()
    F = subprocess.run(["git", "-C", str(HERE), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    checks, out, oks = [], {}, []
    sha_b = lambda b: hashlib.sha256(b).hexdigest()

    def note(label, got, needle, target=ANALYSIS):
        out[label] = got
        oks.append(check(checks, label, got, needle, target, Path(target).exists()))
    # the twin: main (a seed line), feature-a (a range), feature-b (no seed), copy-of-a (feature-a's tip), docs
    twin = wd / "twin.git"
    src = wd / "twin_src"
    G = lambda *a, cwd=src: subprocess.run(["git", *a], cwd=cwd, capture_output=True, text=True, check=True).stdout.strip()
    subprocess.run(["git", "init", "-q", "--bare", str(twin)], check=True)
    src.mkdir()
    G("init", "-q", "-b", "main")
    G("config", "user.name", "twin owner")
    G("config", "user.email", "twin-owner@invalid")
    (src / "notes.txt").write_text("the seed is 12345 for this run\n")
    G("add", ".")
    G("commit", "-q", "-m", "main")
    G("push", "-q", str(twin), "main")
    for b, text in (("feature-a", "noise_seed 23456-23460\n"), ("feature-b", "nothing here 99999\n"), ("docs", "rehearsal 34567\n")):
        G("checkout", "-q", "-b", b, "main")
        (src / f"{b}.txt").write_text(text)
        G("add", ".")
        G("commit", "-q", "-m", b)
        G("push", "-q", str(twin), b)
    G("push", "-q", str(twin), "feature-a:refs/heads/copy-of-a")
    URL = "file://" + str(twin)
    GH = "https://github.com/HevisNico/kernel-R"
    head = f"L={HERE}\nF={F}\nPY={PY}\npython() {{ \"$PY\" \"$@\"; }}\n"

    def run(name, folder, pre=""):
        b = freeze_block(name)
        n = b.count(GH)
        b = b.replace(GH, URL)
        r = subprocess.run(["bash", "-c", head + pre + b], cwd=folder, capture_output=True, text=True)
        return r.returncode, (r.stdout + r.stderr).strip()[-2500:], n
    first = wd / "first"
    first.mkdir()
    rc, txt, n = run("second-scan", first)
    out["second-scan: GitHub URLs replaced by the twin"] = n
    note("the first machine's [block second-scan] on the twin", f"rc {rc}: {txt}", "excluded integers from 6 refs", first)
    honest = (first / "EXCLUDED_SECOND_SCAN.json").read_bytes()
    hj = json.loads(honest)
    extra = [s for s in (41001, 41002, 41003) if s not in hj["seeds"]]
    es = sorted(hj["seeds"] + extra)
    enriched = D.canon(dict(hj, seeds=es, count=len(es), seeds_sha256=sha_b(D.canon(es))))
    note("the enriched scan passes level 1 (analysis.check_scan)",
         "accepted" if A.check_scan(enriched, "ENRICHED.json") else "refused", "accepted")
    for label, sv, folder in (("enriched", enriched, "verifier_enriched"), ("honest", honest, "verifier_honest")):
        fd = wd / folder
        fd.mkdir()
        (fd / "SCAN_TO_VERIFY.json").write_bytes(sv)
        rc, txt, n = run("second-scan", fd)
        assert rc == 0, txt
        rc, txt, n = run("verify-scan", fd)
        out[f"verify-scan: GitHub URLs replaced by the twin ({label})"] = n
        refs = subprocess.run(["git", "--git-dir", str(twin), "for-each-ref", "--format=%(refname)",
                               "refs/heads/evidence/combined-scan-verify"], capture_output=True, text=True).stdout.split()
        rec = fd / "record"
        committed = rec.exists() and subprocess.run(["git", "-C", str(rec), "rev-parse", "-q", "--verify", "HEAD"],
                                                    capture_output=True).returncode == 0
        if label == "enriched":
            note("[block verify-scan]: the enriched scan FAILS, no record", f"rc {rc}, record commit {committed}, twin refs {refs}: {txt}",
                 f"PROBLEM: the reproduced scan has sha256 {sha_b(honest)}, not the scan's {sha_b(enriched)}", fd)
            oks.append(rc != 0 and "THE SCAN IS NOT REPRODUCED" in txt and not committed and not refs)
            # [block announce] (campaign): VS (the reproduction) is not HS (the enriched scan)
            (fd / "EXCLUDED_SECOND.json").write_bytes(enriched)
            pre = (f"M=campaign B=evidence/combined-draw-twin R=x X=EXCLUDED_SECOND.json SIZES='NOT1=60 ANDOR3=32 XOR3=37' "
                   f"H={sha_b(enriched)} S=SCAN_TO_VERIFY.json HS={sha_b(enriched)} VS={sha_b(honest)}\n")
            rc2, txt2, _ = run("announce", fd, pre)
            made = (fd / "announce_campaign").exists()
            note("[block announce]: VS is not HS, refused before any commit", f"rc {rc2}, announce_campaign exists {made}: {txt2}",
                 f"REFUSED: VS ({sha_b(honest)}), the second machine's reproduction of the scan (ORDER 3 (3b)), is not HS "
                 f"({sha_b(enriched)}): no commit, no push", fd)
            oks.append(rc2 != 0 and not made)
        else:
            files = subprocess.run(["git", "--git-dir", str(twin), "ls-tree", "--name-only", refs[0]], capture_output=True,
                                   text=True).stdout.split() if refs else []
            note("[block verify-scan]: the honest scan passes, VS = HS, its record published once",
                 f"rc {rc}, twin refs {refs}, files {files}: {txt}", f"the scan is reproduced scan_sha256 {sha_b(honest)} VS {sha_b(honest)}", fd)
            oks.append(rc == 0 and files == ["SCAN_LSREMOTE.txt", "VERIFY.txt", "VERIFY_LSREMOTE.txt"])
    # the inventory, on analysis.verify_scan
    ls = (wd / "verifier_honest" / "VERIFY_LSREMOTE.txt").read_text()
    lines = [ln for ln in ls.splitlines() if ln.strip() and "combined-scan-verify" not in ln]
    base = "\n".join(lines) + "\n"
    tip_b = next(ln.split()[0] for ln in lines if ln.endswith("refs/heads/feature-b"))
    tip_main = next(ln.split()[0] for ln in lines if ln.endswith("refs/heads/main"))
    for label, lsr, needle in (
            ("the inventory as scanned: verified", base, "[]"),
            ("a branch on the remote, not in the scan", base + f"{tip_b}\trefs/heads/new-branch\n",
             "branch new-branch is on the remote"),
            ("a branch in the scan, not on the remote", "\n".join(ln for ln in lines if not ln.endswith("refs/heads/docs")) + "\n",
             "branch docs is in the scan"),
            ("a branch at another tip", base.replace(f"{tip_b}\trefs/heads/feature-b", f"{tip_main}\trefs/heads/feature-b"),
             f"branch feature-b is at {tip_main[:12]} on the remote, at {tip_b[:12]} in the scan"),
            ("HEAD not main's tip", base.replace(f"{tip_main}\trefs/heads/main", f"{tip_b}\trefs/heads/main"),
             "the scan's HEAD")):
        note("analysis.verify_scan: " + label, json.dumps(A.verify_scan(honest, honest, lsr)), needle)
    return all(oks), dict(checks=checks, results=out, enriched_with=extra)
