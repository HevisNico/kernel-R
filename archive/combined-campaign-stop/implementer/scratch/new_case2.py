ROUND_34340412 = dict(round=34340412, randomness="4522e03cf897e1eae78e736eeaae49f465b1b64e180affd88d9857dfb233ba1d",
                      signature="895cb3f5107c4d6d2ba64e8f084cbf70550952c28d81655f0cf554bcee1f7acbb33e2b93aa27b08a188110b3794003e1")


def case_exact_union_owner(w):
    """The owner's three validation results of 2026-11-28, the announce formats /1 and /2, and rehearsal 2's list in
    campaign mode. Offline except where named (the two GitHub reads: rehearsal 1's announce branch, fetched by name,
    and main for the owner identity inside [block announce]; nothing is pushed to GitHub).
    Inputs as in exact_union: rehearsal 1 as published (tests/fixtures/rehearsal1), rehearsal 2's list from [block
    rehearsal2-list] verbatim, a stand-in rehearsal 2 on round 20000000 over it, a stand-in second scan (the freeze's
    EXCLUDED.json plus 3 integers), the campaign's list from [block list] verbatim. The campaign stand-in draw is the
    published quicknet round 34340412 (2026-11-28T00:10:00Z; announced at 00:00:00Z, after both rehearsals), 60/32/37.
    - V1: one seed present ONLY in the second scan removed from the campaign's list, count and seeds_sha256 recomputed,
      and RE-ANNOUNCED (the /2 announce names the new list; the draw is drawn on it): analysis.check_draw accepts it
      (the old checks: announced sha256, superset of the freeze's list, cap, the draw recomputed), the old inclusion
      check passes (no "lacks rehearsal" refusal), and check_rehearsal_seeds refuses it by the exact union, naming the
      seed. The exact list re-announced the same way is accepted (control).
    - V2: [block announce] verbatim, campaign, its single push twinned to a local bare repository and its ls-remote to
      that same repository: a copy of the scan with ONE byte changed (HS kept from the original) is refused with
      "REFUSED: EXCLUDED_SECOND_SCAN.json has sha256", before any commit (no HEAD in announce_campaign) and the twin
      holds no ref. The original scan (control) gives one commit with the three files and a /2 announce of 5 lines.
    - V3: rehearsal 1's REAL announce, fetched by name from evidence/combined-rehearsal-draw (commit 9c3ec1e1), parses:
      format /1, mode rehearsal, its excluded_sha256 the one analysis.REHEARSAL1 pins.
    - The formats: /1 rehearsal and test accepted; /1 with second_scan_sha256 refused; /1 campaign refused; /2
      campaign with second_scan_sha256 accepted; /2 campaign without it refused; /2 rehearsal refused; another format
      refused.
    - (b): campaign mode with rehearsal_excluded= = rehearsal 2's exact list plus one extra seed, count and
      seeds_sha256 recomputed and re-announced (rehearsal 2 drawn on it, its announce naming it; the campaign's list
      built from that draw): refused by the exact union of rehearsal 2's list, naming the seed."""
    import datetime
    import hashlib
    import importlib.util
    spec = importlib.util.spec_from_file_location("analysis_exact_owner", ANALYSIS)
    A = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(Path(ANALYSIS).parent))
    spec.loader.exec_module(A)
    import beacon_chain
    import beacon_verify
    import draw_seeds as D
    fx = HERE / "tests" / "fixtures" / "rehearsal1"
    wd = w.wd / "exact_union_owner"
    shutil.rmtree(wd, ignore_errors=True)
    wd.mkdir()
    frz = json.loads((HERE / "EXCLUDED.json").read_text())
    F = subprocess.run(["git", "-C", str(HERE), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    checks, out, oks = [], {}, []
    sha_b = lambda b: hashlib.sha256(b).hexdigest()
    utc = lambda t: datetime.datetime.fromtimestamp(t, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    def note(label, got, needle, target):
        out[label] = got
        oks.append(check(checks, label, got, needle, target, Path(target).exists()))

    def run_block(name, folder, twins=()):
        b = freeze_block(name)
        for old, new in twins:
            assert b.count(old) == 1, f"twin of {name}: {b.count(old)} occurrences of {old[:60]!r}"
            b = b.replace(old, new)
        head = f"L={HERE}\nF={F}\nPY={PY}\npython() {{ \"$PY\" \"$@\"; }}\n"
        r = subprocess.run(["bash", "-c", head + b], cwd=folder, capture_output=True, text=True)
        return r.returncode, (r.stdout + r.stderr).strip()[-2000:]

    def call(f, *a):
        try:
            return "accepted: " + json.dumps(f(*a), sort_keys=True, default=str)[:600]
        except SystemExit as e:
            return str(e)

    # ---- the inputs, as in exact_union
    for src, dst in (("DRAW.json", "DRAW_REHEARSAL1.json"), ("EXCLUDED_PUBLISHED.json", "EXCLUDED_REHEARSAL1.json"),
                     ("DRAW_ANNOUNCE.txt", "ANNOUNCE_REHEARSAL1.txt")):
        shutil.copy(fx / src, wd / dst)
    rc, txt = run_block("rehearsal2-list", wd)
    assert rc == 0, txt
    r1 = json.loads((fx / "DRAW.json").read_text())
    rb1 = (fx / "DRAW.json").read_bytes()
    r2b = (wd / "EXCLUDED_REHEARSAL2.json").read_bytes()
    br2 = dict(round=20000000, randomness="f39c98df5525968e6622e0c63edb3d1f9c5607cf780db78abdded36e4b3dba95",
               signature="96892582a33552a7b67ba44ef09c3ccd535bbebe760c93ecf45be8958d0c0f06390c6d19d7bf492eb806af7eef6b125c")

    def announced(label, br, mode, sizes, list_bytes, scan_sha=None, branch=None):
        """A stand-in draw on the published round br over the list, announced 600 s before the round: (draw,
        DRAW.json path, DRAW_ANNOUNCE.txt path, list path)."""
        t0 = beacon_verify.round_time(beacon_chain.QUICKNET, br["round"]) - beacon_verify.DELAY_S
        lf = wd / f"{label}_EXCLUDED.json"
        lf.write_bytes(list_bytes)
        words = " ".join(f"{g}={n}" for g, n in sizes.items())
        fmt = A.ANNOUNCE_FORMAT_CAMPAIGN if mode == "campaign" else A.ANNOUNCE_FORMAT
        af = wd / f"{label}_ANNOUNCE.txt"
        af.write_text(f"format {fmt}\nmode {mode}\nexcluded_sha256 {sha_b(list_bytes)}\n"
                      + (f"second_scan_sha256 {scan_sha}\n" if scan_sha else "") + f"sizes {words}\n")
        d = D.draw(br["randomness"], br["round"], json.loads(list_bytes), dict(sizes))
        df = wd / f"{label}_DRAW.json"
        df.write_bytes(D.canon(dict(d, beacon_round=br, announce=dict(branch=branch or A.ANNOUNCE_BRANCH[mode],
                                                                      commit="0" * 40, push_utc=utc(t0)))))
        return d, df, af, lf
    d2, f2, a2, l2 = announced("r2", br2, "rehearsal", A.DRAW_SIZES_REHEARSAL, r2b)
    for src, dst in ((f2, "DRAW_REHEARSAL.json"), (a2, "ANNOUNCE_REHEARSAL2.txt")):
        shutil.copy(src, wd / dst)
    s1 = sorted(s for v in r1["groups"].values() for s in v)
    s2 = sorted(s for v in d2["groups"].values() for s in v)
    taken = set(frz["seeds"]) | {x for s in s1 + s2 for x in [s] + [10 * s + j for j in range(4)]}
    new3 = [x for x in range(12000, 99999) if x not in taken][:3]
    sc = sorted(set(frz["seeds"]) | set(new3))
    scan = dict(frz, seeds=sc, count=len(sc), seeds_sha256=sha_b(D.canon(sc)))
    (wd / "EXCLUDED_SECOND_SCAN.json").write_bytes(D.canon(scan))
    scan_sha = A.sha(wd / "EXCLUDED_SECOND_SCAN.json")
    rc, txt = run_block("list", wd)
    assert rc == 0, txt
    secb = (wd / "EXCLUDED_SECOND.json").read_bytes()
    (wd / "a_out").mkdir()
    r1kw = dict(rehearsal1_draw=str(wd / "DRAW_REHEARSAL1.json"), rehearsal1_excluded=str(wd / "EXCLUDED_REHEARSAL1.json"),
                rehearsal1_announce=str(wd / "ANNOUNCE_REHEARSAL1.txt"))

    # ---- V1: a seed present ONLY in the second scan removed, re-announced
    gone = new3[0]
    x = json.loads(secb)
    ms = [s for s in x["seeds"] if s != gone]
    mut = D.canon(dict(x, seeds=ms, count=len(ms), seeds_sha256=sha_b(D.canon(ms))))
    for label, lb in (("V1 control: the exact list re-announced", secb), ("V1: a scan-only seed removed, re-announced", mut)):
        tag = "v1c" if lb == secb else "v1m"
        dc, fc, ac, lc = announced(tag, ROUND_34340412, "campaign", A.DRAW_SIZES, lb, scan_sha=scan_sha)
        kw = dict(draw=str(fc), excluded=str(lc), announce=str(ac))
        try:
            _, info, _ = A.check_draw(kw, "campaign", wd / "a_out", None, offline=True)
            drawn = "check_draw accepted"
        except SystemExit as e:
            info, drawn = None, "check_draw REFUSED: " + str(e)
        note(f"{label}: the old checks (check_draw, offline) accept it", drawn, "check_draw accepted", lc)
        if info is None:
            oks.append(False)
            continue
        got = call(A.check_rehearsal_seeds, dict(r1kw, rehearsal_draw=str(f2), rehearsal_excluded=str(l2),
                                                 rehearsal_announce=str(a2), excluded=str(lc),
                                                 second_scan=str(wd / "EXCLUDED_SECOND_SCAN.json")),
                   info, wd / "a_out", None, False, "campaign")
        if lb == secb:
            note(label + ": accepted", got, "accepted: ", lc)
        else:
            note(label + ": refused by the exact union", got,
                 f"the campaign's excluded= list is missing 1 seeds of the exact union of second_scan= and both "
                 f"rehearsals' verified seeds and noise seeds ([block list]): [{gone}]", lc)
            oks.append("lacks rehearsal" not in got)          # not by the old inclusion check
    # ---- V2: [block announce], a scan copy with one byte changed
    bare = wd / "twin.git"
    subprocess.run(["git", "init", "-q", "--bare", str(bare)], check=True)
    GH = "https://github.com/HevisNico/kernel-R"
    twins = [(f"git push -q {GH} HEAD:refs/heads/$B", f"git push -q {bare} HEAD:refs/heads/$B"),
             (f'test -z "$(git ls-remote {GH} refs/heads/$B)"', f'test -z "$(git ls-remote {bare} refs/heads/$B)"')]
    out["announce_twins"] = twins
    H = sha_b(secb)
    orig = (wd / "EXCLUDED_SECOND_SCAN.json").read_bytes()
    k = len(orig) // 2
    while not chr(orig[k]).isdigit():
        k += 1
    one = orig[:k] + (b"7" if orig[k:k + 1] != b"7" else b"8") + orig[k + 1:]
    assert len(one) == len(orig) and sum(a != b for a, b in zip(one, orig)) == 1
    for label, sb, folder in (("V2: a scan copy with one byte changed", one, "v2_mut"), ("V2 control: the scan", orig, "v2_ok")):
        fd = wd / folder
        fd.mkdir()
        shutil.copy(wd / "EXCLUDED_SECOND.json", fd / "EXCLUDED_SECOND.json")
        (fd / "EXCLUDED_SECOND_SCAN.json").write_bytes(sb)
        pre = (f"M=campaign B=evidence/combined-draw-test-{folder} R=x X=EXCLUDED_SECOND.json "
               f"SIZES='NOT1=60 ANDOR3=32 XOR3=37' H={H} S=EXCLUDED_SECOND_SCAN.json HS={scan_sha}\n")
        rc, txt = run_block("announce", fd, twins=[("( set -e\n", pre + "( set -e\n")] + twins)
        repo = fd / "announce_campaign"
        commit = subprocess.run(["git", "-C", str(repo), "rev-parse", "-q", "--verify", "HEAD"], capture_output=True,
                                text=True).returncode == 0 if repo.exists() else False
        refs = subprocess.run(["git", "--git-dir", str(bare), "for-each-ref", "--format=%(refname)", f"refs/heads/evidence/combined-draw-test-{folder}"],
                              capture_output=True, text=True).stdout.split()
        if sb == one:
            note(label + ": refused before any commit", f"rc {rc}, commit {commit}, twin refs {refs}: {txt}",
                 f"REFUSED: EXCLUDED_SECOND_SCAN.json has sha256 {sha_b(one)}, not the validated {scan_sha}: no commit, no push",
                 fd / "EXCLUDED_SECOND_SCAN.json")
            oks.append(rc != 0 and not commit and not refs)
        else:
            files = subprocess.run(["git", "--git-dir", str(bare), "ls-tree", "--name-only", refs[0]], capture_output=True,
                                   text=True).stdout.split() if refs else []
            ann = subprocess.run(["git", "--git-dir", str(bare), "show", f"{refs[0]}:DRAW_ANNOUNCE.txt"], capture_output=True,
                                 text=True).stdout if refs else ""
            note(label + ": one commit, three files, a /2 announce", f"rc {rc}, files {files}, announce {ann!r}: {txt}",
                 "announce pushed: evidence/combined-draw-test-v2_ok", fd / "EXCLUDED_SECOND_SCAN.json")
            oks.append(rc == 0 and files == ["DRAW_ANNOUNCE.txt", "EXCLUDED_PUBLISHED.json", "EXCLUDED_SECOND_SCAN.json"]
                       and ann == f"format layered-draw-announce/2\nmode campaign\nexcluded_sha256 {H}\nsecond_scan_sha256 "
                                  f"{scan_sha}\nsizes NOT1=60 ANDOR3=32 XOR3=37\n")
    # ---- V3: rehearsal 1's real announce, fetched by name
    rr = wd / "r1_announce_fetch"
    subprocess.run(["git", "init", "-q", str(rr)], check=True)
    fr = subprocess.run(["git", "-C", str(rr), "fetch", "-q", GH, "refs/heads/evidence/combined-rehearsal-draw"],
                        capture_output=True, text=True)
    head = subprocess.run(["git", "-C", str(rr), "rev-parse", "FETCH_HEAD"], capture_output=True, text=True).stdout.strip()
    real = subprocess.run(["git", "-C", str(rr), "show", "FETCH_HEAD:DRAW_ANNOUNCE.txt"], capture_output=True).stdout
    got = call(A.parse_announce, real)
    note("V3: rehearsal 1's real announce (fetched by name) parses", f"fetch rc {fr.returncode}, {head}: {got}",
         f'"excluded_sha256": "{A.REHEARSAL1["excluded_sha256"]}", "format": "layered-draw-announce/1", "mode": "rehearsal"', rr)
    oks.append(head.startswith("9c3ec1e1"))
    out["rehearsal1_announce_fixture_identical"] = real == (fx / "DRAW_ANNOUNCE.txt").read_bytes()
    # ---- the formats
    four = "format {f}\nmode {m}\nexcluded_sha256 " + "a" * 64 + "\nsizes NOT1=6 ANDOR3=6 XOR3=6\n"
    five = four.replace("\nsizes", "\nsecond_scan_sha256 " + "b" * 64 + "\nsizes")
    for label, text, needle in (
            ("/1 rehearsal accepted", four.format(f="layered-draw-announce/1", m="rehearsal"), '"format": "layered-draw-announce/1", "mode": "rehearsal"'),
            ("/1 test accepted", four.format(f="layered-draw-announce/1", m="test"), '"mode": "test"'),
            ("/1 with second_scan_sha256 refused", five.format(f="layered-draw-announce/1", m="rehearsal"),
             "DRAW_ANNOUNCE.txt in layered-draw-announce/1 is not exactly the lines ('format', 'mode', 'excluded_sha256', 'sizes') (second_scan_sha256 only in layered-draw-announce/2)"),
            ("/1 campaign refused", four.format(f="layered-draw-announce/1", m="campaign"),
             "a campaign announce is layered-draw-announce/2, not layered-draw-announce/1"),
            ("/2 campaign with second_scan_sha256 accepted", five.format(f="layered-draw-announce/2", m="campaign"),
             '"format": "layered-draw-announce/2", "mode": "campaign", "second_scan_sha256": "' + "b" * 64),
            ("/2 campaign without second_scan_sha256 refused", four.format(f="layered-draw-announce/2", m="campaign"),
             "DRAW_ANNOUNCE.txt in layered-draw-announce/2 is not exactly the lines ('format', 'mode', 'excluded_sha256', 'sizes', 'second_scan_sha256')"),
            ("/2 rehearsal refused", five.format(f="layered-draw-announce/2", m="rehearsal"),
             "layered-draw-announce/2 is the campaign announce only, not mode 'rehearsal'"),
            ("another format refused", four.format(f="layered-draw-announce/3", m="rehearsal"),
             "format 'layered-draw-announce/3' is neither")):
        note("format: " + label, call(A.parse_announce, text.encode()), needle, ANALYSIS)
    # ---- (b): rehearsal 2's list in campaign mode, one extra seed, re-announced
    y = json.loads(r2b)
    extra = next(s for s in range(10000, 99999) if s not in set(y["seeds"]))
    ys = sorted(y["seeds"] + [extra])
    r2mut = D.canon(dict(y, seeds=ys, count=len(ys), seeds_sha256=sha_b(D.canon(ys))))
    d2m, f2m, a2m, l2m = announced("r2m", br2, "rehearsal", A.DRAW_SIZES_REHEARSAL, r2mut)
    cl = A.campaign_list(scan, d2m, f2m.read_bytes(), r1, rb1)
    dc, fc, ac, lc = announced("v4c", ROUND_34340412, "campaign", A.DRAW_SIZES, cl, scan_sha=scan_sha)
    _, info, _ = A.check_draw(dict(draw=str(fc), excluded=str(lc), announce=str(ac)), "campaign", wd / "a_out", None, offline=True)
    got = call(A.check_rehearsal_seeds, dict(r1kw, rehearsal_draw=str(f2m), rehearsal_excluded=str(l2m),
                                             rehearsal_announce=str(a2m), excluded=str(lc),
                                             second_scan=str(wd / "EXCLUDED_SECOND_SCAN.json")),
               info, wd / "a_out", None, False, "campaign")
    note("(b): rehearsal 2's list with one extra seed, re-announced, refused in campaign mode", got,
         f"rehearsal 2's list (rehearsal_excluded=) adds 1 seeds that are not in the exact union of the freeze's "
         f"EXCLUDED.json and rehearsal 1's verified seeds and noise seeds ([block rehearsal2-list]): [{extra}]", l2m)
    got = call(A.check_rehearsal_seeds, dict(r1kw, rehearsal_draw=str(f2), rehearsal_excluded=str(l2),
                                             rehearsal_announce=str(a2), excluded=str(wd / "v1c_EXCLUDED.json"),
                                             second_scan=str(wd / "EXCLUDED_SECOND_SCAN.json")),
               dict(announce=dict(push_utc=utc(beacon_verify.round_time(beacon_chain.QUICKNET, ROUND_34340412["round"]) - 600),
                                  second_scan_sha256=scan_sha)), wd / "a_out", None, False, "campaign")
    note("(b) control: rehearsal 2's exact list accepted in campaign mode", got, '"rehearsal2_list": {"file": "r2_EXCLUDED.json"',
         l2)
    return all(oks), dict(checks=checks, results=out, scan_only_seed_removed=gone, rehearsal2_extra_seed=extra)
