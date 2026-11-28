def freeze_block(name):
    """FREEZE.txt's [block NAME], extracted by proof2.py's own rule (the lines between the markers, dedented)."""
    import re
    import textwrap
    text = (HERE / "FREEZE.txt").read_text().split("\n")
    found, k = [], 0
    while k < len(text):
        m = re.fullmatch(r"\s*\[block ([a-z0-9-]+)\]\s*", text[k])
        if m:
            j = next(i for i in range(k + 1, len(text)) if text[i].strip() == "[end]")
            if m.group(1) == name:
                found.append(textwrap.dedent("\n".join(text[k + 1:j])) + "\n")
            k = j
        k += 1
    assert len(found) == 1, f"[block {name}] found {len(found)} times"
    return found[0]


def case_exact_union(w):
    """The owner's defect of 2026-11-28: the checks of rehearsal 2's list and of the campaign's list only required the
    seeds to be IN the list, so a list with extra exclusions (and a recomputed count and seeds_sha256) passed. Both
    lists must now be the exact union, byte for byte. Offline, on rehearsal 1's published files (tests/fixtures/
    rehearsal1), a stand-in rehearsal 2 drawn on the published quicknet round 20000000 over rehearsal 2's list, and a
    stand-in second scan (the freeze's EXCLUDED.json plus three integers).
    - FREEZE.txt's blocks, extracted verbatim and run in bash: [block rehearsal2-list] and [block list] build the
      lists; [block check-rehearsal2-list] and [block check-list] must say "the list is right" on them and refuse
      (exit 1, never "the list is right") a list with one extra seed (count and seeds_sha256 recomputed: the
      self-consistency the old check required holds), one seed removed, and one field changed. The check blocks run
      with offline twins only (each listed in TWINS below and applied exactly once): the GitHub reads of the
      announces replaced by their offline modes on the announce files. Each mutation is also run with the block's
      call of analysis.check_rehearsal_seeds disabled (a second, listed twin), so that the block's own rebuild is
      seen to refuse it alone ("THE LIST IS WRONG").
    - analysis.check_rehearsal_seeds (offline) in rehearsal mode and in campaign mode: the exact list accepted; one
      extra seed, one seed removed, one field changed, each refused with its own message; in campaign mode
      second_scan= missing, second_scan= not a superset of the freeze's list, and second_scan= not the one the
      announce names, each refused with its own message.
    - analysis.parse_announce: second_scan_sha256 required with mode campaign, refused with any other mode.
    - analysis.py test mode refuses second_scan= (campaign mode only)."""
    import datetime
    import hashlib
    import importlib.util
    spec = importlib.util.spec_from_file_location("analysis_exact", ANALYSIS)
    A = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(Path(ANALYSIS).parent))
    spec.loader.exec_module(A)
    import beacon_chain
    import beacon_verify
    import draw_seeds as D
    fx = HERE / "tests" / "fixtures" / "rehearsal1"
    wd = w.wd / "exact_union"
    shutil.rmtree(wd, ignore_errors=True)
    wd.mkdir()
    frz = json.loads((HERE / "EXCLUDED.json").read_text())
    F = subprocess.run(["git", "-C", str(HERE), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    checks, out, oks = [], {}, []

    def note(label, got, needle, target):
        out[label] = got
        oks.append(check(checks, label, got, needle, target, Path(target).exists()))

    TWINS = {
        "check-rehearsal2-list": [
            ("A.check_draw(dict(draw='DRAW_REHEARSAL1.json', excluded='EXCLUDED_REHEARSAL1.json'), 'rehearsal', tempfile.mkdtemp(), '$F', past=A.REHEARSAL1)",
             "A.check_draw(dict(draw='DRAW_REHEARSAL1.json', excluded='EXCLUDED_REHEARSAL1.json', announce='ANNOUNCE_REHEARSAL1.txt'), "
             "'rehearsal', tempfile.mkdtemp(), '$F', offline=True, past=A.REHEARSAL1)"),
            ("A.check_rehearsal_seeds(dict(rehearsal1_draw='DRAW_REHEARSAL1.json', rehearsal1_excluded='EXCLUDED_REHEARSAL1.json',",
             "A.check_rehearsal_seeds(dict(rehearsal1_draw='DRAW_REHEARSAL1.json', rehearsal1_excluded='EXCLUDED_REHEARSAL1.json', "
             "rehearsal1_announce='ANNOUNCE_REHEARSAL1.txt',"),
            ("dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', True, 'rehearsal')",
             "dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', False, 'rehearsal')")],
        "check-list": [
            ("A.check_draw(dict(draw='DRAW_REHEARSAL.json', excluded='EXCLUDED_REHEARSAL2.json'), 'rehearsal', tempfile.mkdtemp(), '$F')",
             "A.check_draw(dict(draw='DRAW_REHEARSAL.json', excluded='EXCLUDED_REHEARSAL2.json', announce='ANNOUNCE_REHEARSAL2.txt'), "
             "'rehearsal', tempfile.mkdtemp(), '$F', offline=True)"),
            ("A.check_draw(dict(draw='DRAW_REHEARSAL1.json', excluded='EXCLUDED_REHEARSAL1.json'), 'rehearsal', tempfile.mkdtemp(), '$F', past=A.REHEARSAL1)",
             "A.check_draw(dict(draw='DRAW_REHEARSAL1.json', excluded='EXCLUDED_REHEARSAL1.json', announce='ANNOUNCE_REHEARSAL1.txt'), "
             "'rehearsal', tempfile.mkdtemp(), '$F', offline=True, past=A.REHEARSAL1)"),
            ("A.check_rehearsal_seeds(dict(rehearsal_draw='DRAW_REHEARSAL.json', rehearsal_excluded='EXCLUDED_REHEARSAL2.json',",
             "A.check_rehearsal_seeds(dict(rehearsal_draw='DRAW_REHEARSAL.json', rehearsal_excluded='EXCLUDED_REHEARSAL2.json', "
             "rehearsal_announce='ANNOUNCE_REHEARSAL2.txt', rehearsal1_announce='ANNOUNCE_REHEARSAL1.txt',"),
            ("dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', True, 'campaign')",
             "dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', False, 'campaign')")]}
    NO_ANALYSIS = ("A.check_rehearsal_seeds(", "(lambda *a: None)(")    # the second twin: the block's own rebuild alone
    out["twins"] = dict(TWINS, no_analysis=NO_ANALYSIS)

    def block(name, folder, alone=False):
        b = freeze_block(name)
        for old, new in TWINS.get(name, []) + ([NO_ANALYSIS] if alone else []):
            assert b.count(old) == 1, f"twin of {name}: {b.count(old)} occurrences of {old[:60]!r}"
            b = b.replace(old, new)
        head = f"L={HERE}\nF={F}\nPY={PY}\npython() {{ \"$PY\" \"$@\"; }}\n"
        r = subprocess.run(["bash", "-c", head + b], cwd=folder, capture_output=True, text=True)
        return r.returncode, (r.stdout + r.stderr).strip()[-2000:]

    # the inputs: rehearsal 1 as published, rehearsal 2's list from [block rehearsal2-list] verbatim
    for src, dst in (("DRAW.json", "DRAW_REHEARSAL1.json"), ("EXCLUDED_PUBLISHED.json", "EXCLUDED_REHEARSAL1.json"),
                     ("DRAW_ANNOUNCE.txt", "ANNOUNCE_REHEARSAL1.txt")):
        shutil.copy(fx / src, wd / dst)
    rc, txt = block("rehearsal2-list", wd)
    note("[block rehearsal2-list]: 18 and 72", f"rc {rc}: {txt}", "18 rehearsal seeds, 72 noise seeds", wd / "EXCLUDED_REHEARSAL2.json")
    r2b = (wd / "EXCLUDED_REHEARSAL2.json").read_bytes()
    r1 = json.loads((fx / "DRAW.json").read_text())
    want_a = A.rehearsal2_list(frz, r1, (fx / "DRAW.json").read_bytes())
    note("[block rehearsal2-list] = analysis.rehearsal2_list", "identical" if r2b == want_a else "differ", "identical",
         wd / "EXCLUDED_REHEARSAL2.json")
    # rehearsal 2, a stand-in on round 20000000 over rehearsal 2's list, announced 600 s before the round
    br = dict(round=20000000, randomness="f39c98df5525968e6622e0c63edb3d1f9c5607cf780db78abdded36e4b3dba95",
              signature="96892582a33552a7b67ba44ef09c3ccd535bbebe760c93ecf45be8958d0c0f06390c6d19d7bf492eb806af7eef6b125c")
    t0 = beacon_verify.round_time(beacon_chain.QUICKNET, br["round"]) - beacon_verify.DELAY_S
    push = datetime.datetime.fromtimestamp(t0, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    (wd / "ANNOUNCE_REHEARSAL2.txt").write_text(f"format layered-draw-announce/1\nmode rehearsal\nexcluded_sha256 "
                                                f"{hashlib.sha256(r2b).hexdigest()}\nsizes NOT1=6 ANDOR3=6 XOR3=6\n")
    d2 = D.draw(br["randomness"], br["round"], json.loads(r2b), dict(NOT1=6, ANDOR3=6, XOR3=6))
    (wd / "DRAW_REHEARSAL.json").write_bytes(D.canon(dict(d2, beacon_round=br, announce=dict(
        branch=A.ANNOUNCE_BRANCH["rehearsal"], commit="0" * 40, push_utc=push))))
    # the stand-in second scan: the freeze's list plus three integers no rehearsal seed or noise seed is
    s1 = sorted(s for v in r1["groups"].values() for s in v)
    s2 = sorted(s for v in d2["groups"].values() for s in v)
    taken = set(frz["seeds"]) | {x for s in s1 + s2 for x in [s] + [10 * s + j for j in range(4)]}
    new3 = [x for x in range(12000, 99999) if x not in taken][:3]
    sc = sorted(set(frz["seeds"]) | set(new3))
    scan = dict(frz, seeds=sc, count=len(sc), seeds_sha256=hashlib.sha256(D.canon(sc)).hexdigest())
    (wd / "EXCLUDED_SECOND_SCAN.json").write_bytes(D.canon(scan))
    rc, txt = block("list", wd)
    note("[block list]: 36 and 144", f"rc {rc}: {txt}", "36 rehearsal seeds, 144 noise seeds", wd / "EXCLUDED_SECOND.json")
    secb = (wd / "EXCLUDED_SECOND.json").read_bytes()
    want_b = A.campaign_list(scan, d2, (wd / "DRAW_REHEARSAL.json").read_bytes(), r1, (fx / "DRAW.json").read_bytes())
    note("[block list] = analysis.campaign_list", "identical" if secb == want_b else "differ", "identical",
         wd / "EXCLUDED_SECOND.json")

    def mutants(exact, keep):
        """One extra seed (count, seeds_sha256 recomputed), one seed removed (one of `keep`'s, not a rehearsal seed),
        one field changed (the rule's text)."""
        x = json.loads(exact)
        extra = next(s for s in range(10000, 99999) if s not in set(x["seeds"]))
        gone = next(s for s in keep if s not in {y for s in s1 + s2 for y in [s] + [10 * s + j for j in range(4)]})
        out_ = {}
        for label, seeds in (("one extra seed", sorted(x["seeds"] + [extra])), ("one seed removed", [s for s in x["seeds"] if s != gone])):
            m = dict(x, seeds=seeds, count=len(seeds), seeds_sha256=hashlib.sha256(D.canon(seeds)).hexdigest())
            assert m["count"] == len(set(m["seeds"])) and m["seeds"] == sorted(set(m["seeds"]))   # the old check's terms hold
            out_[label] = (D.canon(m), extra if label == "one extra seed" else gone)
        out_["a field changed"] = (D.canon(dict(x, rule=x["rule"] + " (edited)")), "rule")
        return out_
    # ---- the blocks
    for name, lst, exact in (("check-rehearsal2-list", "EXCLUDED_REHEARSAL2.json", r2b),
                             ("check-list", "EXCLUDED_SECOND.json", secb)):
        rc, txt = block(name, wd)
        note(f"[block {name}]: the exact list", f"rc {rc}: {txt}", "the list is right", wd / lst)
        for label, (b, what) in mutants(exact, frz["seeds"] if name == "check-rehearsal2-list" else new3).items():
            mw = wd / f"mut_{name}_{label.replace(' ', '_')}"
            shutil.copytree(wd, mw, ignore=shutil.ignore_patterns("mut_*"))
            (mw / lst).write_bytes(b)
            for alone in (False, True):
                rc, txt = block(name, mw, alone)
                ok_ = rc != 0 and "the list is right" not in txt
                tag = "its own rebuild alone" if alone else "as written"
                got = f"rc {rc}, {'refused' if ok_ else 'NOT REFUSED'}: {txt}"
                note(f"[block {name}] {tag}: {label} ({what}) refused", got,
                     "THE LIST IS WRONG" if alone else ("refused:" if ok_ else "the exact union"), mw / lst)
                if not ok_:
                    oks.append(False)
    # ---- the analysis, rehearsal mode (rehearsal 2's own analysis) and campaign mode
    later = (datetime.datetime.now(datetime.timezone.utc) + datetime.timedelta(days=1)).strftime("%Y-%m-%dT%H:%M:%SZ")
    r1kw = dict(rehearsal1_draw=str(wd / "DRAW_REHEARSAL1.json"), rehearsal1_excluded=str(wd / "EXCLUDED_REHEARSAL1.json"),
                rehearsal1_announce=str(wd / "ANNOUNCE_REHEARSAL1.txt"))
    r2kw = dict(rehearsal_draw=str(wd / "DRAW_REHEARSAL.json"), rehearsal_excluded=str(wd / "EXCLUDED_REHEARSAL2.json"),
                rehearsal_announce=str(wd / "ANNOUNCE_REHEARSAL2.txt"))
    (wd / "a_out").mkdir()

    def call(kw, mode, info=None):
        try:
            r = A.check_rehearsal_seeds(dict(kw), info or dict(announce=dict(push_utc=later)), wd / "a_out", None, False, mode)
            return "accepted: " + json.dumps(r.get("exact_union"), sort_keys=True)
        except SystemExit as e:
            return str(e)

    def put(name, b):
        f = wd / name
        f.write_bytes(b)
        return str(f)
    for mode, kw0, exact, keep in (("rehearsal", r1kw, r2b, frz["seeds"]),
                                   ("campaign", dict(r1kw, **r2kw, second_scan=str(wd / "EXCLUDED_SECOND_SCAN.json")), secb, new3)):
        note(f"analysis {mode} mode: the exact list accepted", call(dict(kw0, excluded=put(f"a_{mode}_exact.json", exact)), mode),
             '"sha256": "' + hashlib.sha256(exact).hexdigest(), wd / f"a_{mode}_exact.json")
        for label, (b, what) in mutants(exact, keep).items():
            needle = {"one extra seed": f"adds 1 seeds that are not in the exact union of", "one seed removed":
                      f"is missing 1 seeds of the exact union of", "a field changed": f"another field differs"}[label]
            needle += {"one extra seed": f"", "one seed removed": "", "a field changed": ""}[label]
            f = put(f"a_{mode}_{label.replace(' ', '_')}.json", b)
            got = call(dict(kw0, excluded=f), mode)
            note(f"analysis {mode} mode: {label} refused", got, needle, f)
            oks.append(str(what) in got)                    # the refusal names the seed or the field
    ckw = dict(r1kw, **r2kw, excluded=str(wd / "a_campaign_exact.json"))
    note("analysis campaign mode: second_scan= missing refused", call(ckw, "campaign"),
         "second_scan=EXCLUDED_SECOND_SCAN.json (the second scan's raw output, published with the campaign announce) is required",
         wd / "a_campaign_exact.json")
    lost = [s for s in sc if s != frz["seeds"][5]]
    sub = put("a_scan_not_superset.json", D.canon(dict(scan, seeds=lost, count=len(lost),
                                                       seeds_sha256=hashlib.sha256(D.canon(lost)).hexdigest())))
    note("analysis campaign mode: second_scan= not a superset refused", call(dict(ckw, second_scan=sub), "campaign"),
         f"second_scan= is not a superset of the freeze's EXCLUDED.json: it lacks 1 of its seeds [{frz['seeds'][5]}]", sub)
    note("analysis campaign mode: second_scan= not the announce's refused",
         call(dict(ckw, second_scan=str(wd / "EXCLUDED_SECOND_SCAN.json")), "campaign",
              dict(announce=dict(push_utc=later, second_scan_sha256="0" * 64))),
         "not the second_scan_sha256 000000000000 the campaign announce names", wd / "EXCLUDED_SECOND_SCAN.json")
    note("analysis campaign mode: second_scan= the announce's accepted",
         call(dict(ckw, second_scan=str(wd / "EXCLUDED_SECOND_SCAN.json")), "campaign",
              dict(announce=dict(push_utc=later, second_scan_sha256=A.sha(wd / "EXCLUDED_SECOND_SCAN.json")))),
         "accepted: ", wd / "EXCLUDED_SECOND_SCAN.json")
    note("analysis rehearsal mode: second_scan= refused",
         call(dict(r1kw, excluded=str(wd / "a_rehearsal_exact.json"), second_scan=str(wd / "EXCLUDED_SECOND_SCAN.json")), "rehearsal"),
         "rehearsal mode: second_scan= is for campaign mode only", wd / "EXCLUDED_SECOND_SCAN.json")
    # ---- the announce's fifth line
    h = "a" * 64

    def parse(text):
        try:
            return "parsed: " + json.dumps(A.parse_announce(text.encode()), sort_keys=True)
        except SystemExit as e:
            return str(e)
    four = "format layered-draw-announce/1\nmode {m}\nexcluded_sha256 " + h + "\nsizes NOT1=60 ANDOR3=32 XOR3=37\n"
    five = four.replace("\nsizes", f"\nsecond_scan_sha256 {'b' * 64}\nsizes")
    note("parse_announce: campaign with second_scan_sha256 parsed", parse(five.format(m="campaign")),
         f'"second_scan_sha256": "{"b" * 64}"', ANALYSIS)
    note("parse_announce: campaign without it refused", parse(four.format(m="campaign")),
         "second_scan_sha256 with mode campaign only", ANALYSIS)
    note("parse_announce: rehearsal with it refused", parse(five.format(m="rehearsal")),
         "second_scan_sha256 with mode campaign only", ANALYSIS)
    note("parse_announce: rehearsal without it parsed", parse(four.format(m="rehearsal")), '"mode": "rehearsal"', ANALYSIS)
    # ---- analysis.py test mode: second_scan= refused
    (wd / "empty_root").mkdir()
    r = sh(PY, "-B", ANALYSIS, "test", wd / "t_out", wd / "empty_root", f"second_scan={wd / 'EXCLUDED_SECOND_SCAN.json'}")
    note("analysis.py test mode: second_scan= refused", f"rc {r.returncode}: {r.stdout}{r.stderr}",
         "test mode: second_scan= is for campaign mode only", ANALYSIS)
    oks.append(r.returncode != 0)
    return all(oks), dict(checks=checks, results=out, new_scan_integers=new3)
