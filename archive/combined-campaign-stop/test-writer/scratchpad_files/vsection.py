# ------------------------------------------------------------------------------------------------ L: the scan itself
# The owner's decisions after the review of a5ba132b (spec relayed 2026-11-28): second_scan= must be draw_seeds.py
# scan's own output, self-consistent and canonical (one refusal each); a missing or unreadable scan is an explicit
# refusal naming the file; [block verify-scan], run on a second machine, reproduces the scan from its own ls-remote
# and [block announce] refuses unless its sha256 VS equals HS.

def rebuild_campaign_list(w, scan_obj):
    """[block list]'s rule, in the test: the scan plus both rehearsals' seeds and noise seeds, with "added" (bools of
    the scan are written as the integers they equal, so the list itself stays a list of integers)."""
    import draw_seeds as DS
    rb, rb1 = (w / "DRAW_REHEARSAL.json").read_bytes(), (w / "DRAW_REHEARSAL1.json").read_bytes()
    rs = sorted({s for b in (rb, rb1) for v in json.loads(b)["groups"].values() for s in v})
    noise = sorted(10 * s + n for s in rs for n in range(4))
    seeds = sorted({int(x) for x in scan_obj["seeds"]} | set(rs) | set(noise))
    out = dict(scan_obj, seeds=seeds, count=len(seeds), seeds_sha256=hashlib.sha256(DS.canon(seeds)).hexdigest(),
               added=dict(rehearsal_seeds=rs, noise_seeds=noise, rehearsal_draw_sha256=hashlib.sha256(rb).hexdigest(),
                          rehearsal1_draw_sha256=hashlib.sha256(rb1).hexdigest()))
    return DS.canon(out)


def scan_variant(obj, variant):
    """The bytes of the scan with exactly one defect; everything else valid (count and seeds_sha256 recomputed over
    the seeds as written, except in the cases on those two fields)."""
    import draw_seeds as DS
    sha_of = lambda seeds: hashlib.sha256(DS.canon(seeds)).hexdigest()
    o = json.loads(json.dumps(obj))
    if variant == "noncanon":
        return (json.dumps(o, sort_keys=True, indent=1) + "\n").encode()
    if variant == "format":
        o["format"] = "layered-excluded-seeds/0"
    elif variant == "rule":
        o["rule"] = o["rule"] + " (edited)"
    elif variant in ("unsorted", "duplicate", "bool"):
        s = list(o["seeds"])
        if variant == "unsorted":
            s[0], s[1] = s[1], s[0]
        elif variant == "duplicate":
            s.insert(1, s[0])
        else:
            assert 1 in s
            s[s.index(1)] = True
        o.update(seeds=s, count=len(s), seeds_sha256=sha_of(s))
    elif variant == "count":
        o["count"] += 1
    elif variant == "seeds_sha256":
        o["seeds_sha256"] = sha_of(o["seeds"] + [9999999])
    elif variant == "refs_malformed":
        k = next(k for k in sorted(o["refs"]) if k != "HEAD")
        o["refs"][k] = dict(tip="not a tip", numbers=o["refs"][k].get("numbers", 0))
    elif variant == "refs_no_head":
        del o["refs"]["HEAD"]
    elif variant == "refs_duplicate":       # canonical bytes with one ref name written twice
        b = DS.canon(o).decode()
        k = next(k for k in sorted(o["refs"]) if k != "HEAD")
        entry = json.dumps({k: o["refs"][k]}, sort_keys=True, separators=(",", ":"))[1:-1]
        return b.replace(entry, entry + "," + entry, 1).encode()
    return DS.canon(o)


SCAN_VARIANTS = {
    "noncanon": "the scan's bytes are not draw_seeds.canon of its JSON (indented)",
    "format": "its format is not draw_seeds.py scan's",
    "rule": "its rule text is not draw_seeds.py scan's",
    "unsorted": "two seeds swapped (count and seeds_sha256 recomputed over them)",
    "duplicate": "one seed written twice (count and seeds_sha256 recomputed)",
    "bool": "the seed 1 written as true (count and seeds_sha256 recomputed)",
    "count": "count one more than the seeds",
    "seeds_sha256": "seeds_sha256 of other seeds",
    "refs_malformed": "one ref's tip is not a commit sha",
    "refs_duplicate": "one ref name written twice in the bytes",
    "refs_no_head": "no HEAD entry in refs",
}
SCAN_MESSAGES = {}


def scan_case(variant):
    """Campaign mode through check_draw + check_rehearsal_seeds: second_scan= the scan with one defect, the announce
    naming its sha256, excluded= rebuilt from it by [block list]'s rule and the draw over that list. Must be refused,
    in check_rehearsal_seeds (or a helper), with a message naming second_scan= that no other variant gives and that is
    not the exact union's. Gated on list_funcs_campaign_exact."""
    def case(tmp, src):
        w, name, _ = list_case_files(tmp, "campaign", None)
        sb = scan_variant(json.loads((w / "EXCLUDED_SECOND_SCAN.json").read_bytes()), variant)
        (w / "SCAN_X.json").write_bytes(sb)
        (w / name).write_bytes(rebuild_campaign_list(w, json.loads(sb)))
        eb = (w / name).read_bytes()
        fmt = campaign_announce_format()
        _, p, _ = announced_draw(w, "CASE", ROUND_C, json.loads(eb), eb, CAMPAIGN_SIZES, "campaign",
                                 "evidence/combined-draw", fmt=fmt, second_scan_sha256=sha(w / "SCAN_X.json"))
        kw = dict(draw=str(p["draw"]), excluded=str(p["excluded"]), announce=str(p["announce"]),
                  rehearsal_draw=str(w / "DRAW_REHEARSAL.json"), rehearsal_excluded=str(w / "EXCLUDED_REHEARSAL2.json"),
                  rehearsal_announce=str(w / "ANNOUNCE_R2.txt"), rehearsal1_draw=str(w / "DRAW_REHEARSAL1.json"),
                  rehearsal1_excluded=str(w / "EXCLUDED_REHEARSAL1.json"), rehearsal1_announce=str(w / "ANNOUNCE_R1.txt"),
                  **{SECOND_SCAN_ARG: str(w / "SCAN_X.json")})
        res = run_funcs(kw, "campaign")
        msg = res.get("message") or ""
        SCAN_MESSAGES[variant] = msg
        obs = dict(variant=variant, defect=SCAN_VARIANTS[variant], scan_sha256=sha(w / "SCAN_X.json"),
                   announce_format=fmt, expected_check="the second scan's own check: " + SCAN_VARIANTS[variant],
                   control_passed=LIST_CONTROL.get(("funcs", "campaign"), False), **res)
        own = (res.get("within") == "check_rehearsal_seeds" and SECOND_SCAN_ARG in msg and CU not in msg
               and not any(o in msg for o in OLD_INCLUSION))
        if variant == list(SCAN_VARIANTS)[-1]:      # the last: every variant's message differs from the others'
            msgs = [SCAN_MESSAGES.get(v) for v in SCAN_VARIANTS]
            obs["messages_distinct"] = len(set(msgs)) == len(msgs) and None not in msgs
            own = own and obs["messages_distinct"]
        obs["reached_own_check"] = own
        return own and obs["control_passed"], obs
    case.__name__ = f"case_scan_{variant}"
    return case


def scan_file_case(kind):
    """second_scan= missing (a path that does not exist) or unreadable (a directory): an explicit refusal naming the
    file, no traceback. Gated on list_funcs_campaign_exact."""
    def case(tmp, src):
        w, name, _ = list_case_files(tmp, "campaign", None)
        eb = (w / name).read_bytes()
        fmt = campaign_announce_format()
        _, p, _ = announced_draw(w, "CASE", ROUND_C, json.loads(eb), eb, CAMPAIGN_SIZES, "campaign",
                                 "evidence/combined-draw", fmt=fmt, second_scan_sha256=sha(w / "EXCLUDED_SECOND_SCAN.json"))
        bad = w / ("NO_SUCH_SCAN.json" if kind == "missing" else "SCAN_DIR.json")
        if kind == "unreadable":
            bad.mkdir()
        kw = dict(draw=str(p["draw"]), excluded=str(p["excluded"]), announce=str(p["announce"]),
                  rehearsal_draw=str(w / "DRAW_REHEARSAL.json"), rehearsal_excluded=str(w / "EXCLUDED_REHEARSAL2.json"),
                  rehearsal_announce=str(w / "ANNOUNCE_R2.txt"), rehearsal1_draw=str(w / "DRAW_REHEARSAL1.json"),
                  rehearsal1_excluded=str(w / "EXCLUDED_REHEARSAL1.json"), rehearsal1_announce=str(w / "ANNOUNCE_R1.txt"),
                  **{SECOND_SCAN_ARG: str(bad)})
        res = run_funcs(kw, "campaign")
        msg = res.get("message") or ""
        obs = dict(kind=kind, file=bad.name, control_passed=LIST_CONTROL.get(("funcs", "campaign"), False),
                   expected_check="an explicit refusal naming the file", **res)
        own = res.get("refused") is True and bad.name in msg and not res.get("crashed")
        obs["reached_own_check"] = own
        return own and obs["control_passed"], obs
    case.__name__ = f"case_scan_file_{kind}"
    return case


# [block verify-scan]: a local twin of the repository (no network), whose scan holds the pinned list
VS_BRANCHES = ("main", "evidence/twin-a", "evidence/twin-b")
VS_BASE = {}


def twin_repository(tmp):
    """A bare repository with VS_BRANCHES. main holds pinned_seeds.txt, one line "seed NNNNNNN" (7 digits, zero
    padded) per seed of the pinned EXCLUDED.json, so that its scan is a superset of the pinned list; the two other
    branches each add one file with other integers. Its main commit's author is a test identity."""
    bare, work = tmp / "twin.git", tmp / "twin_work"
    git("init", "-q", "--bare", str(bare))
    git("init", "-q", "-b", "main", str(work))
    ident = ["-c", "user.name=defect test", "-c", "user.email=defect-test@localhost"]
    pinned = json.loads((HERE / "EXCLUDED.json").read_bytes())["seeds"]
    (work / "pinned_seeds.txt").write_text("".join(f"seed {s:07d}\n" for s in pinned))
    git("add", ".", cwd=work)
    git(*ident, "commit", "-q", "-m", "twin main", cwd=work)
    for k, br in enumerate(VS_BRANCHES[1:]):
        git("checkout", "-q", "-b", br, "main", cwd=work)
        (work / f"twin_{k}.txt").write_text(f"seed {7654321 - k}\nnoise_seed {6543210 - k}\n")
        git("add", ".", cwd=work)
        git(*ident, "commit", "-q", "-m", f"twin {br}", cwd=work)
    git("push", "-q", str(bare), *[f"{b}:refs/heads/{b}" for b in VS_BRANCHES], cwd=work)
    git("symbolic-ref", "HEAD", "refs/heads/main", cwd=bare)
    return bare


def twin_env(tmp, bare):
    cfg = tmp / "gitconfig"
    cfg.write_text(f'[url "file://{bare}"]\n\tinsteadOf = https://github.com/HevisNico/kernel-R\n')
    return dict(os.environ, GIT_CONFIG_GLOBAL=str(cfg), GIT_CONFIG_NOSYSTEM="1", GIT_ALLOW_PROTOCOL="file")


def bash_blocks(w, env, names, fill):
    """Run blocks verbatim, in one bash, after the vars preamble and [block vars-campaign] with its placeholders
    filled by fill(name, description) (None: an unknown placeholder, recorded)."""
    import re
    blocks = freeze_blocks()
    missing = [n for n in names if n not in blocks]
    lines, unknown = [], []
    for ln in blocks["vars-campaign"].splitlines():
        m = re.fullmatch(r"(\w+)=<([^>]*)>\s*", ln)
        if m:
            v = fill(m.group(1), m.group(2))
            if v is None:
                unknown.append(ln)
            ln = f"{m.group(1)}={v}"
        lines.append(ln)
    if missing:
        return None, dict(missing_blocks=missing, unknown_placeholders=unknown)
    pre = f'L={HERE}\nF=$(git -C "$L" rev-parse HEAD)\nPY={PY}\npython() {{ "$PY" "$@"; }}\n' + "\n".join(lines) + "\n"
    r = subprocess.run(["bash", "-c", pre + "".join(blocks[n] for n in names)], cwd=w, env=env, capture_output=True,
                       text=True)
    return r, dict(blocks=names, exit=r.returncode, stdout=r.stdout[-1500:], stderr=r.stderr[-1500:],
                   unknown_placeholders=unknown)


def vs_base(tmp):
    """The twin, and its scan reproduced by [block second-scan] verbatim (the canonical scan of the twin)."""
    if VS_BASE:
        return VS_BASE
    base = list_base(tmp)
    root = tmp.parent / "_vs_base"
    root.mkdir()
    bare = twin_repository(root)
    env = twin_env(root, bare)
    w = root / "scan"
    w.mkdir()
    r, obs = bash_blocks(w, env, ["second-scan"], lambda n, d: "0" * 64)
    assert r is not None and r.returncode == 0, obs
    scan = json.loads((w / "EXCLUDED_SECOND_SCAN.json").read_bytes())
    assert set(base["pinned"]["seeds"]) <= set(scan["seeds"]), "the twin's scan does not hold the pinned list"
    VS_BASE.update(bare=bare, env=env, scan=(w / "EXCLUDED_SECOND_SCAN.json").read_bytes(),
                   scan_sha256=sha(w / "EXCLUDED_SECOND_SCAN.json"), refs=sorted(scan["refs"]))
    return VS_BASE


VS_KINDS = {
    None: "the twin's scan as [block second-scan] makes it (control): verify-scan passes, VS = HS",
    "plus3": "the canonical scan plus 3 integers, count and seeds_sha256 recomputed (the owner's acceptance case): "
             "verify-scan fails before any announce commit, and [block announce] refuses",
    "omit_branch": "the scan without one branch's ref entry: verify-scan fails",
    "wrong_tip": "one ref with another commit's tip: verify-scan fails",
}
VS_CONTROL = {}


def verify_scan_case(kind):
    """[block verify-scan] verbatim in a fresh folder on the twin (no network), with EXCLUDED_SECOND_SCAN.json the case's
    scan and HS its sha256, then (plus3) [block announce] with VS the twin scan's reproduced sha256."""
    def case(tmp, src):
        import draw_seeds as DS
        vb = vs_base(tmp)
        w, name, _ = list_case_files(tmp, "campaign", None)
        o = json.loads(vb["scan"])
        if kind == "plus3":
            extra = [i for i in range(1000001, 9999999) if i not in o["seeds"]][:3]
            o = regen(o, o["seeds"] + extra)
        elif kind == "omit_branch":
            del o["refs"][next(k for k in o["refs"] if k.endswith("twin-a"))]
        elif kind == "wrong_tip":
            k = next(k for k in o["refs"] if k.endswith("twin-b"))
            o["refs"][k]["tip"] = o["refs"][next(k2 for k2 in o["refs"] if k2.endswith("twin-a"))]["tip"]
        (w / "EXCLUDED_SECOND_SCAN.json").write_bytes(DS.canon(o))
        (w / name).unlink()
        bl = run_block(w, "list", {})
        hs, vs = sha(w / "EXCLUDED_SECOND_SCAN.json"), vb["scan_sha256"]

        def fill(n, d):
            d = d.lower()
            return sha(w / name) if n == "H" else vs if ("verify" in d or n == "VS") else hs if "scan" in d else None
        r, obs = bash_blocks(w, vb["env"], ["verify-scan"], fill)
        obs.update(kind=kind, list_block_exit=bl["exit"], HS=hs, VS_reproduced=vs, scan_changed=hs != vs,
                   expected_check=VS_KINDS[kind])
        if r is None:
            return False, obs
        if kind is None:
            VS_CONTROL["ok"] = ok = r.returncode == 0 and hs == vs and vs in r.stdout and not obs["unknown_placeholders"]
            return ok, obs
        obs["control_passed"] = VS_CONTROL.get("ok", False)
        ok = r.returncode != 0 and not (w / "announce_campaign").exists()
        if kind == "plus3":            # and the announce, with VS != HS, refuses before its commit
            ra, oa = bash_blocks(w, vb["env"], ["announce"], fill)
            pushed = subprocess.run(["git", "-C", str(vb["bare"]), "rev-parse", "-q", "--verify",
                                     "refs/heads/evidence/combined-draw"], capture_output=True).returncode == 0
            repo = w / "announce_campaign"
            commit = repo.is_dir() and subprocess.run(["git", "-C", str(repo), "rev-parse", "-q", "--verify", "HEAD"],
                                                      capture_output=True).returncode == 0
            obs["announce"] = dict(oa, commit_made=commit, pushed_to_twin=pushed)
            ok = ok and ra is not None and ra.returncode != 0 and "REFUSED" in ra.stdout and not commit and not pushed
        obs["refused_before_announce"] = ok
        return ok and obs["control_passed"], obs
    case.__name__ = f"case_verify_scan_{kind or 'exact'}"
    return case


