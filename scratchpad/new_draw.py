def parse_announce(b):
    """DRAW_ANNOUNCE.txt: exactly the lines `format layered-draw-announce/1`, `mode M`, `excluded_sha256 H`,
    `sizes NOT1=n ANDOR3=n XOR3=n`."""
    try:
        lines = b.decode().split("\n")
    except UnicodeDecodeError:
        refuse("DRAW_ANNOUNCE.txt is not UTF-8")
    if lines and lines[-1] == "":
        lines = lines[:-1]
    kv = dict((ln.split(" ", 1) + [""])[:2] for ln in lines)
    if len(kv) != len(lines) or set(kv) != set(ANNOUNCE_KEYS) or kv["format"] != ANNOUNCE_FORMAT:
        refuse(f"DRAW_ANNOUNCE.txt is not exactly the lines {ANNOUNCE_KEYS} ({ANNOUNCE_FORMAT})")
    try:
        sizes = {g: int(v) for g, v in (x.split("=") for x in kv["sizes"].split())}
    except ValueError:
        refuse(f"DRAW_ANNOUNCE.txt: sizes {kv['sizes']!r}")
    return dict(mode=kv["mode"], excluded_sha256=kv["excluded_sha256"], sizes=sizes)


def announce_on_github(branch, outdir):
    """The first commit adding DRAW_ANNOUNCE.txt on `branch` (first-parent), its file, and GitHub's push time of it
    (sealpush.github_times; every activity item saved in OUTDIR/activity/)."""
    remote = json.loads(CP.FROZEN_TEMPLATE.read_text())["seal_push"]["remote"]
    with tempfile.TemporaryDirectory() as w:
        try:
            SP.git("init", "-q", cwd=w)
            SP.git("fetch", "-q", str(remote), f"refs/heads/{branch}", cwd=w)
            adds = SP.git("log", "--first-parent", "--reverse", "--diff-filter=A", "--format=%H", "FETCH_HEAD", "--",
                          ANNOUNCE_FILE, cwd=w).stdout.split()
            if not adds:
                refuse(f"no commit adds {ANNOUNCE_FILE} on {branch}")
            commit = adds[0]
            text = subprocess.run(["git", "show", f"{commit}:{ANNOUNCE_FILE}"], cwd=w, capture_output=True,
                                  check=True).stdout
            tm = push_times(remote, branch, "github", outdir)
        except Refused:
            raise
        except Exception as e:                            # never reinterpreted: the analysis is rerun later
            refuse(f"the draw's announce cannot be read from GitHub ({branch}): {e!r}"[:500])
    if commit not in tm:
        refuse(f"GitHub records no push of the announce commit {commit[:12]} as the tip of {branch}")
    return commit, text, tm[commit]


def check_draw(kw, mode, outdir):
    """B16 and D8, the owner's rule: the draw recomputed in full from public inputs only. Returns (the RECOMPUTED
    draw, its record, a notice or None)."""
    import beacon_chain
    import beacon_verify
    import draw_seeds
    b = Path(kw["draw"]).read_bytes()
    try:
        d = json.loads(b)
    except ValueError as e:
        refuse(f"DRAW.json is not JSON: {e}")
    if mode == "test" and DRAW_EXTRA_KEYS[0] not in d:   # a test draw with no beacon: plans checked, not the draw
        if not isinstance(d.get("groups"), dict):
            refuse("DRAW.json has no groups")
        return d, dict(sha256=hashlib.sha256(b).hexdigest(), sizes={g: len(v) for g, v in d["groups"].items()},
                       machines=MACHINES, recomputed=False,
                       note="test mode, a draw with no beacon_round: not recomputed, no signature; its own sizes"), \
            "test draw: not recomputed, no beacon signature (test mode)"
    br, an = d.get("beacon_round"), d.get("announce")
    if not isinstance(br, dict) or set(br) != {"round", "signature", "randomness"}:
        refuse("DRAW.json has no beacon_round {round, signature, randomness}")
    if not isinstance(an, dict) or set(an) != {"branch", "commit", "push_utc"}:
        refuse("DRAW.json has no announce {branch, commit, push_utc}")
    if not isinstance(d.get("beacon"), str) or not isinstance(d.get("round"), int):
        refuse("DRAW.json has no beacon string and round integer")
    if "excluded" not in kw:
        refuse("a draw with a beacon needs excluded=EXCLUDED.json (the published exclusion list it used)")
    notice = None
    # the announce: on GitHub in campaign and rehearsal modes; offline (announce=, DRAW.json's push time) in test mode
    if mode == "test":
        if "announce" not in kw:
            refuse("test mode: a draw with a beacon needs announce=DRAW_ANNOUNCE.txt")
        ab, push_utc = Path(kw["announce"]).read_bytes(), an["push_utc"]
        notice = "test draw: the announce and its push time are DRAW.json's own, not read from GitHub (test mode)"
    else:
        if "announce" in kw:
            refuse(f"{mode} mode reads the announce from GitHub, not announce=")
        if an["branch"] != ANNOUNCE_BRANCH[mode]:
            refuse(f"{mode} mode: the announce branch is {ANNOUNCE_BRANCH[mode]}, not {an['branch']!r}")
        commit, ab, push_utc = announce_on_github(an["branch"], outdir)
        if commit != an["commit"] or push_utc != an["push_utc"]:
            refuse(f"DRAW.json's announce ({an['commit'][:12]}, {an['push_utc']}) is not GitHub's: the first commit "
                   f"adding {ANNOUNCE_FILE} on {an['branch']} is {commit[:12]}, pushed {push_utc}")
    A = parse_announce(ab)
    if A["mode"] != mode:
        refuse(f"DRAW_ANNOUNCE.txt says mode {A['mode']}, not {mode}")
    sizes = DRAW_SIZES if mode == "campaign" else DRAW_SIZES_REHEARSAL if mode == "rehearsal" else d.get("n")
    if not isinstance(sizes, dict) or A["sizes"] != sizes:
        refuse(f"DRAW_ANNOUNCE.txt's sizes {A['sizes']} are not the sizes of {mode} mode {sizes}")
    # the exclusion list: the announced one, a superset of the freeze's
    eb = Path(kw["excluded"]).read_bytes()
    if hashlib.sha256(eb).hexdigest() != A["excluded_sha256"]:
        refuse("the excluded= file is not the one DRAW_ANNOUNCE.txt names (excluded_sha256)")
    ex = json.loads(eb)
    pinned = json.loads((HERE / "EXCLUDED.json").read_text())
    if not set(pinned["seeds"]) <= set(ex.get("seeds") or []):
        refuse("the excluded= list is not a superset of the freeze's EXCLUDED.json")
    # the round from the announce's push time, the beacon's signature
    if not beacon_chain.check():
        refuse("the pinned quicknet chain does not check")
    want_round = beacon_verify.round_after(beacon_chain.QUICKNET, push_utc)
    if d["round"] != want_round:
        refuse(f"DRAW.json's round {d['round']} is not the round the announce's push time fixes ({want_round}, "
               f"{push_utc} + {beacon_verify.DELAY_S} s)")
    if br["round"] != d["round"] or br["randomness"].lower() != d["beacon"].lower():
        refuse(f"DRAW.json: the beacon is not the randomness of round {d['round']}")
    v = beacon_verify.verify(beacon_chain.QUICKNET, br)
    if not v.get("ok"):
        refuse(f"DRAW.json: the beacon round does not verify against the pinned quicknet key: {v}")
    # the seeds, recomputed
    with contextlib.redirect_stdout(io.StringIO()):
        try:
            again = draw_seeds.draw(d["beacon"], d["round"], ex, dict(sizes))
        except AssertionError as e:
            refuse(f"the draw cannot be recomputed: {e}")
    if b != draw_seeds.canon(dict(again, beacon_round=br, announce=an)):
        refuse("DRAW.json is not draw_seeds.draw of its beacon and round on the excluded= list at the sizes "
               f"{sizes} (with its beacon_round and announce), byte for byte")
    return again, dict(sha256=hashlib.sha256(b).hexdigest(), beacon=d["beacon"], round=d["round"], sizes=dict(sizes),
                       machines=MACHINES, recomputed=True, signature_verified=True,
                       excluded=dict(file=Path(kw["excluded"]).name, sha256=A["excluded_sha256"],
                                     seeds_sha256=ex.get("seeds_sha256"), count=ex.get("count"),
                                     superset_of_freeze=pinned["seeds_sha256"]),
                       announce=dict(an, from_github=mode != "test", sha256=hashlib.sha256(ab).hexdigest())), notice


def expected_plans(draw):
    """The 12 plans of the RECOMPUTED draw (plan_split3 on the frozen template)."""
    import plan_split3
    t = json.loads(CP.FROZEN_TEMPLATE.read_text())
    plans, _ = plan_split3.split(draw, t, MACHINES)
    return {f"K{k:02d}": p for k, p in enumerate(plans, start=1)}, t


