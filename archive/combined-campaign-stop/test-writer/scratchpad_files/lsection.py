# ------------------------------------------------------------------------------------------------ L: list exactness
# Rehearsal 2's list must be byte-equal to what [block rehearsal2-list] builds, and the campaign's to what [block list]
# builds from EXCLUDED_SECOND_SCAN.json and the two verified rehearsal draws; the scan must hold the pinned list. Each
# case runs on the FREEZE.txt blocks (extracted as proof2.py extracts them, never edited) and on analysis.py's own
# checks in the order its rehearsal and campaign modes call them: check_draw(kw, mode, ..., offline=True), then
# check_rehearsal_seeds(kw, info, ..., strict=False, mode). Both modes refuse the test roots before any draw check, so
# these two functions are called directly (in a subprocess).
#
# The fixture, built once per run:
# - rehearsal 1: its published DRAW.json (evidence/combined-rehearsal-draw-result at REHEARSAL1's result commit), its
#   EXCLUDED_PUBLISHED.json and DRAW_ANNOUNCE.txt (evidence/combined-rehearsal-draw), fetched by branch name;
# - EXCLUDED_REHEARSAL2.json, written by [block rehearsal2-list];
# - a stand-in rehearsal 2 (published quicknet round 34335000, 6/6/6, mode rehearsal) drawn over that list and announced
#   600 s before its round, after rehearsal 1's announce;
# - EXCLUDED_SECOND_SCAN.json, a twin of the scan's output: the pinned EXCLUDED.json plus SCAN_EXTRA (integers of 7
#   digits that no draw reads), count and seeds_sha256 recomputed;
# - EXCLUDED_SECOND.json, written by [block list];
# - a stand-in campaign draw (round 34340000, 60/32/37, mode campaign) over the case's campaign list.
# A mutated list is announced (its excluded_sha256) and its draw recomputed over it, so check_draw accepts it unless
# the mutation breaks the superset of the pinned list.
#
# The blocks run in bash with L (this tree), F (its HEAD), PY (this python) and python() set as in [block vars], in a
# working folder holding the fixture. A usercustomize.py on PYTHONPATH (the image's sitecustomize is left alone)
# replaces two reads, and only these, once analysis is imported:
# - check_draw called with offline=None in rehearsal or campaign mode (a GitHub read): offline=True and announce= the
#   fixture's DRAW_ANNOUNCE.txt of that draw. So the announce file and its push time are not read from GitHub
#   (announce_on_github), the announce branch name and N1 (freeze_time on research/layered-campaign-freeze) are not
#   checked; the announce's mode, sizes and excluded_sha256, the round, the signature and the recomputed draw are.
# - check_rehearsal_seeds called with strict=True: strict=False (its mode kept), with rehearsal_announce= and
#   rehearsal1_announce= the fixture's announces, so its two draws are checked offline the same way.
# The shim writes one line per replaced read to stderr ("shim: ..."), kept in the record.

ROUND_R2 = dict(round=34335000, randomness="95b68dcc123c90a03aa8609452cb45519c4ed8b054f6e94618455198f10a6fb1",
                signature="86a988abe179f2ea5f9a30f8ff7ee0ca2a6fd3e9245afff6b5d16fc8751ae6b49c58c017d565fa033f46f39ec77af4c7")
ROUND_C = dict(round=34340000, randomness="310a4ed5530b6496e3735158a8d814b106db3fafe3fc31fb4e6a5294cf48e77c",
               signature="a9e6f824268a56d68119afce3fa7e308ed6347e51ffba1fd08ff4f6663ce719811321472d66ca8a28fad244d5b792740")
CAMPAIGN_SIZES = dict(NOT1=60, ANDOR3=32, XOR3=37)
SCAN_EXTRA = (1234567, 2345678, 3456789)
SECOND_SCAN_ARG = "second_scan"                   # the fix's argument: second_scan=EXCLUDED_SECOND_SCAN.json
LIST_WRONG = "THE LIST IS WRONG"                  # the check blocks' verdict on a wrong list
LIST_RIGHT = "the list is right"
OLD_INCLUSION = ("excluded= list lacks",)         # check_rehearsal_seeds's inclusion check (before the fix)

SHIM = '''"""The defect tests' shim (tests/test_analysis_defects.py): two GitHub reads of analysis replaced offline."""
import importlib.machinery, inspect, json, os, sys
ANN = json.loads(os.environ["LAYERED_SHIM_ANNOUNCE"])


def patch(A):
    cd, crs = A.check_draw, A.check_rehearsal_seeds

    def check_draw(*a, **k):
        b = inspect.signature(cd).bind(*a, **k)
        b.apply_defaults()
        x = b.arguments
        if x["offline"] is None and x["mode"] != "test":
            x["kw"] = dict(x["kw"], announce=ANN[os.path.basename(x["kw"]["draw"])])
            x["offline"] = True
            print(f"shim: check_draw {os.path.basename(x['kw']['draw'])} {x['mode']}: offline, announce="
                  f"{os.path.basename(x['kw']['announce'])}", file=sys.stderr)
        return cd(*b.args, **b.kwargs)

    def check_rehearsal_seeds(*a, **k):
        b = inspect.signature(crs).bind(*a, **k)
        b.apply_defaults()
        x = b.arguments
        if x["strict"]:
            kw = dict(x["kw"])
            for pre in ("rehearsal_", "rehearsal1_"):
                if pre + "draw" in kw:
                    kw[pre + "announce"] = ANN[os.path.basename(kw[pre + "draw"])]
            x["kw"], x["strict"] = kw, False
            x["mode"] = x["mode"] if x["mode"] is not None else "campaign"
            print(f"shim: check_rehearsal_seeds {x['mode']}: strict=False, announces offline", file=sys.stderr)
        return crs(*b.args, **b.kwargs)

    A.check_draw, A.check_rehearsal_seeds = check_draw, check_rehearsal_seeds


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

FUNCS = '''import json, sys, tempfile, traceback
sys.path.insert(0, sys.argv[1])
import analysis as A
a = json.loads(sys.argv[2])
out = dict(reached="check_draw")
try:
    d, info, _ = A.check_draw(a["kw"], a["mode"], tempfile.mkdtemp(), None, offline=True)
    out["reached"] = "check_rehearsal_seeds"
    A.check_rehearsal_seeds(a["kw"], info, tempfile.mkdtemp(), None, False, a["mode"])
    out.update(reached="accepted", refused=False)
except A.Refused as e:
    tb = traceback.extract_tb(e.__traceback__)
    out.update(refused=True, message=str(e), raised_in=tb[-2].name if len(tb) > 1 else tb[-1].name)
print(json.dumps(out))
'''


def freeze_blocks():
    """[block NAME] ... [end] of FREEZE.txt, extracted as dev/freeze/final/proof2.py extracts them."""
    import re
    import textwrap
    text = (HERE / "FREEZE.txt").read_text().split("\n")
    blocks, k = {}, 0
    while k < len(text):
        m = re.fullmatch(r"\s*\[block ([a-z0-9-]+)\]\s*", text[k])
        if m:
            j = next(i for i in range(k + 1, len(text)) if text[i].strip() == "[end]")
            assert m.group(1) not in blocks, m.group(1)
            blocks[m.group(1)] = textwrap.dedent("\n".join(text[k + 1:j])) + "\n"
            k = j
        k += 1
    return blocks


def run_block(w, name, announces):
    """Run the block `name` verbatim in bash in the folder w, the shim on PYTHONPATH."""
    shim = w.parent / "shim"
    shim.mkdir(exist_ok=True)
    (shim / "usercustomize.py").write_text(SHIM)
    pre = (f'L={HERE}\nF=$(git -C "$L" rev-parse HEAD)\nPY={PY}\npython() {{ "$PY" "$@"; }}\n')
    env = dict(os.environ, PYTHONPATH=str(shim), LAYERED_SHIM_ANNOUNCE=json.dumps(announces))
    r = subprocess.run(["bash", "-c", pre + freeze_blocks()[name]], cwd=w, env=env, capture_output=True, text=True)
    return dict(block=name, exit=r.returncode, stdout=r.stdout[-1500:], stderr=r.stderr[-2500:])


def run_funcs(kw, mode):
    r = subprocess.run([PY, "-B", "-c", FUNCS, str(HERE), json.dumps(dict(kw=kw, mode=mode))], capture_output=True,
                       text=True)
    if r.returncode != 0 or not r.stdout.strip():
        return dict(crashed=True, exit=r.returncode, stderr=r.stderr[-1500:])
    return json.loads(r.stdout.strip().splitlines()[-1])


def regen(obj, seeds):
    import draw_seeds as DS
    seeds = sorted(set(seeds))
    return dict(obj, seeds=seeds, count=len(seeds), seeds_sha256=hashlib.sha256(DS.canon(seeds)).hexdigest())


LIST_BASE = {}


def list_base(tmp):
    """The shared fixture (see above), built once in the run's temporary folder."""
    if LIST_BASE:
        return LIST_BASE
    sys.path.insert(0, str(HERE))
    import analysis as A
    import draw_seeds as DS
    b = tmp.parent / "_list_base"
    b.mkdir()
    rep = b / "fetch"
    rep.mkdir()
    git("init", "-q", cwd=rep)
    r1 = A.REHEARSAL1
    git("fetch", "-q", origin_url(), f"refs/heads/{r1['result_branch']}", cwd=rep)
    assert git("rev-parse", "FETCH_HEAD", cwd=rep).strip() == r1["result_commit"], "rehearsal 1's result branch moved"
    (b / "DRAW_REHEARSAL1.json").write_bytes(subprocess.run(["git", "show", "FETCH_HEAD:DRAW.json"], cwd=rep,
                                                            check=True, capture_output=True).stdout)
    git("fetch", "-q", origin_url(), f"refs/heads/{r1['announce_branch']}", cwd=rep)
    for f, to in (("EXCLUDED_PUBLISHED.json", "EXCLUDED_REHEARSAL1.json"), ("DRAW_ANNOUNCE.txt", "ANNOUNCE_R1.txt")):
        (b / to).write_bytes(subprocess.run(["git", "show", f"FETCH_HEAD:{f}"], cwd=rep, check=True,
                                            capture_output=True).stdout)
    assert sha(b / "DRAW_REHEARSAL1.json") == r1["draw_sha256"] and sha(b / "EXCLUDED_REHEARSAL1.json") == \
        r1["excluded_sha256"], "rehearsal 1's published files are not the pinned ones"
    bb = run_block(b, "rehearsal2-list", {})
    assert bb["exit"] == 0, bb
    x2b = (b / "EXCLUDED_REHEARSAL2.json").read_bytes()
    R2, p2, t2 = announced_draw(b, "R2", ROUND_R2, json.loads(x2b), x2b, REHEARSAL_SIZES, "rehearsal",
                                "evidence/combined-rehearsal2-draw")
    shutil.copy(p2["draw"], b / "DRAW_REHEARSAL.json")
    shutil.copy(p2["announce"], b / "ANNOUNCE_R2.txt")
    pinned = json.loads((HERE / "EXCLUDED.json").read_bytes())
    assert not set(SCAN_EXTRA) & set(pinned["seeds"])
    (b / "EXCLUDED_SECOND_SCAN.json").write_bytes(DS.canon(regen(pinned, pinned["seeds"] + list(SCAN_EXTRA))))
    bl = run_block(b, "list", {})
    assert bl["exit"] == 0, bl
    rs1 = sorted(s for v in json.loads((b / "DRAW_REHEARSAL1.json").read_text())["groups"].values() for s in v)
    rs2 = sorted(s for v in R2["groups"].values() for s in v)
    LIST_BASE.update(dir=b, pinned=pinned, rs1=rs1, rs2=rs2, rehearsal2_push=t2, blocks=[bb, bl],
                     rehearsal2_list_sha256=sha(b / "EXCLUDED_REHEARSAL2.json"),
                     campaign_list_sha256=sha(b / "EXCLUDED_SECOND.json"))
    return LIST_BASE


def mutate(obj, kind, which, base):
    """The list `obj` with one mutation; seeds changes regenerate count and seeds_sha256."""
    seeds, pinned = list(obj["seeds"]), set(base["pinned"]["seeds"])
    rs = base["rs1"] if which == "rehearsal" else base["rs2"]
    note = None
    if kind == "extra":
        note = next(i for i in range(1000001, 9999999) if i not in seeds)
        return regen(obj, seeds + [note]), note
    if kind == "drop_noise":
        note = next(10 * s + j for s in rs for j in range(4) if 10 * s + j not in pinned and 10 * s + j in seeds)
    elif kind == "drop_scan":
        if which == "rehearsal":     # rehearsal 2's scan is the pinned list itself: a pinned seed, not of rehearsal 1
            ex1 = set(base["rs1"]) | {10 * s + j for s in base["rs1"] for j in range(4)}
            note = next(s for s in sorted(pinned) if s not in ex1)
        else:                        # one of the scan's own seeds beyond the pinned list
            note = SCAN_EXTRA[0]
    elif kind == "field":
        key = "rehearsal1_draw_sha256" if which == "rehearsal" else "rehearsal_draw_sha256"
        note = f"added.{key}"
        return dict(obj, added=dict(obj["added"], **{key: hashlib.sha256(b"another draw").hexdigest()})), note
    seeds.remove(note)
    return regen(obj, seeds), note


def list_case_files(tmp, which, kind):
    """A working folder with the fixture, the list of `which` mutated by `kind` (None: exact)."""
    import draw_seeds as DS
    base = list_base(tmp)
    w = tmp / "work"
    shutil.copytree(base["dir"], w, ignore=shutil.ignore_patterns("fetch"))
    name = "EXCLUDED_REHEARSAL2.json" if which == "rehearsal" else "EXCLUDED_SECOND.json"
    note = None
    if kind in ("extra", "drop_noise", "drop_scan", "field"):
        obj, note = mutate(json.loads((w / name).read_bytes()), kind, which, base)
        (w / name).write_bytes(DS.canon(obj))
    return w, name, note


def list_block_case(which, kind):
    """kind: None (exact), extra, drop_noise, drop_scan, field, no_scan (EXCLUDED_SECOND_SCAN.json absent), scan_short
    (the scan without a pinned seed that rehearsal 1 drew: [block list] rebuilds the same bytes from it)."""
    def case(tmp, src):
        w, name, note = list_case_files(tmp, which, kind)
        obs = dict(list=name, mutation=kind, changed=note)
        if kind == "no_scan":
            (w / "EXCLUDED_SECOND_SCAN.json").unlink()
        elif kind == "scan_short":
            import draw_seeds as DS
            scan = json.loads((w / "EXCLUDED_SECOND_SCAN.json").read_bytes())
            obs["changed"] = drop = LIST_BASE["rs1"][0]
            (w / "EXCLUDED_SECOND_SCAN.json").write_bytes(DS.canon(regen(scan, [s for s in scan["seeds"] if s != drop])))
            (w / "EXCLUDED_SECOND.json").unlink()
            bl = run_block(w, "list", {})
            obs["rebuilt_list_equal"] = sha(w / "EXCLUDED_SECOND.json") == LIST_BASE["campaign_list_sha256"]
            if bl["exit"] != 0 or not obs["rebuilt_list_equal"]:
                return False, dict(obs, list_block=bl)
        ann = {"DRAW_REHEARSAL1.json": str(w / "ANNOUNCE_R1.txt"), "DRAW_REHEARSAL.json": str(w / "ANNOUNCE_R2.txt")}
        r = run_block(w, "check-rehearsal2-list" if which == "rehearsal" else "check-list", ann)
        obs.update(r, shim_lines=[x for x in r["stderr"].splitlines() if x.startswith("shim:")])
        key = ("blocks", which)
        if kind is None:
            LIST_CONTROL[key] = ok = r["exit"] == 0 and LIST_RIGHT in r["stdout"] and bool(obs["shim_lines"])
            return ok, obs
        obs["control_passed"] = LIST_CONTROL.get(key, False)
        if kind == "no_scan":         # the block reads the scan: refused, naming the file
            own = r["exit"] != 0 and LIST_RIGHT not in r["stdout"] and "EXCLUDED_SECOND_SCAN.json" in r["stdout"] + r["stderr"]
        else:                         # the block's own verdict, after both draws checked
            own = r["exit"] != 0 and LIST_WRONG in r["stdout"] and "Traceback" not in r["stderr"]
        obs["reached_own_check"] = own
        return own and obs["control_passed"], obs
    case.__name__ = f"case_list_blocks_{which}_{kind}"
    return case


LIST_CONTROL = {}
LIST_MESSAGES = {}


def list_funcs_case(which, kind):
    """The same mutations through analysis.py's check_draw and check_rehearsal_seeds in rehearsal mode (which
    "rehearsal": draw= rehearsal 2, excluded= its list) or campaign mode (draw= the campaign stand-in, excluded= its
    list, second_scan= the scan; rehearsal_* and rehearsal1_* the two rehearsals)."""
    def case(tmp, src):
        w, name, note = list_case_files(tmp, which, kind)
        obs = dict(list=name, mutation=kind, changed=note)
        eb = (w / name).read_bytes()
        if which == "rehearsal":
            D, p, t0 = announced_draw(w, "CASE", ROUND_R2, json.loads(eb), eb, REHEARSAL_SIZES, "rehearsal",
                                      "evidence/combined-rehearsal2-draw")
            kw = dict(draw=str(p["draw"]), excluded=str(p["excluded"]), announce=str(p["announce"]))
        else:
            D, p, t0 = announced_draw(w, "CASE", ROUND_C, json.loads(eb), eb, CAMPAIGN_SIZES, "campaign",
                                      "evidence/combined-draw")
            kw = dict(draw=str(p["draw"]), excluded=str(p["excluded"]), announce=str(p["announce"]),
                      rehearsal_draw=str(w / "DRAW_REHEARSAL.json"),
                      rehearsal_excluded=str(w / "EXCLUDED_REHEARSAL2.json"),
                      rehearsal_announce=str(w / "ANNOUNCE_R2.txt"))
            kw[SECOND_SCAN_ARG] = str(w / "EXCLUDED_SECOND_SCAN.json")
            if kind == "no_scan":
                del kw[SECOND_SCAN_ARG]
            elif kind == "scan_short":
                import draw_seeds as DS
                scan = json.loads((w / "EXCLUDED_SECOND_SCAN.json").read_bytes())
                obs["changed"] = drop = LIST_BASE["rs1"][0]        # pinned, and drawn by rehearsal 1
                (w / "SCAN_SHORT.json").write_bytes(DS.canon(regen(scan, [s for s in scan["seeds"] if s != drop])))
                kw[SECOND_SCAN_ARG] = str(w / "SCAN_SHORT.json")
        kw.update(rehearsal1_draw=str(w / "DRAW_REHEARSAL1.json"), rehearsal1_excluded=str(w / "EXCLUDED_REHEARSAL1.json"),
                  rehearsal1_announce=str(w / "ANNOUNCE_R1.txt"))
        res = run_funcs(kw, which)
        obs.update(res, mode=which, args=sorted(kw))
        msg = res.get("message") or ""
        key = ("funcs", which)
        if kind is None:
            LIST_CONTROL[key] = ok = res.get("reached") == "accepted"
            return ok, obs
        obs["control_passed"] = LIST_CONTROL.get(key, False)
        old = any(o in msg for o in OLD_INCLUSION)
        if which == "rehearsal" and kind == "drop_scan":       # a pinned seed missing: check_draw's superset check
            own = res.get("raised_in") == "check_draw" and "is not a superset of the freeze's EXCLUDED.json" in msg
        elif kind == "drop_noise":   # the exactness check, or the inclusion check naming the seed
            own = res.get("raised_in") == "check_rehearsal_seeds" and (not old or str(note) in msg)
        elif kind in ("no_scan", "scan_short"):
            own = res.get("raised_in") == "check_rehearsal_seeds" and SECOND_SCAN_ARG in msg and not old
        else:                        # extra, field, drop_scan (campaign): the exactness check
            own = res.get("raised_in") == "check_rehearsal_seeds" and not old
        LIST_MESSAGES[(which, kind)] = msg
        if kind == "scan_short":     # its own check: not the one refusing an absent second_scan=
            own = own and msg != LIST_MESSAGES.get(("campaign", "no_scan"))
        if kind in ("no_scan", "scan_short"):     # nor the exactness check
            own = own and msg != LIST_MESSAGES.get(("campaign", "extra"))
        obs["reached_own_check"] = own
        return own and obs["control_passed"], obs
    case.__name__ = f"case_list_funcs_{which}_{kind}"
    return case


LIST_KINDS = {
    None: "the exact list (control): accepted",
    "extra": "one extra integer, count and seeds_sha256 recomputed: refused",
    "drop_noise": "one noise seed 10 S + j (not in the pinned list) removed, count and sha recomputed: refused",
    "drop_scan": "one scan seed removed, count and sha recomputed: refused",
    "field": "the \"added\" field's draw sha256 changed (a non-seed field): refused",
    "no_scan": "no EXCLUDED_SECOND_SCAN.json / no second_scan=: refused",
    "scan_short": "the scan without one pinned seed (one rehearsal 1 drew, so the rebuilt list is byte-equal): refused",
}
LIST_CASES = [(f"list_{side}_{which}_{kind or 'exact'}", which, kind, side)
              for side in ("blocks", "funcs") for which in ("rehearsal", "campaign")
              for kind in LIST_KINDS if which == "campaign" or kind not in ("no_scan", "scan_short")]


