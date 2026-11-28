import hashlib, json, sys, copy
L = "/home/user/review_clone/research/layered-networks"; sys.path.insert(0, L)
import analysis as A, draw_seeds as D
RW = "/home/user/rescan_work"
sb = open(f"{RW}/EXCLUDED_SECOND_SCAN.json", "rb").read(); scan = json.loads(sb)
ls = open(f"{RW}/SCAN_LSREMOTE.txt").read()
res = {}
def cs(name, b):
    try: A.check_scan(b, "S"); res[name] = "ACCEPTED"
    except A.Refused as e: res[name] = "refused: " + str(e)[:150]
    except Exception as e: res[name] = f"EXCEPTION {type(e).__name__}: {e}"[:150]
def mut(f):
    s = copy.deepcopy(scan); f(s); return s
cs("real_scan", sb)
cs("noncanon_indent", json.dumps(scan, indent=1).encode())
cs("extra_seed_stale_count", D.canon(mut(lambda s: s.__setitem__("seeds", sorted(s["seeds"] + [55555])))))
def fab(s):
    s["seeds"] = sorted(s["seeds"] + [55555, 55556]); s["count"] = len(s["seeds"]); s["seeds_sha256"] = hashlib.sha256(D.canon(s["seeds"])).hexdigest()
cs("fabricated_selfconsistent_extra_seeds", D.canon(mut(fab)))
cs("format_changed", D.canon(mut(lambda s: s.__setitem__("format", "x"))))
cs("rule_changed", D.canon(mut(lambda s: s.__setitem__("rule", s["rule"] + "."))))
cs("unsorted", D.canon(mut(lambda s: s.__setitem__("seeds", s["seeds"][::-1]))))
cs("bool_seed", D.canon(mut(lambda s: s["seeds"].__setitem__(0, True))))
cs("head_missing", D.canon(mut(lambda s: s["refs"].pop("HEAD"))))
cs("head_not_main", D.canon(mut(lambda s: s["refs"]["HEAD"].__setitem__("tip", "0" * 40))))
cs("ref_bad_prefix", D.canon(mut(lambda s: s["refs"].__setitem__("refs/heads/x", {"tip": "a" * 40, "numbers": 1}))))
cs("ref_removed", D.canon(mut(lambda s: s["refs"].pop(sorted(k for k in s["refs"] if k != "HEAD" and "numbers" in s["refs"][k] and not k.endswith("/main"))[0]))))
cs("dup_key_raw", sb.replace(b'"count":', b'"count":1,"count":', 1))
cs("not_json", b"{")
cs("empty", b"")
# verify_scan
def vs(name, sv, sr, l):
    p = A.verify_scan(sv, sr, l); res[name] = p if p else "NO PROBLEMS"
vs("verify_real_vs_itself_with_scan_lsremote", sb, sb, ls)
lines = ls.splitlines()
vs("verify_lsremote_extra_branch", sb, sb, ls + "a" * 40 + "\trefs/heads/new-branch\n")
vs("verify_lsremote_missing_branch", sb, sb, "\n".join(lines[1:]) + "\n")
t, r = lines[1].split(); vs("verify_lsremote_moved_tip", sb, sb, "\n".join([lines[0], "b" * 40 + "\t" + r] + lines[2:]) + "\n")
vs("verify_reproduction_differs", sb, sb + b" ", ls)
vs("verify_fabricated_scan_vs_real_repro", D.canon(mut(fab)), sb, ls)
# parse_announce
def pa(name, txt):
    try: res[name] = A.parse_announce(txt.encode())
    except A.Refused as e: res[name] = "refused: " + str(e)[:140]
H = "a" * 64
pa("ann_v1_rehearsal", f"format layered-draw-announce/1\nmode rehearsal\nexcluded_sha256 {H}\nsizes NOT1=6 ANDOR3=6 XOR3=6\n")
pa("ann_v1_campaign", f"format layered-draw-announce/1\nmode campaign\nexcluded_sha256 {H}\nsizes NOT1=60 ANDOR3=32 XOR3=37\n")
pa("ann_v2_campaign", f"format layered-draw-announce/2\nmode campaign\nexcluded_sha256 {H}\nsecond_scan_sha256 {H}\nsizes NOT1=60 ANDOR3=32 XOR3=37\n")
pa("ann_v2_campaign_no_scan", f"format layered-draw-announce/2\nmode campaign\nexcluded_sha256 {H}\nsizes NOT1=60 ANDOR3=32 XOR3=37\n")
pa("ann_v2_rehearsal", f"format layered-draw-announce/2\nmode rehearsal\nexcluded_sha256 {H}\nsecond_scan_sha256 {H}\nsizes NOT1=6 ANDOR3=6 XOR3=6\n")
pa("ann_v1_with_scan", f"format layered-draw-announce/1\nmode rehearsal\nexcluded_sha256 {H}\nsecond_scan_sha256 {H}\nsizes NOT1=6 ANDOR3=6 XOR3=6\n")
pa("ann_dup_line", f"format layered-draw-announce/2\nmode campaign\nexcluded_sha256 {H}\nsecond_scan_sha256 {H}\nsecond_scan_sha256 {H}\nsizes NOT1=60 ANDOR3=32 XOR3=37\n")
pa("ann_crlf", f"format layered-draw-announce/2\r\nmode campaign\r\nexcluded_sha256 {H}\r\nsecond_scan_sha256 {H}\r\nsizes NOT1=60 ANDOR3=32 XOR3=37\r\n")
pa("ann_scan_sha_not_hex", f"format layered-draw-announce/2\nmode campaign\nexcluded_sha256 {H}\nsecond_scan_sha256 zz\nsizes NOT1=60 ANDOR3=32 XOR3=37\n")
# check_announce_files
lb = b'{"seeds":[1]}'
def caf(name, at, Ad, kw, mode):
    try: A.check_announce_files(at, Ad, kw, mode); res[name] = "ACCEPTED"
    except A.Refused as e: res[name] = "refused: " + str(e)[:140]
    except Exception as e: res[name] = f"EXCEPTION {type(e).__name__}: {e}"[:140]
open("/home/user/review_work/l.json", "wb").write(lb); open("/home/user/review_work/s.json", "wb").write(sb)
hl, hs = hashlib.sha256(lb).hexdigest(), hashlib.sha256(sb).hexdigest()
ok_at = {"EXCLUDED_PUBLISHED.json": lb, "EXCLUDED_SECOND_SCAN.json": sb}
Ad = dict(excluded_sha256=hl, second_scan_sha256=hs)
kwf = dict(excluded="/home/user/review_work/l.json", second_scan="/home/user/review_work/s.json")
caf("caf_ok", ok_at, Ad, kwf, "campaign")
caf("caf_scan_absent", {"EXCLUDED_PUBLISHED.json": lb, "EXCLUDED_SECOND_SCAN.json": None}, Ad, kwf, "campaign")
caf("caf_scan_other_bytes", {"EXCLUDED_PUBLISHED.json": lb, "EXCLUDED_SECOND_SCAN.json": sb + b"x"}, Ad, kwf, "campaign")
caf("caf_kw_scan_differs_but_announce_ok", ok_at, Ad, dict(kwf, second_scan="/home/user/review_work/l.json"), "campaign")
caf("caf_kw_no_second_scan", ok_at, Ad, dict(excluded=kwf["excluded"]), "campaign")
caf("caf_rehearsal_ignores_scan", {"EXCLUDED_PUBLISHED.json": lb}, dict(excluded_sha256=hl), dict(excluded=kwf["excluded"]), "rehearsal")
caf("caf_kw_missing_file", ok_at, Ad, dict(kwf, excluded="/nope"), "campaign")
print(json.dumps(res, indent=1, default=str)[:9000])
