import hashlib, json, sys, tempfile, copy, shutil
L = "/home/user/review_clone/research/layered-networks"; F = "a5ba132bc59e64b4eb6adcc01d107177d5fbe22b"
sys.path.insert(0, L)
import analysis as A, draw_seeds as D
W = sys.argv[1]; p = lambda n: f"{W}/{n}"
res = {}
def run(name, f):
    try: f(); res[name] = "ACCEPTED"
    except A.Refused as e: res[name] = "refused: " + str(e)[:170]
    except Exception as e: res[name] = f"EXCEPTION {type(e).__name__}: {str(e)[:120]}"
now = "2099-01-01T00:00:00Z"
# ---- rehearsal mode, strict, real rehearsal 1 from GitHub
base = dict(rehearsal1_draw=p('DRAW_REHEARSAL1.json'), rehearsal1_excluded=p('EXCLUDED_REHEARSAL1.json'))
run("reh_exact", lambda: A.check_rehearsal_seeds(dict(base, excluded=p('EXCLUDED_REHEARSAL2.json')), dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), F, True, 'rehearsal'))
w = json.load(open(p('EXCLUDED_REHEARSAL2.json')))
g = copy.deepcopy(w); g['seeds'] = sorted(g['seeds'] + [77777777]); g['count'] = len(g['seeds']); g['seeds_sha256'] = hashlib.sha256(D.canon(g['seeds'])).hexdigest()
open(p('R2_extra.json'), 'wb').write(D.canon(g))
run("reh_extra_seed", lambda: A.check_rehearsal_seeds(dict(base, excluded=p('R2_extra.json')), dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), F, True, 'rehearsal'))
run("reh_second_scan_given", lambda: A.check_rehearsal_seeds(dict(base, excluded=p('EXCLUDED_REHEARSAL2.json'), second_scan=p('EXCLUDED_SECOND_SCAN.json')), dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), F, True, 'rehearsal'))
run("reh_freeze_list_only", lambda: A.check_rehearsal_seeds(dict(base, excluded=L + '/EXCLUDED.json'), dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), F, True, 'rehearsal'))
# ---- campaign mode: rehearsal 2 does not exist; stand-in = rehearsal 1's verified draw, copied as DRAW_R2.json
shutil.copy(p('DRAW_REHEARSAL1.json'), p('DRAW_R2.json'))
orig = A.check_draw
cache = {}
def fake(rkw, mode, outdir, tree_commit=None, offline=None, past=None):
    if rkw['draw'] == p('DRAW_R2.json'):
        if 'r1' not in cache: cache['r1'] = orig(dict(draw=p('DRAW_REHEARSAL1.json'), excluded=p('EXCLUDED_REHEARSAL1.json')), 'rehearsal', outdir, tree_commit, past=A.REHEARSAL1)
        return cache['r1']
    return orig(rkw, mode, outdir, tree_commit, offline, past)
A.check_draw = fake
scan = json.load(open(p('EXCLUDED_SECOND_SCAN.json'))); sb = open(p('EXCLUDED_SECOND_SCAN.json'), 'rb').read()
r1 = cache.get('r1') or fake(dict(draw=p('DRAW_R2.json')), 'rehearsal', tempfile.mkdtemp())
rb1 = open(p('DRAW_REHEARSAL1.json'), 'rb').read()
open(p('CAMP_exact.json'), 'wb').write(A.campaign_list(scan, r1[0], rb1, r1[0], rb1))
ck = dict(rehearsal_draw=p('DRAW_R2.json'), rehearsal_excluded=p('EXCLUDED_REHEARSAL2.json'), rehearsal1_draw=p('DRAW_REHEARSAL1.json'), rehearsal1_excluded=p('EXCLUDED_REHEARSAL1.json'))
HS = hashlib.sha256(sb).hexdigest()
ann = lambda named: dict(announce=dict(push_utc=now, **({A.ANNOUNCE_SCAN_KEY: named} if named else {})))
C = lambda kw, d: (lambda: A.check_rehearsal_seeds(kw, d, tempfile.mkdtemp(), F, True, 'campaign'))
run("camp_exact_named_ok", C(dict(ck, excluded=p('CAMP_exact.json'), second_scan=p('EXCLUDED_SECOND_SCAN.json')), ann(HS)))
run("camp_exact_named_none", C(dict(ck, excluded=p('CAMP_exact.json'), second_scan=p('EXCLUDED_SECOND_SCAN.json')), ann(None)))
run("camp_no_second_scan", C(dict(ck, excluded=p('CAMP_exact.json')), ann(HS)))
run("camp_named_mismatch", C(dict(ck, excluded=p('CAMP_exact.json'), second_scan=p('EXCLUDED_SECOND_SCAN.json')), ann("0"*64)))
s2 = dict(scan, seeds=scan['seeds'][1:]); open(p('SCAN_notsuper.json'), 'wb').write(D.canon(s2))
run("camp_scan_not_superset", C(dict(ck, excluded=p('CAMP_exact.json'), second_scan=p('SCAN_notsuper.json')), ann(None)))
w = json.load(open(p('CAMP_exact.json'))); g = copy.deepcopy(w); g['seeds'] = sorted(g['seeds'] + [88888888]); g['count'] += 1; g['seeds_sha256'] = hashlib.sha256(D.canon(g['seeds'])).hexdigest()
open(p('CAMP_extra.json'), 'wb').write(D.canon(g))
run("camp_extra_seed", C(dict(ck, excluded=p('CAMP_extra.json'), second_scan=p('EXCLUDED_SECOND_SCAN.json')), ann(HS)))
run("camp_freeze_list_as_scan_and_list", C(dict(ck, excluded=p('CAMP_exact.json'), second_scan=L + '/EXCLUDED.json'), ann(None)))
# residual: a FABRICATED scan (real scan + extra seeds, fields untouched otherwise) and the list built from it
fab = dict(scan, seeds=sorted(scan['seeds'] + [55555, 55556, 55557])); fb = D.canon(fab); open(p('SCAN_fab.json'), 'wb').write(fb)
open(p('CAMP_fab.json'), 'wb').write(A.campaign_list(fab, r1[0], rb1, r1[0], rb1))
run("camp_fabricated_scan_named_its_own_sha", C(dict(ck, excluded=p('CAMP_fab.json'), second_scan=p('SCAN_fab.json')), ann(hashlib.sha256(fb).hexdigest())))
fab2 = dict(scan, seeds=sorted(scan['seeds'] + [55555])); open(p('SCAN_fab2.json'), 'wb').write(json.dumps(fab2).encode())  # count/seeds_sha256 now stale, not canon
open(p('CAMP_fab2.json'), 'wb').write(A.campaign_list(fab2, r1[0], rb1, r1[0], rb1))
run("camp_scan_inconsistent_count_sha_noncanon", C(dict(ck, excluded=p('CAMP_fab2.json'), second_scan=p('SCAN_fab2.json')), ann(None)))
run("camp_scan_file_missing", C(dict(ck, excluded=p('CAMP_exact.json'), second_scan=p('NOPE.json')), ann(None)))
print(json.dumps(res, indent=1))
