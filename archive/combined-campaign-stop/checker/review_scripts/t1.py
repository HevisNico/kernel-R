import hashlib, json, sys, tempfile, copy
L = "/home/user/review_clone/research/layered-networks"; F = "a5ba132bc59e64b4eb6adcc01d107177d5fbe22b"
sys.path.insert(0, L)
import analysis as A, draw_seeds as D
W = sys.argv[1]
def p(n): return f"{W}/{n}"
res = {}
r1, info1, _ = A.check_draw(dict(draw=p('DRAW_REHEARSAL1.json'), excluded=p('EXCLUDED_REHEARSAL1.json')), 'rehearsal', tempfile.mkdtemp(), F, past=A.REHEARSAL1)
rb1 = open(p('DRAW_REHEARSAL1.json'), 'rb').read()
res['r1_verified'] = dict(seeds=len(A.draw_seeds_of(r1)), file_is_canon_of_recomputed=(D.canon(json.loads(rb1)['groups']) == D.canon(r1['groups'])))
frz = json.load(open(f"{L}/EXCLUDED.json"))
# [block rehearsal2-list] verbatim logic (r2), from the raw file
rs = sorted(s for v in json.loads(rb1)['groups'].values() for s in v)
noise = sorted(10 * s + n for s in rs for n in range(4))
seeds = sorted(set(frz['seeds']) | set(rs) | set(noise))
out = dict(frz, seeds=seeds, count=len(seeds), seeds_sha256=hashlib.sha256(D.canon(seeds)).hexdigest(),
    added=dict(rehearsal1_seeds=rs, noise_seeds=noise, rehearsal1_draw_sha256=hashlib.sha256(rb1).hexdigest()))
blk_r2 = D.canon(out)
fn_r2 = A.rehearsal2_list(frz, r1, rb1)
res['rehearsal2_list_eq_block_r2'] = blk_r2 == fn_r2
res['rehearsal2_list_sha'] = hashlib.sha256(fn_r2).hexdigest()
open(p('EXCLUDED_REHEARSAL2.json'), 'wb').write(blk_r2)
# [block list] logic with r1 standing in for rehearsal 2 (no rehearsal 2 exists yet)
scan = json.load(open(p('EXCLUDED_SECOND_SCAN.json'))); rb = rb1; r = r1
rs2 = sorted({s for d in (json.loads(rb), json.loads(rb1)) for v in d['groups'].values() for s in v})
noise2 = sorted(10 * s + n for s in rs2 for n in range(4))
seeds2 = sorted(set(scan['seeds']) | set(rs2) | set(noise2))
blk_list = D.canon(dict(scan, seeds=seeds2, count=len(seeds2), seeds_sha256=hashlib.sha256(D.canon(seeds2)).hexdigest(),
    added=dict(rehearsal_seeds=rs2, noise_seeds=noise2, rehearsal_draw_sha256=hashlib.sha256(rb).hexdigest(),
    rehearsal1_draw_sha256=hashlib.sha256(rb1).hexdigest())))
fn_list = A.campaign_list(scan, r, rb, r1, rb1)
res['campaign_list_eq_block_list(standin)'] = blk_list == fn_list
# check_exact_list cases
def tryit(name, b, want, whose="X", of="Y"):
    f = p(f"case_{name}.json"); open(f, 'wb').write(b)
    try:
        A.check_exact_list(f, want, whose, of); res[name] = "ACCEPTED"
    except A.Refused as e:
        res[name] = "refused: " + str(e)[:160]
want = fn_r2; w = json.loads(want)
tryit("exact", want, want)
g = copy.deepcopy(w); extra = 99999999; g['seeds'] = sorted(g['seeds'] + [extra]); g['count'] = len(g['seeds']); g['seeds_sha256'] = hashlib.sha256(D.canon(g['seeds'])).hexdigest()
tryit("extra_seed_recomputed", D.canon(g), want)
g = copy.deepcopy(w); g['seeds'] = g['seeds'][1:]; g['count'] -= 1; g['seeds_sha256'] = hashlib.sha256(D.canon(g['seeds'])).hexdigest()
tryit("missing_seed_recomputed", D.canon(g), want)
g = copy.deepcopy(w); g['rule'] = g['rule'] + " "; tryit("other_field", D.canon(g), want)
g = copy.deepcopy(w); g['extra_key'] = 1; tryit("extra_key", D.canon(g), want)
tryit("reserialized", json.dumps(w, indent=1).encode(), want)
tryit("trailing_newline_removed", want.rstrip(b"\n"), want)
tryit("not_json", b"xx", want)
g = copy.deepcopy(w); g['seeds'] = [True] + g['seeds'][1:]; tryit("bool_seed", json.dumps(g).encode(), want)
g = copy.deepcopy(w); g['seeds'] = sorted(g['seeds'] + [g['seeds'][5]]); tryit("duplicate_seed", D.canon(g), want)
tryit("json_list_not_dict", b"[1,2]", want)
print(json.dumps(res, indent=1))
