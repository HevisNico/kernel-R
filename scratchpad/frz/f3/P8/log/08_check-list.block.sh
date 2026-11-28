python -B -c "if True:
    import datetime, hashlib, json, sys, tempfile; sys.path.insert(0, '$L'); import analysis as A, draw_seeds as D
    x = json.load(open('EXCLUDED_SECOND.json')); frz = json.load(open('$L/EXCLUDED.json')); have = set(x['seeds'])
    r, info, _ = A.check_draw(dict(draw='DRAW_REHEARSAL.json', excluded='EXCLUDED_REHEARSAL2.json', announce='announce_rehearsal/DRAW_ANNOUNCE.txt'), 'rehearsal', tempfile.mkdtemp(), '$F', offline=True)
    r1, info1, _ = A.check_draw(dict(draw='DRAW_REHEARSAL1.json', excluded='EXCLUDED_REHEARSAL1.json'), 'rehearsal', tempfile.mkdtemp(), '$F', past=A.REHEARSAL1)
    rs = sorted({s for d in (r, r1) for v in d['groups'].values() for s in v}); noise = [10 * s + n for s in rs for n in range(4)]
    now = datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
    A.check_rehearsal_seeds(dict(rehearsal_draw='DRAW_REHEARSAL.json', rehearsal_excluded='EXCLUDED_REHEARSAL2.json', rehearsal_announce='announce_rehearsal/DRAW_ANNOUNCE.txt', rehearsal1_announce='/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/REHEARSAL1_DRAW_ANNOUNCE.txt',
    rehearsal1_draw='DRAW_REHEARSAL1.json', rehearsal1_excluded='EXCLUDED_REHEARSAL1.json', excluded='EXCLUDED_SECOND.json'),
    dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', False, 'campaign')
    ok = (len(rs) == 36 and len(noise) == 144 and set(rs + noise) <= have and set(frz['seeds']) <= have
    and x['count'] == len(x['seeds']) == len(have) and x['seeds'] == sorted(have)
    and hashlib.sha256(D.canon(x['seeds'])).hexdigest() == x['seeds_sha256']
    and D.excluded_fraction(x) <= D.MAX_EXCLUDED_FRACTION)
    print('the list is right' if ok else 'THE LIST IS WRONG: rebuild it, push nothing', len(rs), len(noise),
    'sha256', hashlib.sha256(open('EXCLUDED_SECOND.json', 'rb').read()).hexdigest()); sys.exit(0 if ok else 1)"
