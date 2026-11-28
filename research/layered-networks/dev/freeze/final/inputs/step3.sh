python -B -c "if True:
    import datetime, hashlib, json, sys, tempfile; sys.path.insert(0, '$L'); import analysis as A, draw_seeds as D
    x = json.load(open('EXCLUDED_SECOND.json')); frz = json.load(open('$L/EXCLUDED.json')); have = set(x['seeds'])
    r, info, _ = A.check_draw(dict(draw='DRAW_REHEARSAL.json', excluded='$L/EXCLUDED.json'), 'rehearsal', tempfile.mkdtemp(), '$F')
    rs = sorted(s for v in r['groups'].values() for s in v); noise = [10 * s + n for s in rs for n in range(4)]
    now = datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
    A.check_rehearsal_seeds(dict(rehearsal_draw='DRAW_REHEARSAL.json', excluded='EXCLUDED_SECOND.json'),
    dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', True)
    ok = (len(rs) == 18 and len(noise) == 72 and set(rs + noise) <= have and set(frz['seeds']) <= have
    and x['count'] == len(x['seeds']) == len(have) and x['seeds'] == sorted(have)
    and hashlib.sha256(D.canon(x['seeds'])).hexdigest() == x['seeds_sha256']
    and D.excluded_fraction(x) <= D.MAX_EXCLUDED_FRACTION)
    print('the list is right' if ok else 'THE LIST IS WRONG: rebuild it, push nothing', len(rs), len(noise),
    'sha256', hashlib.sha256(open('EXCLUDED_SECOND.json', 'rb').read()).hexdigest()); sys.exit(0 if ok else 1)"
