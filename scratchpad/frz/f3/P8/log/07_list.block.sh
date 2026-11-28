python -B -c "if True:
    import hashlib, json, sys; sys.path.insert(0, '$L'); import draw_seeds as D
    scan = json.load(open('EXCLUDED_SECOND_SCAN.json'))
    rb, rb1 = open('DRAW_REHEARSAL.json', 'rb').read(), open('DRAW_REHEARSAL1.json', 'rb').read()
    rs = sorted({s for b in (rb, rb1) for v in json.loads(b)['groups'].values() for s in v})
    noise = sorted(10 * s + n for s in rs for n in range(4))
    seeds = sorted(set(scan['seeds']) | set(rs) | set(noise))
    out = dict(scan, seeds=seeds, count=len(seeds), seeds_sha256=hashlib.sha256(D.canon(seeds)).hexdigest(),
    added=dict(rehearsal_seeds=rs, noise_seeds=noise, rehearsal_draw_sha256=hashlib.sha256(rb).hexdigest(),
    rehearsal1_draw_sha256=hashlib.sha256(rb1).hexdigest()))
    open('EXCLUDED_SECOND.json', 'wb').write(D.canon(out))
    print(len(rs), 'rehearsal seeds,', len(noise), 'noise seeds;', out['count'], 'integers, seeds_sha256', out['seeds_sha256'])"
