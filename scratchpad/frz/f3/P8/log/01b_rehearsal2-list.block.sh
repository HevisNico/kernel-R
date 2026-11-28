python -B -c "if True:
    import hashlib, json, sys; sys.path.insert(0, '$L'); import draw_seeds as D
    frz = json.load(open('$L/EXCLUDED.json')); rb1 = open('DRAW_REHEARSAL1.json', 'rb').read()
    rs = sorted(s for v in json.loads(rb1)['groups'].values() for s in v)
    noise = sorted(10 * s + n for s in rs for n in range(4))
    seeds = sorted(set(frz['seeds']) | set(rs) | set(noise))
    out = dict(frz, seeds=seeds, count=len(seeds), seeds_sha256=hashlib.sha256(D.canon(seeds)).hexdigest(),
    added=dict(rehearsal1_seeds=rs, noise_seeds=noise, rehearsal1_draw_sha256=hashlib.sha256(rb1).hexdigest()))
    open('EXCLUDED_REHEARSAL2.json', 'wb').write(D.canon(out))
    print(len(rs), 'rehearsal seeds,', len(noise), 'noise seeds;', out['count'], 'integers, seeds_sha256', out['seeds_sha256'])"
