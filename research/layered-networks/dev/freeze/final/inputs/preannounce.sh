cp $X EXCLUDED_PUBLISHED.json                                           # the list the draw uses, published with it
printf 'format layered-draw-announce/1\nmode %s\nexcluded_sha256 %s\nsizes %s\n' $M \
  "$(sha256sum EXCLUDED_PUBLISHED.json | cut -c1-64)" "$Z" > DRAW_ANNOUNCE.txt
python -B -c "if True:
    import hashlib, json, sys; sys.path.insert(0, '$TREE/research/layered-networks');
    import analysis as A, draw_seeds as D;
    a = A.parse_announce(open('DRAW_ANNOUNCE.txt', 'rb').read()); x = json.load(open('EXCLUDED_PUBLISHED.json'));
    want = A.DRAW_SIZES if '$M' == 'campaign' else A.DRAW_SIZES_REHEARSAL;
    frz = json.load(open('$TREE/research/layered-networks/EXCLUDED.json'));
    ok = (a['mode'] == '$M' and a['sizes'] == want and set(frz['seeds']) <= set(x['seeds']) and
    a['excluded_sha256'] == hashlib.sha256(open('EXCLUDED_PUBLISHED.json', 'rb').read()).hexdigest() and
    D.excluded_fraction(x) <= D.MAX_EXCLUDED_FRACTION);
    print('announce ok' if ok else 'ANNOUNCE WRONG: do not push'); sys.exit(0 if ok else 1)"
