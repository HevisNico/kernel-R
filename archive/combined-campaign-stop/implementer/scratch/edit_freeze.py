from pathlib import Path
p = Path("FREEZE.txt"); t = p.read_text()
def rep(a, b):
    global t
    assert t.count(a) == 1, a[:70]
    t = t.replace(a, b)
# analysis command lines
rep("""  python -B analysis.py campaign  OUTDIR ROOT ... draw=DRAW.json excluded=EXCLUDED_SECOND.json
                                   rehearsal_draw=DRAW_REHEARSAL.json rehearsal_excluded=EXCLUDED_REHEARSAL2.json
                                   rehearsal1_draw=DRAW_REHEARSAL1.json rehearsal1_excluded=EXCLUDED_REHEARSAL1.json
     (draw= is the DRAW.json of evidence/combined-draw-result; rehearsal_draw= that of rehearsal 2,
     evidence/combined-rehearsal2-draw-result; rehearsal1_draw= and rehearsal1_excluded= rehearsal 1's published files:
     the DRAW.json of evidence/combined-rehearsal-draw-result at f74b75fb and the EXCLUDED_PUBLISHED.json of its
     announce, evidence/combined-rehearsal-draw; ORDER 3 block rehearsal-draw fetches all three)
  python -B analysis.py rehearsal OUTDIR ROOT ... draw=DRAW_REHEARSAL.json excluded=EXCLUDED_REHEARSAL2.json
                                   rehearsal1_draw=DRAW_REHEARSAL1.json rehearsal1_excluded=EXCLUDED_REHEARSAL1.json
     (rehearsal 2; its list is the freeze's EXCLUDED.json plus rehearsal 1's seeds, ORDER 2)
""", """  python -B analysis.py campaign  OUTDIR ROOT ... draw=DRAW.json excluded=EXCLUDED_SECOND.json
                                   second_scan=EXCLUDED_SECOND_SCAN.json
                                   rehearsal_draw=DRAW_REHEARSAL.json rehearsal_excluded=EXCLUDED_REHEARSAL2.json
                                   rehearsal1_draw=DRAW_REHEARSAL1.json rehearsal1_excluded=EXCLUDED_REHEARSAL1.json
     (draw= is the DRAW.json of evidence/combined-draw-result; excluded= and second_scan= the EXCLUDED_PUBLISHED.json
     and EXCLUDED_SECOND_SCAN.json of its announce, evidence/combined-draw; rehearsal_draw= that of rehearsal 2,
     evidence/combined-rehearsal2-draw-result; rehearsal1_draw= and rehearsal1_excluded= rehearsal 1's published files:
     the DRAW.json of evidence/combined-rehearsal-draw-result at f74b75fb and the EXCLUDED_PUBLISHED.json of its
     announce, evidence/combined-rehearsal-draw; ORDER 3 block rehearsal-draw fetches all three. excluded= must be
     byte for byte the exact union [block list] builds from second_scan= and the two verified rehearsal draws)
  python -B analysis.py rehearsal OUTDIR ROOT ... draw=DRAW_REHEARSAL.json excluded=EXCLUDED_REHEARSAL2.json
                                   rehearsal1_draw=DRAW_REHEARSAL1.json rehearsal1_excluded=EXCLUDED_REHEARSAL1.json
     (rehearsal 2; its list is the freeze's EXCLUDED.json plus rehearsal 1's seeds, ORDER 2, byte for byte the exact
     union [block rehearsal2-list] builds from rehearsal 1's verified draw)
""")
rep("""    X=EXCLUDED_REHEARSAL2.json  SIZES="NOT1=6 ANDOR3=6 XOR3=6"
    H=<the 64 hex characters that ORDER 2 step (r3) printed after "sha256">
    [end]""", """    X=EXCLUDED_REHEARSAL2.json  SIZES="NOT1=6 ANDOR3=6 XOR3=6"
    H=<the 64 hex characters that ORDER 2 step (r3) printed after "sha256">
    S=  HS=
    [end]""")
rep("""    X=EXCLUDED_SECOND.json  SIZES="NOT1=60 ANDOR3=32 XOR3=37"
    H=<the 64 hex characters that ORDER 3 step (3) printed after "sha256">
    [end]
  (H is KEPT from step (3)'s printed line: the announce block publishes the list only if the copied file has that
  sha256.)""", """    X=EXCLUDED_SECOND.json  SIZES="NOT1=60 ANDOR3=32 XOR3=37"
    H=<the 64 hex characters that ORDER 3 step (3) printed after "sha256">
    S=EXCLUDED_SECOND_SCAN.json
    HS=<the 64 hex characters that ORDER 3 step (3) printed after "scan_sha256">
    [end]
  (H and HS are KEPT from step (3)'s printed line: the announce block publishes the list and the second scan's raw
  output only if the copied files have those sha256.)""")
# check-rehearsal2-list
rep("""       (r3) re-read the FINAL file and check it, BEFORE rehearsal 2's announce: rehearsal 1's draw verified in full
       against its own freeze (analysis.REHEARSAL1; its announce from GitHub), its 18 seeds and 72 noise seeds all in the
       file, the file's own count and seeds_sha256, the 20 % cap, the superset of the freeze's list:
    [block check-rehearsal2-list]
    python -B -c "if True:
        import hashlib, json, sys, tempfile; sys.path.insert(0, '$L'); import analysis as A, draw_seeds as D
        x = json.load(open('EXCLUDED_REHEARSAL2.json')); frz = json.load(open('$L/EXCLUDED.json')); have = set(x['seeds'])
        r1, info1, _ = A.check_draw(dict(draw='DRAW_REHEARSAL1.json', excluded='EXCLUDED_REHEARSAL1.json'), 'rehearsal', tempfile.mkdtemp(), '$F', past=A.REHEARSAL1)
        rs = sorted(s for v in r1['groups'].values() for s in v); noise = [10 * s + n for s in rs for n in range(4)]
        ok = (len(rs) == 18 and len(noise) == 72 and set(rs + noise) <= have and set(frz['seeds']) <= have
        and x['count'] == len(x['seeds']) == len(have) and x['seeds'] == sorted(have)
        and hashlib.sha256(D.canon(x['seeds'])).hexdigest() == x['seeds_sha256']
        and D.excluded_fraction(x) <= D.MAX_EXCLUDED_FRACTION)
        print('the list is right' if ok else 'THE LIST IS WRONG: rebuild it, push nothing', len(rs), len(noise),
        'sha256', hashlib.sha256(open('EXCLUDED_REHEARSAL2.json', 'rb').read()).hexdigest()); sys.exit(0 if ok else 1)"
    [end]""", """       (r3) re-read the FINAL file and check it, BEFORE rehearsal 2's announce: rehearsal 1's draw verified in full
       against its own freeze (analysis.REHEARSAL1; its announce from GitHub), its 18 seeds and 72 noise seeds; THE
       EXACT UNION: the list rebuilt here from the freeze's EXCLUDED.json and that VERIFIED draw, as (r2) builds it,
       must be the file byte for byte (an extra or a missing seed, or any other field, refuses, even with a recomputed
       count and seeds_sha256); analysis.check_rehearsal_seeds in rehearsal mode, which rebuilds it too
       (analysis.rehearsal2_list); the 20 % cap:
    [block check-rehearsal2-list]
    python -B -c "if True:
        import datetime, hashlib, json, sys, tempfile; sys.path.insert(0, '$L'); import analysis as A, draw_seeds as D
        xb = open('EXCLUDED_REHEARSAL2.json', 'rb').read(); x = json.loads(xb); frz = json.load(open('$L/EXCLUDED.json'))
        r1, info1, _ = A.check_draw(dict(draw='DRAW_REHEARSAL1.json', excluded='EXCLUDED_REHEARSAL1.json'), 'rehearsal', tempfile.mkdtemp(), '$F', past=A.REHEARSAL1)
        rb1 = open('DRAW_REHEARSAL1.json', 'rb').read()
        rs = sorted(s for v in r1['groups'].values() for s in v); noise = sorted(10 * s + n for s in rs for n in range(4))
        seeds = sorted(set(frz['seeds']) | set(rs) | set(noise))
        want = D.canon(dict(frz, seeds=seeds, count=len(seeds), seeds_sha256=hashlib.sha256(D.canon(seeds)).hexdigest(),
        added=dict(rehearsal1_seeds=rs, noise_seeds=noise, rehearsal1_draw_sha256=hashlib.sha256(rb1).hexdigest())))
        now = datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
        A.check_rehearsal_seeds(dict(rehearsal1_draw='DRAW_REHEARSAL1.json', rehearsal1_excluded='EXCLUDED_REHEARSAL1.json',
        excluded='EXCLUDED_REHEARSAL2.json'), dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', True, 'rehearsal')
        ok = (len(rs) == 18 and len(noise) == 72 and xb == want
        and D.excluded_fraction(x) <= D.MAX_EXCLUDED_FRACTION)
        print('the list is right' if ok else 'THE LIST IS WRONG: rebuild it, push nothing', len(rs), len(noise),
        'sha256', hashlib.sha256(xb).hexdigest()); sys.exit(0 if ok else 1)"
    [end]""")
# second scan bullets
rep("""     - It must contain every seed of the freeze's EXCLUDED.json (analysis.py refuses otherwise), and so the
       rehearsals' seeds, which their SEALS.txt lines name.""", """     - It must contain every seed of the freeze's EXCLUDED.json (the check (3) below and analysis.py, from
       second_scan=, refuse otherwise), and so the rehearsals' seeds, which their SEALS.txt lines name.""")
rep("""     - The scan output must be draw_seeds.py scan's, unedited, at the refs and tips it names, so that anyone can rerun
       the scan and get the same bytes.""", """     - The scan output must be draw_seeds.py scan's, unedited, at the refs and tips it names, so that anyone can rerun
       the scan and get the same bytes. It is PUBLIC: the campaign announce commit carries it as
       EXCLUDED_SECOND_SCAN.json, and DRAW_ANNOUNCE.txt names its sha256 (second_scan_sha256), so that anyone can
       rerun the exact-union check (analysis.py campaign, second_scan=).""")
# check-list
rep("""     (3) Re-read the FINAL file and check it, BEFORE the announce. It checks:
       - both rehearsal draws, verified in full (their announces and push times read from GitHub, their signatures,
         rounds and seeds at 6/6/6; rehearsal 1 against its own freeze, analysis.REHEARSAL1);
       - their 36 seeds and 144 noise seeds, all in the file;
       - the file's own count and seeds_sha256;
       - the 20 % cap;
       - the superset of the freeze's list;
       - analysis.check_rehearsal_seeds, with now as the campaign announce's earliest time.
    [block check-list]
    python -B -c "if True:
        import datetime, hashlib, json, sys, tempfile; sys.path.insert(0, '$L'); import analysis as A, draw_seeds as D
        x = json.load(open('EXCLUDED_SECOND.json')); frz = json.load(open('$L/EXCLUDED.json')); have = set(x['seeds'])
        r, info, _ = A.check_draw(dict(draw='DRAW_REHEARSAL.json', excluded='EXCLUDED_REHEARSAL2.json'), 'rehearsal', tempfile.mkdtemp(), '$F')
        r1, info1, _ = A.check_draw(dict(draw='DRAW_REHEARSAL1.json', excluded='EXCLUDED_REHEARSAL1.json'), 'rehearsal', tempfile.mkdtemp(), '$F', past=A.REHEARSAL1)
        rs = sorted({s for d in (r, r1) for v in d['groups'].values() for s in v}); noise = [10 * s + n for s in rs for n in range(4)]
        now = datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
        A.check_rehearsal_seeds(dict(rehearsal_draw='DRAW_REHEARSAL.json', rehearsal_excluded='EXCLUDED_REHEARSAL2.json',
        rehearsal1_draw='DRAW_REHEARSAL1.json', rehearsal1_excluded='EXCLUDED_REHEARSAL1.json', excluded='EXCLUDED_SECOND.json'),
        dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', True, 'campaign')
        ok = (len(rs) == 36 and len(noise) == 144 and set(rs + noise) <= have and set(frz['seeds']) <= have
        and x['count'] == len(x['seeds']) == len(have) and x['seeds'] == sorted(have)
        and hashlib.sha256(D.canon(x['seeds'])).hexdigest() == x['seeds_sha256']
        and D.excluded_fraction(x) <= D.MAX_EXCLUDED_FRACTION)
        print('the list is right' if ok else 'THE LIST IS WRONG: rebuild it, push nothing', len(rs), len(noise),
        'sha256', hashlib.sha256(open('EXCLUDED_SECOND.json', 'rb').read()).hexdigest()); sys.exit(0 if ok else 1)"
    [end]
     If (3) fails, the list is rebuilt from (1) and rechecked; nothing is pushed until (3) passes. The sha256 that (3)
     prints is KEPT as H (block vars-campaign). The announce block refuses, with no commit and no push, unless its
     copy of X has exactly that sha256. The published list is therefore the scan's output with the "added" field,
     which names what was added.""", """     (3) Re-read the FINAL file and check it, BEFORE the announce. It checks:
       - both rehearsal draws, verified in full (their announces and push times read from GitHub, their signatures,
         rounds and seeds at 6/6/6; rehearsal 1 against its own freeze, analysis.REHEARSAL1);
       - their 36 seeds and 144 noise seeds;
       - the second scan's raw output, EXCLUDED_SECOND_SCAN.json, re-read: a superset of the freeze's list;
       - THE EXACT UNION: the list rebuilt here from that scan and the two VERIFIED draws, as (1) builds it, must be
         the file byte for byte (an extra or a missing seed, or any other field, refuses, even with a recomputed count
         and seeds_sha256);
       - the 20 % cap;
       - analysis.check_rehearsal_seeds, with now as the campaign announce's earliest time and second_scan=, which
         rebuilds the exact union too (analysis.campaign_list).
    [block check-list]
    python -B -c "if True:
        import datetime, hashlib, json, sys, tempfile; sys.path.insert(0, '$L'); import analysis as A, draw_seeds as D
        xb = open('EXCLUDED_SECOND.json', 'rb').read(); x = json.loads(xb); frz = json.load(open('$L/EXCLUDED.json'))
        sb = open('EXCLUDED_SECOND_SCAN.json', 'rb').read(); scan = json.loads(sb)
        r, info, _ = A.check_draw(dict(draw='DRAW_REHEARSAL.json', excluded='EXCLUDED_REHEARSAL2.json'), 'rehearsal', tempfile.mkdtemp(), '$F')
        r1, info1, _ = A.check_draw(dict(draw='DRAW_REHEARSAL1.json', excluded='EXCLUDED_REHEARSAL1.json'), 'rehearsal', tempfile.mkdtemp(), '$F', past=A.REHEARSAL1)
        rb, rb1 = open('DRAW_REHEARSAL.json', 'rb').read(), open('DRAW_REHEARSAL1.json', 'rb').read()
        rs = sorted({s for d in (r, r1) for v in d['groups'].values() for s in v}); noise = sorted(10 * s + n for s in rs for n in range(4))
        seeds = sorted(set(scan['seeds']) | set(rs) | set(noise))
        want = D.canon(dict(scan, seeds=seeds, count=len(seeds), seeds_sha256=hashlib.sha256(D.canon(seeds)).hexdigest(),
        added=dict(rehearsal_seeds=rs, noise_seeds=noise, rehearsal_draw_sha256=hashlib.sha256(rb).hexdigest(),
        rehearsal1_draw_sha256=hashlib.sha256(rb1).hexdigest())))
        now = datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
        A.check_rehearsal_seeds(dict(rehearsal_draw='DRAW_REHEARSAL.json', rehearsal_excluded='EXCLUDED_REHEARSAL2.json',
        rehearsal1_draw='DRAW_REHEARSAL1.json', rehearsal1_excluded='EXCLUDED_REHEARSAL1.json', excluded='EXCLUDED_SECOND.json',
        second_scan='EXCLUDED_SECOND_SCAN.json'), dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', True, 'campaign')
        ok = (len(rs) == 36 and len(noise) == 144 and set(frz['seeds']) <= set(scan['seeds']) and xb == want
        and D.excluded_fraction(x) <= D.MAX_EXCLUDED_FRACTION)
        print('the list is right' if ok else 'THE LIST IS WRONG: rebuild it, push nothing', len(rs), len(noise),
        'sha256', hashlib.sha256(xb).hexdigest(), 'scan_sha256', hashlib.sha256(sb).hexdigest()); sys.exit(0 if ok else 1)"
    [end]
     If (3) fails, the list is rebuilt from (1) and rechecked; nothing is pushed until (3) passes. The two sha256 that
     (3) prints are KEPT as H and HS (block vars-campaign). The announce block refuses, with no commit and no push,
     unless its copies of X and S have exactly those sha256. The published list is therefore the scan's output with
     the "added" field, which names what was added, and the scan's output itself is published beside it.""")
rep("""     analysis.py campaign with rehearsal_draw=DRAW_REHEARSAL.json, rehearsal_excluded=EXCLUDED_REHEARSAL2.json,
     rehearsal1_draw=DRAW_REHEARSAL1.json and rehearsal1_excluded=EXCLUDED_REHEARSAL1.json (ORDER 2 and 3's files).""",
"""     analysis.py campaign with second_scan=EXCLUDED_SECOND_SCAN.json, rehearsal_draw=DRAW_REHEARSAL.json,
     rehearsal_excluded=EXCLUDED_REHEARSAL2.json, rehearsal1_draw=DRAW_REHEARSAL1.json and
     rehearsal1_excluded=EXCLUDED_REHEARSAL1.json (ORDER 2 and 3's files).""")
# announce
rep("""DRAW_ANNOUNCE (after the block vars and the block vars-rehearsal or vars-campaign; one announce branch, created by
one push of one commit, never pushed again, never forced, never deleted)""", """DRAW_ANNOUNCE (after the block vars and the block vars-rehearsal or vars-campaign; one announce branch, created by
one push of one commit, never pushed again, never forced, never deleted; the campaign's commit also carries the second
scan's raw output, EXCLUDED_SECOND_SCAN.json, named in DRAW_ANNOUNCE.txt's fifth line second_scan_sha256)""")
rep("""      X=$(realpath -e "$X")                                   # absolute, before any cd
      test ${#H} = 64 || { echo "REFUSED: H is not a sha256: no commit, no push"; exit 1; }
      test -z "$(git ls-remote""", """      X=$(realpath -e "$X")                                   # absolute, before any cd
      test ${#H} = 64 || { echo "REFUSED: H is not a sha256: no commit, no push"; exit 1; }
      if [ "$M" = campaign ]; then                            # the second scan's raw output, published with the list
        S=$(realpath -e "$S")
        test ${#HS} = 64 || { echo "REFUSED: HS is not a sha256: no commit, no push"; exit 1; }
      else
        [ -z "$S$HS" ] || { echo "REFUSED: S and HS are for the campaign only: no commit, no push"; exit 1; }
      fi
      test -z "$(git ls-remote""")
OLD_A = r"""      [ "$P" = "$H" ] || { echo "REFUSED: EXCLUDED_PUBLISHED.json has sha256 $P, not the validated $H: no commit, no push"; exit 1; }
      printf 'format layered-draw-announce/1\nmode %s\nexcluded_sha256 %s\nsizes %s\n' $M "$H" "$SIZES" > DRAW_ANNOUNCE.txt
      python -B -c "if True:
          import hashlib, json, sys; sys.path.insert(0, '$L'); import analysis as A, draw_seeds as D
          a = A.parse_announce(open('DRAW_ANNOUNCE.txt', 'rb').read()); x = json.load(open('EXCLUDED_PUBLISHED.json'))
          want = A.DRAW_SIZES if '$M' == 'campaign' else A.DRAW_SIZES_REHEARSAL
          frz = json.load(open('$L/EXCLUDED.json'))
          ok = (a['mode'] == '$M' and a['sizes'] == want and set(frz['seeds']) <= set(x['seeds'])
                and a['excluded_sha256'] == '$H' == hashlib.sha256(open('EXCLUDED_PUBLISHED.json', 'rb').read()).hexdigest()
                and D.excluded_fraction(x) <= D.MAX_EXCLUDED_FRACTION)
          print('announce ok' if ok else 'REFUSED: the announce is wrong: no commit, no push'); sys.exit(0 if ok else 1)"
"""
NEW_A = r"""      [ "$P" = "$H" ] || { echo "REFUSED: EXCLUDED_PUBLISHED.json has sha256 $P, not the validated $H: no commit, no push"; exit 1; }
      if [ "$M" = campaign ]; then
        cp "$S" EXCLUDED_SECOND_SCAN.json                     # the second scan's raw output, unedited
        Q=$(sha256sum EXCLUDED_SECOND_SCAN.json | cut -c1-64)
        [ "$Q" = "$HS" ] || { echo "REFUSED: EXCLUDED_SECOND_SCAN.json has sha256 $Q, not the validated $HS: no commit, no push"; exit 1; }
        printf 'format layered-draw-announce/1\nmode %s\nexcluded_sha256 %s\nsecond_scan_sha256 %s\nsizes %s\n' $M "$H" "$HS" "$SIZES" > DRAW_ANNOUNCE.txt
      else
        printf 'format layered-draw-announce/1\nmode %s\nexcluded_sha256 %s\nsizes %s\n' $M "$H" "$SIZES" > DRAW_ANNOUNCE.txt
      fi
      python -B -c "if True:
          import hashlib, json, sys; sys.path.insert(0, '$L'); import analysis as A, draw_seeds as D
          a = A.parse_announce(open('DRAW_ANNOUNCE.txt', 'rb').read()); x = json.load(open('EXCLUDED_PUBLISHED.json'))
          want = A.DRAW_SIZES if '$M' == 'campaign' else A.DRAW_SIZES_REHEARSAL
          frz = json.load(open('$L/EXCLUDED.json'))
          scan_ok = (a.get('second_scan_sha256') == '$HS' == hashlib.sha256(open('EXCLUDED_SECOND_SCAN.json', 'rb').read()).hexdigest()
                     and set(frz['seeds']) <= set(json.load(open('EXCLUDED_SECOND_SCAN.json'))['seeds'])) if '$M' == 'campaign' else 'second_scan_sha256' not in a
          ok = (a['mode'] == '$M' and a['sizes'] == want and set(frz['seeds']) <= set(x['seeds']) and scan_ok
                and a['excluded_sha256'] == '$H' == hashlib.sha256(open('EXCLUDED_PUBLISHED.json', 'rb').read()).hexdigest()
                and D.excluded_fraction(x) <= D.MAX_EXCLUDED_FRACTION)
          print('announce ok' if ok else 'REFUSED: the announce is wrong: no commit, no push'); sys.exit(0 if ok else 1)"
"""
rep(OLD_A, NEW_A)
rep("""      git add DRAW_ANNOUNCE.txt EXCLUDED_PUBLISHED.json
""", """      git add DRAW_ANNOUNCE.txt EXCLUDED_PUBLISHED.json
      [ "$M" != campaign ] || git add EXCLUDED_SECOND_SCAN.json
""")
rep("""  EXCLUDED.json (Pins); for the campaign, the line printed by ORDER 3 step (3). It is not checked against a sha256 it
  computes itself.""", """  EXCLUDED.json (Pins); for the campaign, the line printed by ORDER 3 step (3), which also gives HS, the second
  scan's sha256. It is not checked against a sha256 it computes itself.""")
p.write_text(t)
print("ok")
