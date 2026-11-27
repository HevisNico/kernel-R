# step (3) with the rehearsal's announce read offline (the stand-in has no announce on GitHub): the same checks,
# check_draw and check_rehearsal_seeds with offline=True / strict=False and rehearsal_announce=
import datetime, hashlib, json, sys, tempfile; sys.path.insert(0, '/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/final/W/kernel-R/research/layered-networks'); import analysis as A, draw_seeds as D
x = json.load(open('EXCLUDED_SECOND.json')); frz = json.load(open('/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/final/W/kernel-R/research/layered-networks/EXCLUDED.json')); have = set(x['seeds'])
r, info, _ = A.check_draw(dict(draw='DRAW_REHEARSAL.json', excluded='/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/final/W/kernel-R/research/layered-networks/EXCLUDED.json', announce='/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/final/W/work/ANNOUNCE_REHEARSAL.txt'), 'rehearsal', tempfile.mkdtemp(), '0b33340d16cbac3edc00ffae7b6416dddfbdb013', offline=True)
rs = sorted(s for v in r['groups'].values() for s in v); noise = [10 * s + n for s in rs for n in range(4)]
now = datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
print(A.check_rehearsal_seeds(dict(rehearsal_draw='DRAW_REHEARSAL.json', excluded='EXCLUDED_SECOND.json', rehearsal_announce='/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/final/W/work/ANNOUNCE_REHEARSAL.txt'),
      dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '0b33340d16cbac3edc00ffae7b6416dddfbdb013', False))
ok = (len(rs) == 18 and len(noise) == 72 and set(rs + noise) <= have and set(frz['seeds']) <= have
      and x['count'] == len(x['seeds']) == len(have) and x['seeds'] == sorted(have)
      and hashlib.sha256(D.canon(x['seeds'])).hexdigest() == x['seeds_sha256']
      and D.excluded_fraction(x) <= D.MAX_EXCLUDED_FRACTION)
print('the list is right' if ok else 'THE LIST IS WRONG', len(rs), len(noise), 'fraction', D.excluded_fraction(x),
      'sha256', hashlib.sha256(open('EXCLUDED_SECOND.json', 'rb').read()).hexdigest()); sys.exit(0 if ok else 1)
