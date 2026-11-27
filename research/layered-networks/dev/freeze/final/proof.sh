#!/bin/bash
# The final freeze proof, on a clean clone of the freeze candidate. Usage: proof.sh WORK COMMIT PYTHON TOOLS
# WORK must not exist. Every command is printed ("$ ...") with its output and its exit status, into WORK/log/*.txt.
set -u
W=$1; C=$2; V=$3; T=$4
[ -e "$W" ] && { echo "WORK $W exists"; exit 2; }
mkdir -p $W/log $W/work
run() { local f=$1; shift; { echo "\$ $*"; ( eval "$@" ) 2>&1; echo "rc=$?"; echo; } >> $W/log/$f.txt; }
REMOTE=https://github.com/HevisNico/kernel-R
python() { "$V" "$@"; }   # FREEZE.txt's `python` is the pinned Python

# 0. the clean clone, fetched by branch name; worktrees at the template's kit_commit and noise_commit
run 00_clone "git init -q $W/kernel-R && cd $W/kernel-R && git remote add origin $REMOTE && for b in research/layered-campaign-dev research/inverter-instances research/layered-networks main; do git fetch -q origin refs/heads/\$b:refs/remotes/origin/\$b || exit 1; done && git merge-base --is-ancestor $C origin/research/layered-campaign-dev && git checkout -q -B research/layered-campaign-dev $C && git rev-parse HEAD origin/research/layered-campaign-dev && git status --porcelain --untracked-files=all | wc -l"
L=$W/kernel-R/research/layered-networks
K=$(python3 -c "import json;print(json.load(open('$L/campaign_template.json'))['kit_commit'])")
N=$(python3 -c "import json;print(json.load(open('$L/campaign_template.json'))['noise_commit'])")
run 00_clone "cd $W/kernel-R && git worktree add -q --detach $W/kit $K && git worktree add -q --detach $W/noise $N && git worktree list"
F=$(git -C $L rev-parse HEAD)

# 1. the pins regeneration, on the clone's own files, compared byte for byte with its FREEZE_PINS.json
BASE=$(python3 -c "import json;print(json.load(open('$L/FREEZE_PINS.json'))['base'])")
run 01_pins "cd $W/work && python3 $T/closure2.py $W/kernel-R campaign.py analysis.py plan_split3.py draw_seeds.py beacon_verify.py beacon_chain.py d4_regate.py leancell.py tests/check_duplicate.py > closure.json && python3 -c \"import json;print(len(json.load(open('closure.json'))['files']), 'files in the closure')\""
run 01_pins "cd $W/work && python3 $T/make_pins3.py $W/kernel-R closure.json FREEZE_PINS.regenerated.json $(printf %q "$BASE") | tail -3"
run 01_pins "cmp $W/work/FREEZE_PINS.regenerated.json $L/FREEZE_PINS.json && echo IDENTICAL && sha256sum $L/FREEZE_PINS.json"
run 01_pins "cd $W/kernel-R && python3 -c \"import json,subprocess as s; a=json.loads(s.run(['git','show','483f90c5:research/layered-networks/FREEZE_PINS.json'],capture_output=True,check=True).stdout); b=json.load(open('$L/FREEZE_PINS.json')); fa={p:h for g in a['groups'].values() for p,h in g.items()}; fb={p:h for g in b['groups'].values() for p,h in g.items()}; print('against the pins before (483f90c5): added', sorted(set(fb)-set(fa)), 'removed', sorted(set(fa)-set(fb)), 'changed', sorted(p for p in fa if p in fb and fa[p]!=fb[p]), 'groups the same', {k:sorted(v) for k,v in a['groups'].items()}=={k:sorted(v) for k,v in b['groups'].items()}, 'tools the same', a['tools']==b['tools'])\""

# 2. the stand-ins: quicknet round 1000000 as published (a STAND-IN: the rehearsal draw does not exist yet)
cat > $W/work/standin.py <<EOF
import datetime, hashlib, json, sys
sys.path.insert(0, '$L'); import beacon_chain, beacon_verify, draw_seeds as D
br = dict(round=1000000, randomness="b22aad4794f7451896f7a371aa46106fd84d919f3f569acd5b2fddf1d1440af3",
          signature="83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98fd8b11a029f1bee9d9e83b45088abe72")
assert beacon_verify.verify(beacon_chain.QUICKNET, br)["ok"]
t0 = beacon_verify.round_time(beacon_chain.QUICKNET, 1000000) - beacon_verify.DELAY_S
push = datetime.datetime.fromtimestamp(t0, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
exf = '$L/EXCLUDED.json'; ex = json.load(open(exf)); xs = hashlib.sha256(open(exf, 'rb').read()).hexdigest()
for label, mode, branch, sizes in (("REHEARSAL", "rehearsal", "evidence/combined-rehearsal-draw", dict(NOT1=6, ANDOR3=6, XOR3=6)),
                                   ("CAMPAIGN_SIZES", "campaign", "evidence/combined-draw", dict(NOT1=60, ANDOR3=32, XOR3=37))):
    d = D.draw(br["randomness"], br["round"], ex, dict(sizes))
    open(f"DRAW_{label}.json", "wb").write(D.canon(dict(d, beacon_round=br, announce=dict(branch=branch, commit="0" * 40, push_utc=push))))
    open(f"ANNOUNCE_{label}.txt", "w").write(f"format layered-draw-announce/1\nmode {mode}\nexcluded_sha256 {xs}\nsizes "
                                             + " ".join(f"{g}={sizes[g]}" for g in ("NOT1", "ANDOR3", "XOR3")) + "\n")
    print(label, {g: len(v) for g, v in d["groups"].items()}, "push_utc", push, "sha256",
          hashlib.sha256(open(f"DRAW_{label}.json", "rb").read()).hexdigest())
EOF
run 02_standins "cd $W/work && cat standin.py && $V -B standin.py"

# 3. the plans (plan_split3 on the stand-in at 60/32/37) and campaign.py check campaign on all 12
run 03_check_campaign "cd $W/work && $V -B $L/plan_split3.py DRAW_CAMPAIGN_SIZES.json $L/campaign_template.json plans | tail -3 && ls plans"
for k in 01 02 03 04 05 06 07 08 09 10 11 12; do
  run 03_check_campaign "cd $L && $V -B campaign.py check campaign campaign_template.json $W/work/plans/PLAN_K$k.json > $W/work/check_K$k.json; echo exit \$?; $V -c \"import json; d=json.load(open('$W/work/check_K$k.json')); p=d.get('pins') or {}; print('PLAN_K$k', 'ok', d.get('ok'), 'tree_clean', p.get('tree_clean'), 'mismatched', p.get('mismatched'), 'not_pinned', p.get('not_pinned'), 'pinned_files', p.get('pinned_files'), 'pins_sha256', p.get('pins_sha256'), 'tree_commit', p.get('tree_commit'))\""
done
cp $W/work/check_K01.json $W/log/03_check_campaign_K01.json
run 03_check_campaign "cd $W/kernel-R && git status --porcelain --untracked-files=all | wc -l"

# 4. analysis.py rehearsal past the pins gate, on a TEST root (evidence/devtest-run2-K02's out_K02)
run 04_analysis_rehearsal "cd $W && mkdir rootsrc && cd rootsrc && git init -q && git fetch -q $REMOTE refs/heads/evidence/devtest-run2-K02 && git rev-parse FETCH_HEAD && git archive FETCH_HEAD out_K02 | tar -x -C $W && ls $W/out_K02 | head -5"
run 04_analysis_rehearsal "cd $L && $V -B analysis.py rehearsal $W/an1 $W/out_K02 times=github controls=$W/noise draw=$W/work/DRAW_REHEARSAL.json"
run 04_analysis_rehearsal "cd $L && $V -B analysis.py rehearsal $W/an2 $W/out_K02 times=github controls=$W/noise/research/layered-networks draw=$W/work/DRAW_REHEARSAL.json"
run 04_analysis_rehearsal "cd $L && $V -B analysis.py campaign $W/an3 $W/out_K02 times=github controls=$W/noise/research/layered-networks draw=$W/work/DRAW_CAMPAIGN_SIZES.json"

# 5. option (A), FREEZE.txt's three steps, verbatim, on the real files: EXCLUDED_SECOND_SCAN.json = the last scan's
#    output (the pinned EXCLUDED.json, unedited); DRAW_REHEARSAL.json = the round-1000000 STAND-IN
extract() { python3 - "$L/FREEZE.txt" "$1" <<'EOF'
import sys
t = open(sys.argv[1]).read().split("\n"); key = sys.argv[2]
i0 = next(k for k, x in enumerate(t) if x.strip().startswith(key))
i = next(k for k in range(i0, len(t)) if t[k].strip().startswith("python -B -c"))
j = next(k for k in range(i, len(t)) if t[k].rstrip().endswith(')"'))
print("\n".join(x[7:] if x.startswith("       ") else x for x in t[i:j + 1]))
EOF
}
mkdir -p $W/work/A && cp $L/EXCLUDED.json $W/work/A/EXCLUDED_SECOND_SCAN.json && cp $W/work/DRAW_REHEARSAL.json $W/work/A/
extract "(1) and (2)" > $W/work/A/step12.sh; extract "(3) re-read" > $W/work/A/step3.sh
run 05_option_A "cd $W/work/A && L=$L F=$F && sha256sum EXCLUDED_SECOND_SCAN.json DRAW_REHEARSAL.json && cat step12.sh && . ./step12.sh"
run 05_option_A "cd $W/work/A && L=$L F=$F && cat step3.sh && . ./step3.sh"
cat > $W/work/A/step3_offline.py <<EOF
# step (3) with the rehearsal's announce read offline (the stand-in has no announce on GitHub): the same checks,
# check_draw and check_rehearsal_seeds with offline=True / strict=False and rehearsal_announce=
import datetime, hashlib, json, sys, tempfile; sys.path.insert(0, '$L'); import analysis as A, draw_seeds as D
x = json.load(open('EXCLUDED_SECOND.json')); frz = json.load(open('$L/EXCLUDED.json')); have = set(x['seeds'])
r, info, _ = A.check_draw(dict(draw='DRAW_REHEARSAL.json', excluded='$L/EXCLUDED.json', announce='$W/work/ANNOUNCE_REHEARSAL.txt'), 'rehearsal', tempfile.mkdtemp(), '$F', offline=True)
rs = sorted(s for v in r['groups'].values() for s in v); noise = [10 * s + n for s in rs for n in range(4)]
now = datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
print(A.check_rehearsal_seeds(dict(rehearsal_draw='DRAW_REHEARSAL.json', excluded='EXCLUDED_SECOND.json', rehearsal_announce='$W/work/ANNOUNCE_REHEARSAL.txt'),
      dict(announce=dict(push_utc=now)), tempfile.mkdtemp(), '$F', False))
ok = (len(rs) == 18 and len(noise) == 72 and set(rs + noise) <= have and set(frz['seeds']) <= have
      and x['count'] == len(x['seeds']) == len(have) and x['seeds'] == sorted(have)
      and hashlib.sha256(D.canon(x['seeds'])).hexdigest() == x['seeds_sha256']
      and D.excluded_fraction(x) <= D.MAX_EXCLUDED_FRACTION)
print('the list is right' if ok else 'THE LIST IS WRONG', len(rs), len(noise), 'fraction', D.excluded_fraction(x),
      'sha256', hashlib.sha256(open('EXCLUDED_SECOND.json', 'rb').read()).hexdigest()); sys.exit(0 if ok else 1)
EOF
run 05_option_A "cd $W/work/A && cat step3_offline.py && $V -B step3_offline.py"
run 05_option_A "cd $W/work/A && $V -c \"import json; a=json.load(open('EXCLUDED_SECOND_SCAN.json')); b=json.load(open('EXCLUDED_SECOND.json')); print('scan', a['count'], 'final', b['count'], 'added', len(set(b['seeds'])-set(a['seeds'])), 'removed', len(set(a['seeds'])-set(b['seeds'])), 'keys added', sorted(set(b)-set(a)), 'refs kept', a['refs']==b['refs'], 'rule kept', a['rule']==b['rule'])\""

# 6. the pre-announce check (DRAW_ANNOUNCE), verbatim, for the rehearsal (X = the pinned list) and the campaign
#    (X = EXCLUDED_SECOND.json of step 5); nothing committed, nothing pushed
pre() { python3 - "$L/FREEZE.txt" <<'EOF'
import sys
t = open(sys.argv[1]).read().split("\n")
i = next(k for k, x in enumerate(t) if x.strip().startswith("cp $X EXCLUDED_PUBLISHED.json"))
j = next(k for k in range(i, len(t)) if t[k].rstrip().endswith('sys.exit(0 if ok else 1)"'))
print("\n".join(x[2:] for x in t[i:j + 1]).replace("<frozen tree>", "$TREE"))
EOF
}
pre > $W/work/preannounce.sh
for M in rehearsal campaign; do
  if [ $M = rehearsal ]; then B=evidence/combined-rehearsal-draw; X=$L/EXCLUDED.json; Z="NOT1=6 ANDOR3=6 XOR3=6"; else B=evidence/combined-draw; X=$W/work/A/EXCLUDED_SECOND.json; Z="NOT1=60 ANDOR3=32 XOR3=37"; fi
  run 06_preannounce "B=$B; M=$M; X=$X; Z='$Z'; TREE=$W/kernel-R; echo B=\$B M=\$M X=\$X Z=\$Z; git ls-remote $REMOTE refs/heads/\$B | wc -l; mkdir $W/announce_$M && cd $W/announce_$M && git init -q && git checkout -q --orphan \$B && cat $W/work/preannounce.sh && . $W/work/preannounce.sh && cat DRAW_ANNOUNCE.txt"
done
run 06_preannounce "cd $W/kernel-R && git status --porcelain --untracked-files=all | wc -l && git rev-parse HEAD"
echo done
