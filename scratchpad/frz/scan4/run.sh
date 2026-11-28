#!/bin/bash
# the final rescan, same procedure as FREEZE.txt [block second-scan], output EXCLUDED.json
set -e
S=/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad
W=$S/frz/scan4; cd $W
L=$S/dev/research/layered-networks; V=$S/prefreeze2/venvA/bin/python
[ ! -e scanrepo ] || { echo "REFUSED: scanrepo exists"; exit 1; }
mkdir scanrepo; cd scanrepo; git init -q; git remote add origin https://github.com/HevisNico/kernel-R
git ls-remote --heads origin > ../SCAN_LSREMOTE.txt
date -u +%FT%TZ > ../SCAN_START.txt
awk '{print $2}' ../SCAN_LSREMOTE.txt | sed 's#refs/heads/##' > ../SCAN_BRANCHES.txt
wc -l < ../SCAN_BRANCHES.txt
split -l 10 ../SCAN_BRANCHES.txt ../SCAN_BATCH_
for f in ../SCAN_BATCH_*; do
  for i in 1 2 3 4; do
    timeout 3600 git fetch -q --depth 1 origin $(sed 's#.*#+refs/heads/&:refs/remotes/origin/&#' "$f") && break
    [ $i = 4 ] && { echo "REFUSED: fetch of $f failed 4 times"; exit 1; }; sleep $((i * 10))
  done
done
git for-each-ref --format='%(objectname) %(refname)' refs/remotes/origin | sed 's# refs/remotes/origin/# refs/heads/#' | sort > ../SCAN_FETCHED.txt
awk '{print $1" "$2}' ../SCAN_LSREMOTE.txt | sort > ../SCAN_EXPECTED.txt
cmp -s ../SCAN_FETCHED.txt ../SCAN_EXPECTED.txt || { echo "REFUSED: fetched refs differ from ls-remote"; diff ../SCAN_EXPECTED.txt ../SCAN_FETCHED.txt | head; exit 1; }
echo "fetched: $(wc -l < ../SCAN_FETCHED.txt) branches at their ls-remote tips"
git ls-remote --heads origin | awk '{print $1" "$2}' | sort > ../SCAN_LSREMOTE_AFTER.txt
cmp -s ../SCAN_EXPECTED.txt ../SCAN_LSREMOTE_AFTER.txt && echo "origin unchanged during the scan" || echo "NOTE: origin moved after the fetch (see SCAN_LSREMOTE_AFTER.txt)"
git update-ref refs/heads/master "$(git rev-parse refs/remotes/origin/main)"
git symbolic-ref HEAD refs/heads/master
cd ..
$V -B "$L/draw_seeds.py" scan EXCLUDED.json scanrepo
$V -B "$L/draw_seeds.py" print EXCLUDED.json > EXCLUDED_PRINT.txt
date -u +%FT%TZ > SCAN_END.txt
echo "scan done"
