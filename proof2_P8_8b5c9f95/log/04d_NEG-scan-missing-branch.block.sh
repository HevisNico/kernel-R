snap before
mkdir -p /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/work/neg_scan
cd /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/work/neg_scan
( set -e
  [ ! -e scanrepo ] || { echo "REFUSED: scanrepo already exists: no commit, no push"; exit 1; }
  [ ! -e EXCLUDED_SECOND_SCAN.json ] || { echo "REFUSED: EXCLUDED_SECOND_SCAN.json already exists: no commit, no push"; exit 1; }
  mkdir scanrepo
  cd scanrepo
  git init -q
  git remote add origin https://github.com/HevisNico/kernel-R
  [ ! -e ../SCAN_LSREMOTE.txt ] || { echo "REFUSED: SCAN_LSREMOTE.txt already exists"; exit 1; }
  { printf '0000000000000000000000000000000000000000\trefs/heads/no-such-branch-for-the-proof\n'; git ls-remote --heads origin; } > ../SCAN_LSREMOTE.txt          # ONE ls-remote: the branches and their tips
  awk '{print $2}' ../SCAN_LSREMOTE.txt | sed 's#refs/heads/##' > ../SCAN_BRANCHES.txt
  wc -l < ../SCAN_BRANCHES.txt
  rm -f ../SCAN_BATCH_*
  split -l 10 ../SCAN_BRANCHES.txt ../SCAN_BATCH_              # fetched 10 branches at a time, each batch retried
  for f in ../SCAN_BATCH_*; do
    for i in 1 2 3 4; do
      timeout 3600 git fetch -q --depth 1 origin $(sed 's#.*#+refs/heads/&:refs/remotes/origin/&#' "$f") && break
      [ $i = 4 ] && { echo "REFUSED: the fetch of $f failed 4 times"; exit 1; }; sleep $((i * 10))
    done
  done
  # exactly the branches of the ls-remote, each at the tip the ls-remote gave
  git for-each-ref --format='%(objectname) %(refname)' refs/remotes/origin | sed 's# refs/remotes/origin/# refs/heads/#' | sort > ../SCAN_FETCHED.txt
  awk '{print $1" "$2}' ../SCAN_LSREMOTE.txt | sort > ../SCAN_EXPECTED.txt
  cmp -s ../SCAN_FETCHED.txt ../SCAN_EXPECTED.txt || { echo "REFUSED: the fetched refs are not the ls-remote's"; diff ../SCAN_EXPECTED.txt ../SCAN_FETCHED.txt | head; exit 1; }
  echo "fetched: every branch of the ls-remote at its tip ($(wc -l < ../SCAN_FETCHED.txt))"
  git update-ref refs/heads/master "$(git rev-parse refs/remotes/origin/main)"
  git symbolic-ref HEAD refs/heads/master
  cd ..
  python -B "$L/draw_seeds.py" scan EXCLUDED_SECOND_SCAN.json scanrepo )
echo "rc of the block=$?"
git -C scanrepo rev-parse -q --verify HEAD >/dev/null 2>&1 && echo 'NEGCHECK commit=yes' || echo 'NEGCHECK commit=no'
cd /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/work
snap after
cmp -s /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/log/.twin_before /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/log/.twin_after && echo 'NEGCHECK twin=same' || echo 'NEGCHECK twin=changed'
cmp -s /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/log/.gh_before /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/log/.gh_after && echo 'NEGCHECK github=same' || echo 'NEGCHECK github=changed'
