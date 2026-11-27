( set -e
  [ ! -e fetch_rehearsal ] || { echo "REFUSED: fetch_rehearsal already exists: no commit, no push"; exit 1; }
  [ ! -e DRAW_REHEARSAL.json ] || { echo "REFUSED: DRAW_REHEARSAL.json already exists: no commit, no push"; exit 1; }
  mkdir fetch_rehearsal
  cd fetch_rehearsal
  git init -q
  git fetch -q /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P7/github_twin.git refs/heads/evidence/combined-rehearsal-draw-result
  git show FETCH_HEAD:DRAW.json > ../DRAW_REHEARSAL.json
  cd ..
  sha256sum DRAW_REHEARSAL.json )
