( set -e
  [ ! -e fetch_rehearsal1 ] || { echo "REFUSED: fetch_rehearsal1 already exists"; exit 1; }
  [ ! -e DRAW_REHEARSAL1.json ] || { echo "REFUSED: DRAW_REHEARSAL1.json already exists"; exit 1; }
  [ ! -e EXCLUDED_REHEARSAL1.json ] || { echo "REFUSED: EXCLUDED_REHEARSAL1.json already exists"; exit 1; }
  mkdir fetch_rehearsal1
  cd fetch_rehearsal1
  git init -q
  git fetch -q https://github.com/HevisNico/kernel-R refs/heads/evidence/combined-rehearsal-draw-result
  [ "$(git rev-parse FETCH_HEAD)" = f74b75fbdf72a5e57abe4ef8c5694197df0335dd ] || { echo "REFUSED: rehearsal 1's result branch moved"; exit 1; }
  git show FETCH_HEAD:DRAW.json > ../DRAW_REHEARSAL1.json
  git fetch -q https://github.com/HevisNico/kernel-R refs/heads/evidence/combined-rehearsal-draw
  git show FETCH_HEAD:EXCLUDED_PUBLISHED.json > ../EXCLUDED_REHEARSAL1.json
  cd ..
  sha256sum DRAW_REHEARSAL1.json EXCLUDED_REHEARSAL1.json )
