( set -e
  X=$(realpath -e "$X")                                   # absolute, before any cd
  test ${#H} = 64 || { echo "REFUSED: H is not a sha256: no commit, no push"; exit 1; }
  test -z "$(git ls-remote https://github.com/HevisNico/kernel-R refs/heads/$B)" || { echo "REFUSED: $B already exists: no commit, no push"; exit 1; }
  ! git rev-parse --is-inside-work-tree >/dev/null 2>&1 || { echo "REFUSED: started inside a git work tree: no commit, no push"; exit 1; }
  [ ! -e announce_$M ] || { echo "REFUSED: announce_$M already exists: no commit, no push"; exit 1; }
  mkdir announce_$M
  cd announce_$M
  git init -q
  git checkout -q --orphan $B
  git fetch -q --depth 1 https://github.com/HevisNico/kernel-R refs/heads/main     # the owner identity, from main, never printed
  git config user.name "$(git log -1 --format=%an FETCH_HEAD)"
  git config user.email "$(git log -1 --format=%ae FETCH_HEAD)"
  cp "$X" EXCLUDED_PUBLISHED.json                         # the list the draw uses, published with it
  P=$(sha256sum EXCLUDED_PUBLISHED.json | cut -c1-64)
  [ "$P" = "$H" ] || { echo "REFUSED: EXCLUDED_PUBLISHED.json has sha256 $P, not the validated $H: no commit, no push"; exit 1; }
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
  [ "$(git rev-parse --show-toplevel)" = "$(pwd -P)" ] || { echo "REFUSED: the repository is not this new folder: no commit, no push"; exit 1; }
  [ "$(git symbolic-ref --short HEAD)" = "$B" ] || { echo "REFUSED: HEAD is not the orphan $B: no commit, no push"; exit 1; }
  ! git rev-parse -q --verify HEAD >/dev/null || { echo "REFUSED: the new repository already has a commit: no commit, no push"; exit 1; }
  git add DRAW_ANNOUNCE.txt EXCLUDED_PUBLISHED.json
  git commit -q -m "Draw announce ($M)"                   # the owner identity, set above
  O=$(git log -1 --format='%an %ae' FETCH_HEAD)
  [ "$(git log -1 --format='%an %ae' HEAD)" = "$O" ] && [ "$(git log -1 --format='%cn %ce' HEAD)" = "$O" ] || { echo "REFUSED: the commit's author or committer is not main's (the owner): no push"; exit 1; }
  git push -q https://github.com/HevisNico/kernel-R HEAD:refs/heads/$B   # the one push: the branch_creation that fixes t_push
  echo "announce pushed: $B $(git rev-parse HEAD)" )
