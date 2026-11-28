( set -e
  X=$(realpath -e "$X")                                   # absolute, before any cd
  ! git rev-parse --is-inside-work-tree >/dev/null 2>&1 || { echo "REFUSED: started inside a git work tree: no commit, no push"; exit 1; }
  [ ! -e draw_$M ] || { echo "REFUSED: draw_$M already exists: no commit, no push"; exit 1; }
  mkdir draw_$M
  cd draw_$M
  # 1. the announce commit and GitHub's push time of its branch_creation, read as analysis.py reads them
  CT=$(python -B -c "if True:
      import sys, tempfile; sys.path.insert(0, '$L'); import analysis as A
      c, text, t = A.announce_on_github('$B', tempfile.mkdtemp()); print(c, t)")
  C=${CT% *}; T=${CT#* }; echo "announce commit $C, pushed $T"
  # 2. the round that push time fixes (ROUND below); wait until its time has passed
  python -B -c "if True:
      import json, sys; sys.path.insert(0, '$L'); import beacon_chain
      open('CHAIN.json', 'w').write(json.dumps(beacon_chain.QUICKNET))"
  python -B "$L/beacon_verify.py" round CHAIN.json "$T" | tee ROUND_RULE.json
  ROUND=$(python -B -c "import json; print(json.load(open('ROUND_RULE.json'))['round'])")
  RT=$(python -B -c "import json; print(json.load(open('ROUND_RULE.json'))['round_time_unix'])")
  while [ "$(date +%s)" -lt "$RT" ]; do sleep 5; done
  # 3. the round from drand (api.drand.sh, else api2.drand.sh; any relay will do), verified against the pinned key
  CH=52db9ba70e0cc0f6eaf7803dd07447a1f5477735fd3f661792ba94600c84e971
  curl -sf https://api.drand.sh/$CH/public/$ROUND > ROUND_RAW.json || curl -sf https://api2.drand.sh/$CH/public/$ROUND > ROUND_RAW.json
  python -B -c "if True:
      import json; r = json.load(open('ROUND_RAW.json'))
      open('ROUND.json', 'w').write(json.dumps({k: r[k] for k in ('round', 'signature', 'randomness')}))"
  python -B "$L/beacon_verify.py" verify CHAIN.json ROUND.json
  # 4. the draw, on the published list X, and DRAW.json (DRAW_CORE.json and two keys, byte for byte draw_seeds.canon)
  python -B "$L/draw_seeds.py" draw "$(python -B -c "import json; print(json.load(open('ROUND.json'))['randomness'])")" "$ROUND" "$X" DRAW_CORE.json $SIZES
  python -B -c "if True:
      import json, sys; sys.path.insert(0, '$L'); import draw_seeds as D
      d = json.load(open('DRAW_CORE.json')); d['beacon_round'] = json.load(open('ROUND.json'))
      d['announce'] = dict(branch='$B', commit='$C', push_utc='$T')
      open('DRAW.json', 'wb').write(D.canon(d))"
  # 5. THE CHECK BEFORE ANY MACHINE STARTS, on the file itself: it reads the announce on GitHub and refuses as
  #    analysis.py would; it must print the draw's record
  python -B -c "if True:
      import sys, tempfile; sys.path.insert(0, '$L'); import analysis as A
      d, info, n = A.check_draw(dict(draw='DRAW.json', excluded='$X'), '$M', tempfile.mkdtemp(), '$F'); print(info)"
  # 6. the plans made from that checked file (m=12), PLAN_K01..K12.json, each sent to its machine unedited
  python -B "$L/plan_split3.py" DRAW.json "$L/campaign_template.json" PLANS
  # 7. DRAW.json published on its own result branch R, by one creating push (the announce branch B keeps its
  #    single push)
  D=$(realpath -e DRAW.json)
  test -z "$(git ls-remote https://github.com/HevisNico/kernel-R refs/heads/$R)" || { echo "REFUSED: $R already exists"; exit 1; }
  [ ! -e result ] || { echo "REFUSED: result already exists: no commit, no push"; exit 1; }
  mkdir result
  cd result
  git init -q
  git checkout -q --orphan $R
  git fetch -q --depth 1 https://github.com/HevisNico/kernel-R refs/heads/main     # the owner identity, from main, never printed
  git config user.name "$(git log -1 --format=%an FETCH_HEAD)"
  git config user.email "$(git log -1 --format=%ae FETCH_HEAD)"
  cp "$D" DRAW.json
  [ "$(git rev-parse --show-toplevel)" = "$(pwd -P)" ] || { echo "REFUSED: the repository is not this new folder: no commit, no push"; exit 1; }
  [ "$(git symbolic-ref --short HEAD)" = "$R" ] || { echo "REFUSED: HEAD is not the orphan $R: no commit, no push"; exit 1; }
  ! git rev-parse -q --verify HEAD >/dev/null || { echo "REFUSED: the new repository already has a commit: no commit, no push"; exit 1; }
  git add DRAW.json
  git commit -q -m "Draw result ($M)"                     # the owner identity, set above
  O=$(git log -1 --format='%an %ae' FETCH_HEAD)
  [ "$(git log -1 --format='%an %ae' HEAD)" = "$O" ] && [ "$(git log -1 --format='%cn %ce' HEAD)" = "$O" ] || { echo "REFUSED: the commit's author or committer is not main's (the owner): no push"; exit 1; }
  git push -q https://github.com/HevisNico/kernel-R HEAD:refs/heads/$R
  echo "draw published: $R $(git rev-parse HEAD)" )
