#!/bin/bash
export PATH=$HOME/.elan/bin:$PATH
V=/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/prefreeze2/venvA/bin/python
F=/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/final
run() { # machine clone plan
  k=$1; c=$2; p=$3
  cd $F/clone$c/research/layered-networks
  t0=$(date +%s); echo "K$k start $(date -u +%H:%M:%S) clone$c free $(df -BG --output=avail /tmp | tail -1)"
  if [ ! -d $F/out_K$k ]; then $V -B campaign_run14.py launch $p $F/out_K$k jobs=4 template=$F/TEMPLATE_DRY.json || { echo "K$k launch failed"; return; }; else echo "K$k already launched"; fi
  while ! $V -B campaign_run14.py wait $F/out_K$k 580 > /dev/null; do :; done
  echo "K$k ended $(( $(date +%s) - t0 ))s free $(df -BG --output=avail /tmp | tail -1) $($V -B campaign_run14.py status $F/out_K$k | tr '\n' ' ')"
}
withseal() { # dup plan gets seal_log from the home machine's seal_push.json (the dry runs' manual step)
  python3 - "$@" <<'PY'
import json, sys
src, out, homes = sys.argv[1], sys.argv[2], sys.argv[3:]
p = json.load(open(src))
for x in p["remote_duplicates"]:
    for h in homes:
        import glob
        for f in glob.glob(h + "/*/seal_push.json"):
            r = json.load(open(f))
            if f.split("/")[-2].endswith("_%d" % x["seed"]):
                x["seal_log"] = [r["commit"], r["branch"]]
open(out, "w").write(json.dumps(p, indent=1, sort_keys=True) + "\n")
print("seal_log", [x.get("seal_log") for x in p["remote_duplicates"]])
PY
}
for k in 01 02 03 07 08; do run $k A $F/plans/PLAN_K$k.json; done
withseal $F/plans/PLAN_K04.json $F/plansB/PLAN_K04.json $F/out_K01; run 04 B $F/plansB/PLAN_K04.json
withseal $F/plans/PLAN_K05.json $F/plansB/PLAN_K05.json $F/out_K04; run 05 B $F/plansB/PLAN_K05.json
withseal $F/plans/PLAN_K06.json $F/plansB/PLAN_K06.json $F/out_K02; run 06 B $F/plansB/PLAN_K06.json
echo ALLDONE $(date -u +%H:%M:%S)
