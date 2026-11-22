#!/bin/bash
# N1, then N2, then N3 on M1, by the coordinator's brief section 1. Stops before a stage whose checks fail.
set -uo pipefail
O=/home/user/owner-prep; W=$O/wt; PY=$O/venv312-dev/bin/python; M=M1
export PYTHONPATH=$W/campaign-6-followup/research/learned-dnf-circuit-campaign-6-followup/dev:$W/campaign-7-prep/research/learned-dnf-circuit-campaign-7-prep/dev:$W/ffimpl/research/function-family/dev:$W/ffimpl/research/function-family-campaign/impl:$W/ffnet/research/function-family-campaign/net
ST=$W/ffpred/research/function-family-campaign/predicted/stages
inv() { echo "taken $(date -u +%FT%TZ), $1"; echo "## uptime -s"; uptime -s; echo "## nproc"; nproc; echo "## free"; free; echo "## df"; df; }
over() { python3 -c "import json,sys; s=json.load(open(sys.argv[1]))['runs']; sys.exit('running' in [v['status'] for v in s.values()])" "$1"; }
prev=Q
for S in N1 N2 N3; do
  JF=$ST/JOBS_${S}_$M.json
  over $O/campaign-runs/$M/$prev/STATE.json || { echo "STOP $S: $prev not over"; exit 1; }
  [ "$(pgrep -c ngspice)" = 0 ] || { echo "STOP $S: ngspice running"; exit 1; }
  free_kb=$(df --output=avail / | tail -1); [ "$free_kb" -ge 8000000 ] || { echo "STOP $S: disk $free_kb kB"; exit 1; }
  test ! -e $O/campaign-runs/$M/$S || { echo "STOP $S: stage folder exists"; exit 1; }
  for id in $(python3 -c "import json; print(' '.join(j['id'] for j in json.load(open('$JF'))['waves'][0]))"); do
    test ! -e $O/campaign-runs/$M/$id || { echo "STOP $S: $id exists"; exit 1; }
  done
  echo "CHECKS $S ok $(date -u +%T), free $((free_kb/1000000)) GB"
  inv "immediately before stage $S" > $O/campaign/INVENTORY_START_$S.staged.txt
  nohup $PY -B -c "import dosedev2; dosedev2.many('$JF')" > $O/campaign/many_$S.log 2>&1 &
  pid=$!
  for i in $(seq 100); do [ -d $O/campaign-runs/$M/$S ] && break; sleep 0.1; done
  cp $O/campaign/INVENTORY_START_$S.staged.txt $O/campaign-runs/$M/$S/INVENTORY_START.txt
  echo "START $S pid $pid $(date -u +%T)"
  wait $pid; echo "MANY $S exit $? $(date -u +%T)"
  inv "immediately after stage $S" > $O/campaign-runs/$M/$S/INVENTORY_END.txt
  python3 -c "
import json; s=json.load(open('$O/campaign-runs/$M/$S/STATE.json'))
for k,v in s['runs'].items():
    w=v.get('wall_s'); print('END $S', k, v['status'], 'wall_s', round(w,1) if w else None, 'limit', v['limit_s'], 'share', round(w/v['limit_s'],3) if w else None)"
  prev=$S
done
echo "ALL DONE $(date -u +%T)"
