#!/bin/bash
# N1, then N2, then N3 on M3, as briefed: per-stage checks, launch once, wait, end inventory. Stops on a failed check.
O=/home/user/owner-prep; W=$O/wt; PY=$O/venv312-dev/bin/python; M=M3
export PYTHONPATH=$W/campaign-6-followup/research/learned-dnf-circuit-campaign-6-followup/dev:$W/campaign-7-prep/research/learned-dnf-circuit-campaign-7-prep/dev:$W/ffimpl/research/function-family/dev:$W/ffimpl/research/function-family-campaign/impl:$W/ffnet/research/function-family-campaign/net
ST=$W/ffpred/research/function-family-campaign/predicted/stages; R=$O/campaign-runs/$M
inv(){ echo "taken $(date -u +%FT%TZ), $1"; echo "## uptime -s"; uptime -s; echo "## nproc"; nproc; echo "## free"; free; echo "## df"; df; }
prev=Q
for S in N1 N2 N3; do
  JF=$ST/JOBS_${S}_$M.json
  echo "[$(date -u +%T)] checks before $S"
  [ -f $R/$prev/STATE.json ] && ! grep -q '"running"' $R/$prev/STATE.json || { echo "STOP: $prev not over"; exit 1; }
  [ "$(pgrep -c ngspice)" = 0 ] || { echo "STOP: ngspice running"; exit 1; }
  free_kb=$(df --output=avail / | tail -1); [ $free_kb -ge $((8*1024*1024)) ] || { echo "STOP: under 8 GB free"; exit 1; }
  test ! -e $R/$S || { echo "STOP: $R/$S exists"; exit 1; }
  for id in $(python3 -I -c "import json;print(' '.join(j['id'] for j in json.load(open('$JF'))['waves'][0]))"); do test ! -e $R/$id || { echo "STOP: $R/$id exists"; exit 1; }; done
  df -h / | tail -1
  inv "immediately before stage $S" > $O/campaign/INVENTORY_START_$S.staged.txt
  nohup $PY -B -c "import dosedev2; dosedev2.many('$JF')" > $O/campaign/many_$S.log 2>&1 < /dev/null &
  P=$!; echo "[$(date -u +%T)] $S launched, many pid $P"
  for i in $(seq 100); do [ -d $R/$S ] && break; sleep 0.1; done
  cp $O/campaign/INVENTORY_START_$S.staged.txt $R/$S/INVENTORY_START.txt && echo "$S inventory start copied"
  while kill -0 $P 2>/dev/null; do sleep 10; done
  grep -q '"running"' $R/$S/STATE.json && echo "WARN: $S STATE still has running"
  inv "immediately after stage $S" > $R/$S/INVENTORY_END.txt
  echo "[$(date -u +%T)] $S ended"; python3 -I -c "import json;d=json.load(open('$R/$S/STATE.json'));[print('  ',k,v['status'],'wall',round(v['wall_s'],1),'limit',v['limit_s'],'share',round(v['share_of_limit'],3)) for k,v in d['runs'].items()]"
  echo "STAGE_DONE $S"
  prev=$S
done
echo "ALL_DONE"
