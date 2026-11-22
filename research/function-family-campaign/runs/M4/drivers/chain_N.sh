#!/bin/bash
# N1, then N2, then N3 (brief section 1). Per-stage checks; on a failed check: STOP (no later stage).
O=/home/user/owner-prep; W=$O/wt; PY=$O/venv312-dev/bin/python; M=M4; R=$O/campaign-runs/$M
ST=$W/ffpred/research/function-family-campaign/predicted/stages
export PYTHONPATH=$W/campaign-6-followup/research/learned-dnf-circuit-campaign-6-followup/dev:$W/campaign-7-prep/research/learned-dnf-circuit-campaign-7-prep/dev:$W/ffimpl/research/function-family/dev:$W/ffimpl/research/function-family-campaign/impl:$W/ffnet/research/function-family-campaign/net
inv() { echo "taken $(date -u +%FT%TZ), $1"; echo "## uptime -s"; uptime -s; echo "## nproc"; nproc; echo "## free"; free; echo "## df"; df; }
cd $O
prev=Q
for S in N1 N2 N3; do
  JF=$ST/JOBS_${S}_$M.json
  grep -q '"running"' $R/$prev/STATE.json && { echo "STOP before $S: $prev still running"; exit 1; }
  [ "$(pgrep -c ngspice)" = 0 ] || { echo "STOP before $S: ngspice running"; exit 1; }
  avail=$(df -BG --output=avail / | tail -1 | tr -dc 0-9); [ "$avail" -ge 8 ] || { echo "STOP before $S: only ${avail}G free"; exit 1; }
  [ ! -e $R/$S ] || { echo "STOP before $S: $R/$S exists"; exit 1; }
  for id in $(python3 -c "import json;print(' '.join(j['id'] for w in json.load(open('$JF'))['waves'] for j in w))"); do [ ! -e $R/$id ] || { echo "STOP before $S: $R/$id exists"; exit 1; }; done
  echo "$S checks OK (${avail}G free)"
  inv "immediately before stage $S" > $O/campaign/INVENTORY_START_$S.staged.txt
  nohup $PY -B -c "import dosedev2; dosedev2.many('$JF')" > $O/campaign/many_$S.log 2>&1 &
  pid=$!; echo $pid > $O/campaign/many_$S.pid; echo "$S launched $(date -u +%FT%TZ) pid $pid"
  for i in $(seq 1200); do [ -d $R/$S ] && break; sleep 0.1; done
  if [ -d $R/$S ]; then cp $O/campaign/INVENTORY_START_$S.staged.txt $R/$S/INVENTORY_START.txt; else echo "WARN $S folder not seen in 120 s"; fi
  sleep 5; while kill -0 $pid 2>/dev/null || grep -q '"running"' $R/$S/STATE.json 2>/dev/null; do sleep 20; done
  [ -d $R/$S ] && inv "immediately after stage $S" > $R/$S/INVENTORY_END.txt
  [ -e $R/$S/INVENTORY_START.txt ] || { [ -d $R/$S ] && cp $O/campaign/INVENTORY_START_$S.staged.txt $R/$S/INVENTORY_START.txt && echo "$S START inventory copied late"; }
  echo "$S ended $(date -u +%FT%TZ)"
  prev=$S
done
echo ALL_DONE
