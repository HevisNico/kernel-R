#!/bin/bash
# N1, then N2, then N3 on M2, each once, each after its own checks (brief section 1). Stops at the first failed check.
O=/home/user/owner-prep; W=$O/wt; PY=$O/venv312-dev/bin/python; M=M2; ST=$W/ffpred/research/function-family-campaign/predicted/stages
export PYTHONPATH=$W/campaign-6-followup/research/learned-dnf-circuit-campaign-6-followup/dev:$W/campaign-7-prep/research/learned-dnf-circuit-campaign-7-prep/dev:$W/ffimpl/research/function-family/dev:$W/ffimpl/research/function-family-campaign/impl:$W/ffnet/research/function-family-campaign/net
inv() { echo "taken $(date -u +%FT%TZ), $1"; echo "## uptime -s"; uptime -s; echo "## nproc"; nproc; echo "## free"; free; echo "## df"; df; }
prev=Q
for S in N1 N2 N3; do
  JF=$ST/JOBS_${S}_$M.json
  grep -q '"running"' $O/campaign-runs/$M/$prev/STATE.json && { echo "STOP before $S: $prev still running"; exit 1; }
  [ "$(pgrep -c ngspice)" = 0 ] || { echo "STOP before $S: ngspice running"; exit 1; }
  free_gb=$(df -BG --output=avail / | tail -1 | tr -dc 0-9); [ "$free_gb" -ge 8 ] || { echo "STOP before $S: ${free_gb}G free"; exit 1; }
  test ! -e $O/campaign-runs/$M/$S || { echo "STOP before $S: folder exists"; exit 1; }
  for id in $($PY -c "import json; print(' '.join(j['id'] for w in json.load(open('$JF'))['waves'] for j in w))"); do test ! -e $O/campaign-runs/$M/$id || { echo "STOP before $S: $id exists"; exit 1; }; done
  echo "checks OK before $S $(date -u +%FT%TZ)"
  inv "immediately before stage $S" > $O/campaign/INVENTORY_START_$S.staged.txt
  cd /tmp; $PY -B -c "import dosedev2; dosedev2.many('$JF')" > $O/campaign/many_$S.log 2>&1 < /dev/null &
  pid=$!; echo $pid > $O/campaign/many_$S.pid
  for i in $(seq 600); do [ -d $O/campaign-runs/$M/$S ] && break; sleep 0.1; done; cp $O/campaign/INVENTORY_START_$S.staged.txt $O/campaign-runs/$M/$S/INVENTORY_START.txt
  wait $pid; echo "stage $S many exit $? $(date -u +%FT%TZ)"
  inv "immediately after stage $S" > $O/campaign-runs/$M/$S/INVENTORY_END.txt
  prev=$S
done
echo "done $(date -u +%FT%TZ)"
