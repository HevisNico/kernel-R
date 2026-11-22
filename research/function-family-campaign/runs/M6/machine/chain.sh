#!/bin/bash
# M6: after stage D ends, write its END inventory, then run S, then O, each with START/END inventories.
O=/home/user/owner-prep; W=$O/wt; PY=$O/venv312-dev/bin/python; M=M6; RUNS=$O/campaign-runs/$M
export PYTHONPATH=$W/campaign-6-followup/research/learned-dnf-circuit-campaign-6-followup/dev:$W/campaign-7-prep/research/learned-dnf-circuit-campaign-7-prep/dev:$W/ffimpl/research/function-family/dev:$W/ffimpl/research/function-family-campaign/impl:$W/ffnet/research/function-family-campaign/net
inv() { echo "taken $(date -u +%FT%TZ), $1"; echo "## uptime -s"; uptime -s; echo "## nproc"; nproc; echo "## free"; free; echo "## df"; df; }
running() { python3 -c "import json,sys;s=json.load(open('$1'));sys.exit(0 if any(v['status']=='running' for v in s['runs'].values()) else 1)"; }
wait_stage() {  # $1 stage, $2 pid file
  while pgrep -f "manifests.py stage $M $1 " >/dev/null || running "$RUNS/$1/STATE.json"; do sleep 20; done
  inv "immediately after stage $1" > "$RUNS/$1/INVENTORY_END.txt"
  echo "$(date -u +%FT%TZ) stage $1 ended" >> $O/campaign/chain.log
}
wait_stage D $O/campaign/stage_D.pid
cd $W/ffimpl/research/function-family-campaign/impl
for S in S O; do
  test ! -e "$RUNS/$S" || { echo "refused: $RUNS/$S exists" >> $O/campaign/chain.log; exit 1; }
  inv "immediately before stage $S" > $O/campaign/INVENTORY_START_$S.staged.txt
  setsid nohup $PY -B manifests.py stage $M $S $W/campaign-6-impl $RUNS /usr/bin/ngspice $O/pdk-src > $O/campaign/stage_$S.log 2>&1 < /dev/null &
  echo $! > $O/campaign/stage_$S.pid
  echo "$(date -u +%FT%TZ) stage $S launched pid $!" >> $O/campaign/chain.log
  for i in $(seq 300); do [ -d "$RUNS/$S" ] && break; sleep 0.1; done
  cp $O/campaign/INVENTORY_START_$S.staged.txt "$RUNS/$S/INVENTORY_START.txt"
  wait_stage $S $O/campaign/stage_$S.pid
done
echo "$(date -u +%FT%TZ) all stages ended" >> $O/campaign/chain.log
