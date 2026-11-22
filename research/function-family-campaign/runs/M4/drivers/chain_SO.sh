#!/bin/bash
# After stage D ends: D's END inventory, then S, then O, each once, in this order (brief section 2).
O=/home/user/owner-prep; W=$O/wt; PY=$O/venv312-dev/bin/python; M=M4; RUNS=$O/campaign-runs/$M
export PYTHONPATH=$W/campaign-6-followup/research/learned-dnf-circuit-campaign-6-followup/dev:$W/campaign-7-prep/research/learned-dnf-circuit-campaign-7-prep/dev:$W/ffimpl/research/function-family/dev:$W/ffimpl/research/function-family-campaign/impl:$W/ffnet/research/function-family-campaign/net
inv() { echo "taken $(date -u +%FT%TZ), $1"; echo "## uptime -s"; uptime -s; echo "## nproc"; nproc; echo "## free"; free; echo "## df"; df; }
running() { kill -0 "$(cat $O/campaign/stage_$1.pid)" 2>/dev/null || grep -q '"running"' $RUNS/$1/STATE.json; }
while running D; do sleep 20; done
inv "immediately after stage D" > $RUNS/D/INVENTORY_END.txt; echo "D ended $(date -u +%FT%TZ)"
cd $W/ffimpl/research/function-family-campaign/impl
for st in S O; do
  [ -e $RUNS/$st ] && { echo "refused: $RUNS/$st exists"; exit 1; }
  inv "immediately before stage $st" > $O/campaign/INVENTORY_START_$st.staged.txt
  nohup $PY -B manifests.py stage $M $st $W/campaign-6-impl $RUNS /usr/bin/ngspice $O/pdk-src > $O/campaign/stage_$st.log 2>&1 &
  echo $! > $O/campaign/stage_$st.pid; echo "$st launched $(date -u +%FT%TZ) pid $!"
  for i in $(seq 300); do [ -d $RUNS/$st ] && break; sleep 0.1; done
  [ -d $RUNS/$st ] && cp $O/campaign/INVENTORY_START_$st.staged.txt $RUNS/$st/INVENTORY_START.txt
  sleep 5; while running $st; do sleep 20; done
  [ -d $RUNS/$st ] && inv "immediately after stage $st" > $RUNS/$st/INVENTORY_END.txt; echo "$st ended $(date -u +%FT%TZ)"
done
echo ALL_DONE
