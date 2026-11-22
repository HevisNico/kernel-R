#!/bin/bash
# After stage D's process ends: D's END inventory, then stage S, then stage O, each once, as the brief's section 2.
O=/home/user/owner-prep; W=$O/wt; PY=$O/venv312-dev/bin/python; M=M2; RUNS=$O/campaign-runs/$M
export PYTHONPATH=$W/campaign-6-followup/research/learned-dnf-circuit-campaign-6-followup/dev:$W/campaign-7-prep/research/learned-dnf-circuit-campaign-7-prep/dev:$W/ffimpl/research/function-family/dev:$W/ffimpl/research/function-family-campaign/impl:$W/ffnet/research/function-family-campaign/net
inv() { echo "taken $(date -u +%FT%TZ), $1"; echo "## uptime -s"; uptime -s; echo "## nproc"; nproc; echo "## free"; free; echo "## df"; df; }
while kill -0 "$(cat $O/campaign/stage_D.pid)" 2>/dev/null; do sleep 10; done
grep -q '"running"' $RUNS/D/STATE.json && { echo "refused: D still has a running run"; exit 1; }
inv "immediately after stage D" > $RUNS/D/INVENTORY_END.txt
for st in S O; do
  test ! -e $RUNS/$st || { echo "refused: $RUNS/$st exists"; exit 1; }
  inv "immediately before stage $st" > $O/campaign/INVENTORY_START_$st.staged.txt
  cd $W/ffimpl/research/function-family-campaign/impl
  $PY -B manifests.py stage $M $st $W/campaign-6-impl $RUNS /usr/bin/ngspice $O/pdk-src > $O/campaign/stage_$st.log 2>&1 < /dev/null &
  echo $! > $O/campaign/stage_$st.pid
  for i in $(seq 100); do [ -d $RUNS/$st ] && break; sleep 0.1; done; cp $O/campaign/INVENTORY_START_$st.staged.txt $RUNS/$st/INVENTORY_START.txt
  wait $!; echo "stage $st exit $?" >> $O/campaign/drive.log
  inv "immediately after stage $st" > $RUNS/$st/INVENTORY_END.txt
done
echo "done $(date -u +%FT%TZ)" >> $O/campaign/drive.log
