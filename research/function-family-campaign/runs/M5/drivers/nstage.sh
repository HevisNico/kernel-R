#!/bin/bash
# usage: nstage.sh S PREV   (launches stage S once, after the per-stage checks)
S=$1; PREV=$2
O=/home/user/owner-prep; W=$O/wt; PY=$O/venv312-dev/bin/python; M=M5
export PYTHONPATH=$W/campaign-6-followup/research/learned-dnf-circuit-campaign-6-followup/dev:$W/campaign-7-prep/research/learned-dnf-circuit-campaign-7-prep/dev:$W/ffimpl/research/function-family/dev:$W/ffimpl/research/function-family-campaign/impl:$W/ffnet/research/function-family-campaign/net
ST=$W/ffpred/research/function-family-campaign/predicted/stages; JF=$ST/JOBS_${S}_$M.json
python3 -c "import json;s=json.load(open('$O/campaign-runs/$M/$PREV/STATE.json'))['runs'];assert 'running' not in [v['status'] for v in s.values()]" || { echo "STOP: $PREV still running"; exit 1; }
[ "$(pgrep -c ngspice)" = 0 ] || { echo "STOP: ngspice running"; exit 1; }
free_gb=$(df -BG --output=avail / | tail -1 | tr -dc 0-9); [ "$free_gb" -ge 8 ] || { echo "STOP: disk $free_gb G"; exit 1; }
test ! -e $O/campaign-runs/$M/$S || { echo "STOP: $S exists"; exit 1; }
python3 -c "import json,os,sys;d=json.load(open('$JF'));sys.exit(any(os.path.exists('$O/campaign-runs/$M/'+j['id']) for w in d['waves'] for j in w))" || { echo "STOP: a job folder exists"; exit 1; }
echo "checks OK: $PREV over, 0 ngspice, ${free_gb}G free, folders absent"
{ echo "taken $(date -u +%FT%TZ), immediately before stage $S"; echo "## uptime -s"; uptime -s; echo "## nproc"; nproc; echo "## free"; free; echo "## df"; df; } > $O/campaign/INVENTORY_START_$S.staged.txt
cd $O/campaign
setsid nohup $PY -B -c "import dosedev2; dosedev2.many('$JF')" > $O/campaign/many_$S.log 2>&1 < /dev/null &
for i in $(seq 100); do [ -d $O/campaign-runs/$M/$S ] && break; sleep 0.1; done; cp $O/campaign/INVENTORY_START_$S.staged.txt $O/campaign-runs/$M/$S/INVENTORY_START.txt && echo "inventory copied"
sleep 4; python3 -c "import json;d=json.load(open('$O/campaign-runs/$M/$S/STATE.json'));print('$S started',d['started_utc'],{k:(v['status'],v['limit_s']) for k,v in d['runs'].items()})"; echo "ngspice: $(pgrep -c ngspice)"
