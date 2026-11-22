#!/bin/bash
S=$1; O=/home/user/owner-prep; F=$O/campaign-runs/M5/$S/STATE.json
for i in $(seq 57); do grep -q '"ended_utc"' $F && break; sleep 10; done
if grep -q '"ended_utc"' $F; then
  { echo "taken $(date -u +%FT%TZ), after stage $S ended"; echo "## uptime -s"; uptime -s; echo "## nproc"; nproc; echo "## free"; free; echo "## df"; df; } > $O/campaign-runs/M5/$S/INVENTORY_END.txt
  python3 -c "
import json;d=json.load(open('$F'));print('$S',d['started_utc'],d['ended_utc'])
for k,v in d['runs'].items(): print(k,v['status'],v.get('exit'),round(v['wall_s']),v['limit_s'],round(v['share_of_limit'],3))"
else date -u; python3 -c "import json;d=json.load(open('$F'));print('still', {k:v['status'] for k,v in d['runs'].items()})"; fi
