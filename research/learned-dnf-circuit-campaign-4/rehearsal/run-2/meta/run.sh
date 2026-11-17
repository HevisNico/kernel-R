#!/bin/bash
# The rehearsal of the frozen implementation (3156ee4), from a clean clone at that commit, detached from any session task.
cd /home/user/frozen-3156ee4
echo "$(date -u +%FT%TZ) start pid=$$ sid=$(ps -o sid= -p $$ | tr -d ' ') head=$(git rev-parse HEAD) uptime-s=$(uptime -s)"
PATH=/home/user/lean/bin:$PATH /home/user/owner-prep/venv312/bin/python -B research/learned-dnf-circuit-campaign-4/rehearsal.py \
  --ngspice /usr/bin/ngspice --pdk /home/user/campaign/pdk --work /home/user/rehearsal2 --report /home/user/rehearsal2-meta/REHEARSAL.json
rc=$?
echo "$(date -u +%FT%TZ) exit $rc"
echo "exit $rc at $(date -u +%FT%TZ)" > /home/user/rehearsal2-meta/DONE
