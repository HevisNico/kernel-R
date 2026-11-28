#!/bin/bash
export PATH=$HOME/.elan/bin:$PATH
V=/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/prefreeze2/venvA/bin/python
R=/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/eqbrun
cd $R/clone/research/layered-networks
nohup bash -c "while [ ! -f $R/STOP_SAMPLER ]; do echo \"\$(date -u +%H:%M:%S) \$(df -B1M --output=avail /tmp | tail -1)\" >> $R/disk.log; sleep 30; done" >/dev/null 2>&1 &
for k in 01 02 03 04 05; do
  t0=$(date +%s); echo "K$k launch $(date -u +%H:%M:%S)"
  $V -B campaign.py launch test $R/TEST_TEMPLATE.json $R/plans/PLAN_K$k.json $R/out_K$k || { echo "K$k launch refused"; continue; }
  while ! $V -B campaign.py wait $R/out_K$k 580 > /dev/null 2>&1; do :; done
  echo "K$k ended $(( $(date +%s)-t0 ))s"
done
touch $R/STOP_SAMPLER; echo ALLDONE $(date -u +%H:%M:%S)
