#!/bin/bash
export PATH=$HOME/.elan/bin:$PATH
cd /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/d4check/repo/research/layered-networks
for k in 01 02 03 04 05 06; do
  t0=$(date +%s)
  /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/prefreeze2/venvA/bin/python -B campaign_run12.py launch /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/d4check/plans/PLAN_K$k.json /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/d4check/out_K$k jobs=4 || { echo "K$k launch failed"; continue; }
  while ! /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/prefreeze2/venvA/bin/python -B campaign_run12.py wait /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/d4check/out_K$k 580 > /dev/null; do :; done
  echo "K$k ended $(( $(date +%s) - t0 ))s $(/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/prefreeze2/venvA/bin/python -B campaign_run12.py status /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/d4check/out_K$k | tr '\n' ' ')"
done
echo ALLDONE
