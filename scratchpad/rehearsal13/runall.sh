#!/bin/bash
export PATH=$HOME/.elan/bin:$PATH
V=/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/prefreeze2/venvA/bin/python
cd /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/rehearsal13/tree/research/layered-networks
for k in 01 02; do
  t0=$(date +%s)
  $V -B campaign_run13.py launch /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/rehearsal13/plans/PLAN_K$k.json /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/rehearsal13/out_K$k jobs=4 template=/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/rehearsal13/TEMPLATE_REHEARSAL.json || { echo "K$k launch failed"; continue; }
  while ! $V -B campaign_run13.py wait /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/rehearsal13/out_K$k 580 > /dev/null; do :; done
  echo "K$k ended $(( $(date +%s) - t0 ))s $($V -B campaign_run13.py status /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/rehearsal13/out_K$k | tr '\n' ' ')"
done
echo ALLDONE
