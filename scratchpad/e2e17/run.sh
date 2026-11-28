#!/bin/bash
export PATH=$HOME/.elan/bin:$PATH
V=/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/prefreeze2/venvA/bin/python
R=/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/e2e17
nohup bash -c "while [ ! -f $R/STOP_SAMPLER ]; do echo \"\$(date -u +%H:%M:%S) \$(df -B1M --output=avail /tmp | tail -1)\" >> $R/disk.log; sleep 20; done" >/dev/null 2>&1 &
L() { cd $R/clone$1/research/layered-networks && $V -B campaign_run17.py launch $R/plans/PLAN_K$2.json $R/out_K$2 jobs=4 template=$R/TEMPLATE_DRY.json; }
W() { [ -f $R/out_K$1/DRIVER_PID ] || { echo "K$1 has no driver"; return; }; cd $R/cloneA/research/layered-networks; while ! $V -B campaign_run17.py wait $R/out_K$1 580 > /dev/null 2>&1; do :; done; echo "K$1 DONE $(date -u +%H:%M:%S)"; }
echo "K07 (B, duplicate) launch $(date -u +%H:%M:%S)"; L B 07
sleep 90
echo "K02 (A, home) launch $(date -u +%H:%M:%S) seal branches: [$(git -C $R/seallog.git for-each-ref --format='%(refname:short)' | tr '\n' ' ')]"; L A 02
W 02
W 07
echo "K01 (A, audited) launch $(date -u +%H:%M:%S)"; L A 01
W 01
touch $R/STOP_SAMPLER; echo ALLDONE $(date -u +%H:%M:%S)
