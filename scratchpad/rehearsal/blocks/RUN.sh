set -u
cd /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/rehearsal/work
echo "### 1 vars"
. /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/rehearsal/blocks/1_vars.sh
rc=$?; echo "### rc=$rc"
[ $rc = 0 ] || { echo "### STOPPED at vars"; exit $rc; }
echo "### 2 vars-rehearsal"
. /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/rehearsal/blocks/2_vars-rehearsal.sh
rc=$?; echo "### rc=$rc"
[ $rc = 0 ] || { echo "### STOPPED at vars-rehearsal"; exit $rc; }
echo "### 3 announce"
. /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/rehearsal/blocks/3_announce.sh
rc=$?; echo "### rc=$rc"
[ $rc = 0 ] || { echo "### STOPPED at announce"; exit $rc; }
echo "### 4 draw"
. /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/rehearsal/blocks/4_draw.sh
rc=$?; echo "### rc=$rc"
[ $rc = 0 ] || { echo "### STOPPED at draw"; exit $rc; }
