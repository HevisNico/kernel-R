set -u
cd /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/work
snap() { git --git-dir /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/github_twin.git for-each-ref --format='%(refname) %(objectname)' > /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case4/.twin_$1; git ls-remote https://github.com/HevisNico/kernel-R 'refs/heads/evidence/combined-*' > /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case4/.gh_$1; }
echo "### 1 identity (pass)"
. /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case4/1_identity.block.sh > /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case4/1_identity.out 2>&1; echo "rc=$?" >> /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case4/1_identity.out
tail -4 /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case4/1_identity.out
grep -qx "rc=0" /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case4/1_identity.out || { echo "STOPPED: step 1 identity failed"; exit 1; }
