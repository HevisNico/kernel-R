set -u
cd /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/work
snap() { git --git-dir /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/github_twin.git for-each-ref --format='%(refname) %(objectname)' > /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case6/.twin_$1; git ls-remote https://github.com/HevisNico/kernel-R 'refs/heads/evidence/combined-*' > /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case6/.gh_$1; }
echo "### 1 ok (pass)"
. /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case6/1_ok.block.sh > /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case6/1_ok.out 2>&1; echo "rc=$?" >> /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case6/1_ok.out
tail -4 /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case6/1_ok.out
grep -qx "rc=0" /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case6/1_ok.out || { echo "STOPPED: step 1 ok failed"; exit 1; }
echo "### 2 neg-refuses (neg)"
. /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case6/2_neg-refuses.block.sh > /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case6/2_neg-refuses.out 2>&1; echo "rc=$?" >> /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case6/2_neg-refuses.out
tail -4 /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case6/2_neg-refuses.out
