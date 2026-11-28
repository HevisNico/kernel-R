snap before
mkdir -p /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/work/n2
cd /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/work/n2
( set -e
  mkdir r
  cd r
  git init -q
  git -c user.name=x -c user.email=x@invalid commit -q --allow-empty -m x
  exit 1 )
echo "rc of the block=$?"
git -C r rev-parse -q --verify HEAD >/dev/null 2>&1 && echo 'NEGCHECK commit=yes' || echo 'NEGCHECK commit=no'
cd /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/work
snap after
cmp -s /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case3/.twin_before /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case3/.twin_after && echo 'NEGCHECK twin=same' || echo 'NEGCHECK twin=changed'
cmp -s /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case3/.gh_before /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/selftest/case3/.gh_after && echo 'NEGCHECK github=same' || echo 'NEGCHECK github=changed'
