O="$(git -C /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/kernel-R log -1 --format='%an %ae' origin/main)"
echo "the global identity is the owner's: $([ "$(git config --global user.name) $(git config --global user.email)" = "$O" ] && echo yes || echo no)"
N=0
for r in $(git --git-dir /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/github_twin.git for-each-ref --format='%(refname)'); do
  a="$(git --git-dir /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/github_twin.git log -1 --format='%an %ae' $r)"; c="$(git --git-dir /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/github_twin.git log -1 --format='%cn %ce' $r)"; n=$(git --git-dir /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/github_twin.git rev-list --count $r)
  if [ "$a" = "$O" ] && [ "$c" = "$O" ] && [ "$n" = 1 ]; then echo "$r: one commit, the owner's"; else echo "$r: NOT one commit of the owner's"; N=1; fi
done
[ $(git --git-dir /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/github_twin.git for-each-ref | wc -l) = 4 ] || { echo 'the twin does not hold exactly 4 refs'; N=1; }
( exit $N )
