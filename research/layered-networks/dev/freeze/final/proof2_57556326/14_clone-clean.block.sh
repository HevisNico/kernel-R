x=$(git -C /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P7/kernel-R status --porcelain --untracked-files=all | grep -vx '?? research/circuit/pdk' || true)
if [ -z "$x" ]; then echo "the clone is clean (only the PDK link)"; else echo "THE CLONE IS NOT CLEAN:"; echo "$x"; fi
( exit $([ -z "$x" ] && echo 0 || echo 1) )
