#!/bin/bash
# Task 1: the frozen analysis of the rehearsal. Fetch the 12 roots by name (tips), restore every TRANSPORT_SPLIT.txt
# line, then analysis.py rehearsal twice, as FREEZE.txt writes it. Pushes nothing.
set -u
A=/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/rehearsal/analysis
C=/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/rehearsal/kernel-R
L=$C/research/layered-networks
PY=/tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/prefreeze2/venvA/bin/python
export PATH=$HOME/.elan/bin:$PATH
GH=https://github.com/HevisNico/kernel-R
echo "### clone $(git -C $C rev-parse HEAD); porcelain: $(git -C $C status --porcelain --untracked-files=all | tr '\n' ' ')"
# 1. the 12 roots, each branch's tip fetched by name, extracted to $A/R/K<nn>/out_K<nn>
[ ! -e $A/R ] || { echo "STOP: $A/R exists"; exit 1; }
mkdir $A/R
for k in 01 02 03 04 05 06 07 08 09 10 11 12; do
  git -C $A/roots.git fetch -q $GH +refs/heads/evidence/combined-rehearsal-K$k:refs/heads/K$k || { echo "STOP: fetch K$k failed"; exit 1; }
  t=$(git -C $A/roots.git rev-parse K$k); r=$(git ls-remote $GH refs/heads/evidence/combined-rehearsal-K$k | cut -f1)
  [ "$t" = "$r" ] || { echo "STOP: K$k fetched $t, GitHub tip $r"; exit 1; }
  echo "K$k tip $t"
  mkdir $A/R/K$k && git -C $A/roots.git archive K$k | tar -x -C $A/R/K$k || { echo "STOP: extract K$k"; exit 1; }
done
# 2. the transport splits, restored before anything else
for f in $A/R/K*/TRANSPORT_SPLIT.txt; do
  d=$(dirname $f)
  while read -r sha size n path; do
    [ -n "$sha" ] || continue
    out=$d/$path
    [ ! -e "$out" ] || { echo "STOP: $out exists before the restore"; exit 1; }
    for i in $(seq 0 $((n - 1))); do p=$(printf '%s.transport-part-%03d' "$out" $i); [ -f "$p" ] || { echo "STOP: missing $p"; exit 1; }; cat "$p"; done > "$out"
    s=$(sha256sum "$out" | cut -c1-64); z=$(stat -c %s "$out")
    [ "$s" = "$sha" ] && [ "$z" = "$size" ] || { echo "STOP: $path restored sha $s size $z, not $sha $size"; exit 1; }
    for i in $(seq 0 $((n - 1))); do rm "$(printf '%s.transport-part-%03d' "$out" $i)"; done
    echo "restored $path: $n parts, sha256 $s, $z bytes"
  done < $f
done
left=$(find $A/R -name '*.transport-part-*' | wc -l); [ "$left" = 0 ] || { echo "STOP: $left parts left"; exit 1; }
for f in $A/R/K*/NOT_PUBLISHED.txt; do echo "NOT_PUBLISHED ($f):"; cat $f; done
# 3. analysis.py rehearsal, twice, as FREEZE.txt writes it
ROOTS=$(for k in 01 02 03 04 05 06 07 08 09 10 11 12; do printf '%s ' $A/R/K$k/out_K$k; done)
cd $L
for run in 1 2; do
  echo "### analysis run $run: python -B analysis.py rehearsal $A/OUT$run $ROOTS draw=$A/DRAW_REHEARSAL.json excluded=EXCLUDED.json"
  $PY -B analysis.py rehearsal $A/OUT$run $ROOTS draw=$A/DRAW_REHEARSAL.json excluded=EXCLUDED.json > $A/analysis_run$run.log 2>&1
  echo "### analysis run $run exit=$?"; tail -c 3000 $A/analysis_run$run.log
done
if [ -f $A/OUT1/RESULTS.json ] && [ -f $A/OUT2/RESULTS.json ]; then
  cmp $A/OUT1/RESULTS.json $A/OUT2/RESULTS.json && cmp $A/OUT1/SHA256SUMS $A/OUT2/SHA256SUMS && diff -r $A/OUT1 $A/OUT2 >/dev/null && echo "### the two runs are byte-identical" || echo "### THE TWO RUNS DIFFER"
  sha256sum $A/OUT1/RESULTS.json
fi
echo "### porcelain after: $(git -C $C status --porcelain --untracked-files=all | tr '\n' ' ')"
