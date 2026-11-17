#!/usr/bin/env bash
# Campaign 4, amendment 8: the detached wrapper of the completion of the rehearsal's attempt 2. It pins numpy's
# OpenBLAS to its SkylakeX kernel (complete_rehearsal.py refuses without it), records `uptime -s` at the start, at
# each collected stage, every 10 minutes and at the end, and writes LOG_DIR/DONE with the exit code.
#
#   setsid nohup bash complete_rehearsal.sh ATTEMPT_DIR META_DIR WORK_DIR REHEARSAL.json LOG_DIR > /dev/null 2>&1 < /dev/null &
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
attempt=$1 meta=$2 work=$3 report=$4 log=$5
mkdir "$log" || exit 1
export OPENBLAS_CORETYPE=SkylakeX
export PATH=/home/user/lean/bin:$PATH
(
  echo "$(date -u +%FT%TZ) start uptime-s=$(uptime -s) pid=$BASHPID"
  seen="" n=0
  while [[ ! -f "$log/DONE" ]]; do
    now=$(ls -d "$work"/collected-* 2>/dev/null | xargs -rn1 basename | sort | tr '\n' ' ')
    for d in $now; do
      case " $seen " in *" $d "*) ;; *) echo "$(date -u +%FT%TZ) stage-folder $d uptime-s=$(uptime -s)" ;; esac
    done
    seen=$now n=$((n + 1))
    (( n % 20 == 0 )) && echo "$(date -u +%FT%TZ) tick uptime-s=$(uptime -s)"
    sleep 30
  done
  echo "$(date -u +%FT%TZ) end uptime-s=$(uptime -s) $(cat "$log/DONE")"
) >> "$log/uptime.log" 2>&1 &
echo "$(date -u +%FT%TZ) start pid=$$ sid=$(ps -o sid= -p $$ | tr -d ' ') head=$(git -C "$here" rev-parse HEAD) uptime-s=$(uptime -s)" > "$log/completion.log"
/home/user/owner-prep/venv312/bin/python -B "$here/complete_rehearsal.py" --attempt "$attempt" --meta "$meta" \
  --ngspice /usr/bin/ngspice --pdk /home/user/campaign/pdk --work "$work" --report "$report" >> "$log/completion.log" 2>&1
rc=$?
echo "$(date -u +%FT%TZ) exit $rc" >> "$log/completion.log"
echo "exit $rc at $(date -u +%FT%TZ)" > "$log/DONE"
wait
