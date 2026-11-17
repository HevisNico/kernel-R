#!/bin/bash
# Records `uptime -s` at the start, at each new stage folder of the rehearsal, every 10 minutes, and at the end.
W=/home/user/rehearsal2; L=/home/user/rehearsal2-meta/uptime.log; seen=""; n=0
echo "$(date -u +%FT%TZ) start uptime-s=$(uptime -s) pid=$$ sid=$(ps -o sid= -p $$ | tr -d ' ')" >> $L
while :; do
  now=$(ls -d $W/collected-* 2>/dev/null | xargs -rn1 basename | sort | tr '\n' ' ')
  if [ "$now" != "$seen" ]; then
    for d in $now; do case " $seen " in *" $d "*) ;; *) echo "$(date -u +%FT%TZ) stage-folder $d uptime-s=$(uptime -s)" >> $L;; esac; done
    seen="$now"
  fi
  n=$((n+1)); [ $((n % 20)) -eq 0 ] && echo "$(date -u +%FT%TZ) tick uptime-s=$(uptime -s)" >> $L
  if [ -f /home/user/rehearsal2-meta/DONE ]; then echo "$(date -u +%FT%TZ) end uptime-s=$(uptime -s) $(cat /home/user/rehearsal2-meta/DONE)" >> $L; exit 0; fi
  sleep 30
done
