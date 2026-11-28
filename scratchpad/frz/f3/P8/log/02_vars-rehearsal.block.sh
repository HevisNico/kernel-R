M=rehearsal  B=evidence/combined-rehearsal2-draw  R=evidence/combined-rehearsal2-draw-result
X=EXCLUDED_REHEARSAL2.json  SIZES="NOT1=6 ANDOR3=6 XOR3=6"
H=$(grep -o 'sha256 [0-9a-f]\{64\}' /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/log/01c_check-rehearsal2-list.out | tail -1 | cut -c8-)
