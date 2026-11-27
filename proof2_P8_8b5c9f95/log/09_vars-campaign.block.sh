M=campaign  B=evidence/combined-draw  R=evidence/combined-draw-result
X=EXCLUDED_SECOND.json  SIZES="NOT1=60 ANDOR3=32 XOR3=37"
H=$(grep -o 'sha256 [0-9a-f]\{64\}' /tmp/claude-0/-home-user-kernel-R/dbf013be-0c0e-5eee-ad1c-7c5e7bfb6d12/scratchpad/frz/f3/P8/log/08_check-list.out | tail -1 | cut -c8-)
