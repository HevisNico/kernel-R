# Amendment 4: record of the report generator change of commit 9efb1ff

This file records a change made before any execution of the
certification analysis on results. It changes no rule of `PREDICTION.md`.

## The change

- **Bound `B`.** `PREDICTION.md` adds `eps_kappa` to `B` when read `r`
  has a FIRE. The first version of `cert_analyze.py` omitted it when
  `r = 0`. Commit `9efb1ff` adds it in that case too. The change makes
  `B` larger, never smaller, and brings the code in line with the
  registered rule.
- **Traces section.** The report now states where the compact traces are
  kept (private repository), that the recorded SHA-256 is that of the
  compact trace, that `cert_run.py` is identical to the file of commit
  `5b9d75f` (checked by hash), and that noisy runs are not replayed by
  their seed.

The functions `calibrate` and `predict` were not changed by that commit.

## Dates

GitHub received the push of commit `9efb1ff` on 2026-11-12 at
16:14:22 UTC: before the first execution of `certify` and before any
result of stage 3. The predicted needs of the 200 ports were pushed at
16:34:59 UTC (commit `b44de8d`).

The first four runs of stage 3 were started at 16:35:04 UTC, before this
amendment was written. When this amendment is pushed, those runs are
still running: no result of stage 3 exists, and `certify` has not been
executed. This amendment is pushed after commit `9efb1ff`, to record it
among the amendments.
