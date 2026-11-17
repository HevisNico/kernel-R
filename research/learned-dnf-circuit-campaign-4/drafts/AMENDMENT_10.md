# Campaign 4, amendment 10: the stage caps of `BEFORE_M.md` and the time limits at each stage

Pushed alone on `research/learned-dnf-circuit-campaign-4`, after `PREDICTION.md` (commit `1596b36`) and amendments
1 to 9 (commits `c14124f`, `d6a75a9`, `41cf88b`, `a167f3c`, `6c5630f`, `424f6f9`, `53d50f3`, `d380da6`, `184b595`),
after the rehearsal's record (`REHEARSAL.json`, commit `9d96744`) and before `BEFORE_M.md`. It is the owner's
decision. It changes neither the code nor `BEFORE_M.md`, and nothing else in `PREDICTION.md` or amendments 1 to 9.

Amendment 5, section 3, says that the stage caps recorded in `BEFORE_M.md` are computed with the time limits of its
section 2, which after the rehearsal are those of the rehearsal's limits basis. The frozen code (`plan.py before-m`)
computes them otherwise. This file states what `BEFORE_M.md` records and where each limit is computed:

1. **`BEFORE_M.md`'s stage caps** are computed with the time limit of each run at 1.3 times its expected cost
   (amendment 5, section 2, item 5), so they are **upper bounds** of the stages' caps.
2. **Each stage's actual time limits and cap** are computed by the frozen code at its manifest, with
   `REHEARSAL.json`'s limits basis (amendment 5, section 2, item 4), and recorded in the stage's run list
   (`STAGE_<name>_RUNS.json`) and its manifest (`CAMPAIGN_<name>.json`).
3. **`I` is sized by the expected cost alone** (amendment 5, section 2), and is 12 either way: with the costs of
   `BEFORE_M.md`, 12 instances need 7.61 h of expected compute and 13 would need 8.07 h, with or without the
   rehearsal's limits.
4. **Under the limits basis** (calibration deck 0.549, run without noise 0.700, untrained control run 0.363, noisy run
   under the injected model 0.782), the frozen code gives, for `I` = 12: M, 24 calibration decks at 660 s each, cap
   5 360 s; Q, at need 4, the runs without noise at 770 s and the untrained control run at 180 s, cap 3 752 s; N1, N2
   and N3, at need 4, the noisy runs at 1 340 s, cap 6 412 s each. The real limits of Q's and N's runs come later,
   from the needs in `PREDICTED.json`.
5. **`reuse_trip: false`** in `BEFORE_M.md` means **not applicable**: there is no extraction under the injected default
   (amendment 7, section 2, item 2), and the frozen code writes the Boolean for that case.
