# Campaign 4, amendment 3: exact arithmetic for every integer, the pinned interpreter, and a correction

Pushed alone on `research/learned-dnf-circuit-campaign-4`, after `PREDICTION.md` (commit `1596b36`), amendment 1
(commit `c14124f`) and amendment 2 (commit `d6a75a9`), before any further run of the cases of the kernel gate or of
the mutations of its checker mirror, and before any prediction code is committed to this branch. It is the owner's
decision. It corrects one item of amendment 2's account, fixes how every number that becomes an integer is computed
and rounded, and fixes the interpreter of every run. Nothing else in `PREDICTION.md`, amendment 1 or amendment 2
changes.

**No campaign seed (7501 and up) has been simulated, and nothing here depends on campaign-4 data.** Section 4 says
what was seen before this file was written.

## 1. Correction of amendment 2, section 6, item 4

On P0 (`research/learned-dnf-circuit/CALIBRATION.json`, #172, commit `49684af`), the exact least-squares solution
of layer 1's guarded tuple on the integer scores has the help **20735/2** for a and for b, exactly halfway between
two units. The code as it stood fitted in floats (`np.linalg.lstsq`) and rounded with `int(round(x))`, so the
floating-point error of the solver chose the unit:

| Environment | help of a | `epsilon` of a | training budget of a under `beta_0` | room of a's last silence |
|---|---|---|---|---|
| pinned: Python 3.12.3, numpy 2.3.5 | 10 367 | 692 | 778 | +4 |
| container default: Python 3.13.18, numpy 2.5.3 | 10 368 | 691 | 777 | +4 |

The room is +4 either way: on P0, a help one unit lower lowers the guarded score by one unit and raises the residual bound,
so the budget, by one unit. Amendment 2's sentence "692 would give +3" is **wrong**, and its "the outgoing director's
figure is unexplained" is withdrawn: the outgoing director computed P0 at 14:01:04 UTC with the pinned interpreter
(`/home/user/owner-prep/venv312/bin/python`), where 692 is the result (the independent review's reading of its
transcript). The 691 of the case builder and of the independent review came from the container's default Python
3.13.18 with numpy 2.5.3.

The outputs pushed to the work branch `research/learned-dnf-circuit-campaign-4-wip` at commits `574dae3`, `768e991`
and `7e263ef` were computed outside the pinned environment. Under the pinned one, their verdicts and every failing
condition they list are unchanged (the Python logs are byte-identical), but four of their files are not reproducible:
`Gate4Cases.lean` and `CASES.json` of the cases, `MirrorMutations.lean` and `MUTATIONS.json` of the mutations.

## 2. Exact arithmetic for everything that becomes an integer

This replaces "rounded to the nearest unit" (`PREDICTION.md`, Guarded tuple) and completes "One set of numbers"
(`PREDICTION.md`, The kernel gate):

1. **Every measure is converted exactly to a rational**: a float is taken at its exact binary value (as
   `fractions.Fraction(x)`), a decimal written in a file at its exact decimal value.
2. **The guarded tuple** is the exact rational solution of the normal equations of the least-squares fit (the same
   reads, stages and unknowns as before), on the integer scores, then rounded.
3. **`epsilon`, the sensitivities, the budgets, the integer scores and the dates** are computed in rationals.
4. **Rounding to the nearest is to the nearest, ties to even** (Python's `round` on an exact `Fraction`). This
   applies to the guarded tuple, to the integer scores (`Z` times 100 000) and to the dates (0.0001 unit).
5. **The noise terms are rounded up exactly.** For `beta_0`, the least integer at least `0.030 mV x s`. For
   `beta_3`, the least integer `m >= 0` with `m >= 3 x sigma`; for a read of one port, `m^2 >= 9 s^2 (w^2 + b^2 + n
   d^2)`; for a read of two ports, whose terms `x = 3 sigma_1` and `y = 3 sigma_2` are added linearly as
   `PREDICTION.md` says, `m >= x + y`, decided from the rational squares `X = x^2` and `Y = y^2` without floats:
   `m^2 >= X`, `m^2 + X - Y >= 0` and `(m^2 + X - Y)^2 >= 4 m^2 X`.
6. **Floats remain only where nothing becomes an integer**: the geometric fit and its validation residuals (M5).
   The byte identity of `PREDICTED.json` is checked under the pinned environment (section 3).

**The effect of the tie rule on P0 is known in advance**: 20735/2 rounds to 10 368, which gives a's `epsilon` 691
and training budget 777 under `beta_0`. Rounding half up would give the same. The room of the last silence is +4
under any rule, so no verdict of P0 depends on the choice.

## 3. The interpreter

Every run of the campaign code (prediction, cases, mutations, gate, rehearsal, manifests, analysis) uses the pinned
interpreter of the launch kit, `/home/user/owner-prep/venv312/bin/python`: Python 3.12.3 (SHA-256
`e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f`) with numpy 2.3.5 (SHA-256 of its `RECORD`
file `064003bdb6f9f7bb06e46e07cc3398cbfdc3c114dfe55b89d239e564917be2fb`). `check.sh`, the CI and `rehearsal.py`
record the interpreter and the numpy version, and refuse any other.

## 4. What was seen before this file (2026-11-16)

1. The outputs of section 1 (cases at `574dae3` and `768e991`, mutations at `7e263ef`), all reported to the
   independent review, were computed under the container's default Python 3.13.18 with numpy 2.5.3.
2. After installing the pinned environment (the kit's `launch.py identity` passing on all seven pins), the draft
   `check.sh` regenerated those outputs under the pinned interpreter for a byte comparison; it failed. The
   difference was traced to the tie of section 1: the solver's results were 10367.500000000047 (default) and
   10367.499999999985 (pinned) for a's help, and 10367.500000000044 and 10367.50000000002 for b's. Every other value
   that differed was a float that becomes no integer (58 values, relative difference at most 7e-15). The verdicts and
   failing-condition lists were identical. This was reported and nothing was run further.
3. The independent review then computed the exact rational solution on `CALIBRATION.json`'s integer scores: layer 1,
   help 20735/2, gains 154645/4 and 1082755/28, dose 53755/28; c, help 10000, gains 2153035/28 and 2153475/28, dose
   103415/28. Only the layer-1 help is a tie. The independent review also found in the outgoing director's
   transcript the pinned run of P0 at 14:01:04 UTC.
4. No case, mutation or prediction has been run under the rules of section 2 before this file was pushed.
