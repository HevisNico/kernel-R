# M3: score mapping, guarded fit, budgets and per-cell verdicts (9801, 9802)

**Development only, nothing preregistered. No new simulation**: computed from the M2 records
(`dev/cal_not1`, `dev/cal_andor3`), one mismatch draw each, no noise.

## Files (new only)

- `fit.py`: per cell, everything listed in its docstring:
  - the guarded tuple (exact least squares over the cell's training states 0..need and the masks of its kind);
  - ε and the sensitivities;
  - the budgets at K0 and K3, with the deviation terms;
  - the Lean `Cell`;
  - the mirror of `Cell.Valid`, of the training calibration (every lesson read) and of the read calibration
    (every test and replay read, with the exact decoder fired = θ ≤ Z).
- `leanfit.py`: the partial Lean, with every measured cell as a `Cell` literal at K0 and K3. It states
  `Checker.cellValid` and each `Cell.stop` at the mirror's values, by `decide +kernel`.
- `tests/test_fit.py`: 5 tests. Exact solve; known budget values; `Cell.Valid` on hand-computed copy and both cells;
  the committed dev records reproduce their committed fit. `tests/test_cal.py` still passes (6).
- `dev/cal_*/fit.json`, `Fit*.lean`, `leanfit.json`.

**Against P.** `fit.solve` and `fit.read_budget` are bit-identical to campaign 5's frozen `predicted.py`
(`solve`, `read_budget` with `DECISION5`, taken from ecfcd1c1) on 3200 random cases (a one-off check, not committed).

## The scan deviations, in the budgets

| # | Deviation from scan6 | Effect on the budget | How it is bounded |
|---|---|---|---|
| D1 | target tolerance 10 µV instead of 2 µV | none: term 0. The bracket ends are the **measured** states of the reads, not their targets | by construction: s* and h are computed from measured u only (`reads[].s` in the record) |
| D2 | leak undershoot 4 % (not 30 µV), step up to 1.5 mV (not 1.2) | none: term 0. They change how a state is reached, not the state read | as D1; any change of u between the u window and the read is D5 |
| D3 | no ascent from s = 0: the bracket starts from training reads under network timing | none in the budget; it is a measurement rule | **a scan must have its own FIRE and its own silence**. Otherwise the cell is **not measured**: no widening, no re-scan |
| D4 | parallel scans | none | **not bounded** by these data: no solo comparison has been run. Open |
| D5 | drift of u between the u window (35 µs before T − 3 tu) and the read | H_drift = ⌈Σ_p d · max\|Δu_p\| / D_p⌉ over the run's read-only slots | measured: 0.2–0.3 µV per slot, so H_drift = 2–6 score units |

Each error is the gate's base budget (P's rule), plus H = ⌈h · d⌉ (or ⌈h · 2d⌉ for a both cell), plus H_drift.

## D3 applied: ANDOR3's both cell c1_0 is NOT MEASURED, which corrects M2

- **What M2 said.** c1_0 had s* = 3.9956, "0.004 stage below its stop stage".
- **What the scan did.** All 6 of its own reads were silent, the highest at s = 3.9911. Its bracket's upper end,
  4.0, is the training read at round 4, which fired under network timing.
- **So the crossing under the scan's own reads is only known to be above 3.9911.** "0.004 below the stop" was not
  established.
- **Under D3 the cell is not measured.** It is also expected to have no room at K3. It is not tuned and not
  re-scanned, as asked.
- **This is the no-ascent risk, realised on one of 6 groups.** A fix for the instrument, not applied here: read the
  training stop state again during the scan before bisecting.

## Per cell (θ = 100 000; scores in integer units)

| Instance | Cell | Gate | need (per group) | Fit: help, gains, dose | ε | sens /mV | K0: trainError / testError | K0 | K3: trainError / testError | K3 |
|---|---|---|---|---|---|---|---|---|---|---|
| NOT1 | c1_0 | copy | 4 | 0; 59193; 11351 | 0 | 8419 | 325 / 325 | **eligible**, tightest anchor +4273 | 3774 / 3774 | **room**, tightest anchor +824 |
| ANDOR3 | c1_0 | both | 4 | — | — | — | — | **not measured (D3)** | — | **not measured (D3)** |
| | c1_1 | copy | 3 | 0; 70431; 9946 | 0 | 7414 | 247 / 247 | **eligible**, tightest anchor +23 | 3278 / 3278 | **no room**: stop margin and anchor −3008 |
| | c2_0 | either | 4, 3 | 0; 40714, 59269; 14989 | 7 | 11206, 11076 | 436 / 768 | **not eligible**: anchor (1,) −97 | 5027 / 9888 | **no room**: stop margins −4356 and −790; anchors −9217 and −5651 |
| | c3_0 | copy | 4 | 0; 52667; 12164 | 1 | 8974 | 324 / 324 | **eligible**, tightest anchor +1000 | 4000 / 4000 | **no room**: stop margin and anchor −2676 |

**Budget breakdown.**

| Instance | Cell | Base train / test, K0 | Base train / test, K3 | H | H_drift |
|---|---|---|---|---|---|
| NOT1 | c1_0 | 253 / 253 | 3702 / 3702 | 69 | 3 |
| ANDOR3 | c1_1 | 223 / 223 | 3254 / 3254 | 22 | 2 |
| | c2_0 | 344 / 676 | 4935 / 9796 | 86 | 6 |
| | c3_0 | 271 / 271 | 3947 / 3947 | 50 | 3 |

- **K3 is dominated by the noise term.** At K3 the base budget is 3σ of campaign 5's noise constants, times the
  sensitivity: about 3300–4900 per port.
- **The binding clause is the stop margin** (equal to the anchor for a copy cell), as in the yield check. The
  crossings of c1_1 (2.973) and c3_0 (3.889) are 0.027 and 0.11 stage below their stop stages. K3 needs about 0.3–0.4
  stage at these doses.
- **The calibration checkers hold on every measured cell at K0 and K3.**
  - Every lesson residual is within trainError, every test and replay residual within testError.
  - Anchors and submask dominance hold.
  - The exact decoder (fired = θ ≤ Z) holds on every read.
  - The failures are all in `Cell.Valid`, which is the room.

**Instance verdicts.**
- NOT1 (9801) is eligible at K0 and has room at K3.
- ANDOR3 (9802) is not measured, because of c1_0, so it is neither eligible nor with room.

## A rule question for the owner: the either cell's testError

The proposal (M1, (c)) merges the family's two testing rules for an either cell by taking their max: 768 at K0.

The Lean clauses show the two-port budget is never used:
- an either read with both inputs present is a `FiringSlot`, which has no residual clause;
- the only `AdditiveSlot` reads of an either cell have no input.

With testError = the one-port rule (436 at K0), c2_0 would be **eligible at K0** (valid, no failing clause). It still
has **no room at K3** (stop margins and anchors fail).

**The verdicts above use the pre-written proposal rule.** Changing it is the owner's decision. It is reported here,
not applied.

## Mirror against the partial Lean

`FitNOT1.lean` and `FitANDOR3.lean` are accepted by the kernel (0.8 s and 0.9 s):
- for every measured cell at K0 and K3, `Checker.cellValid` and each `Cell.stop` equal the Python mirror's values;
- 4 theorems for NOT1, 14 for ANDOR3;
- the mirror's `Cell.Valid` and the kernel agree on all 8 cell × K cases.

Not checked in Lean yet: the calibration checkers on the traces (`checkLayeredTrainingCalibration`, read
calibration). That is M4.
