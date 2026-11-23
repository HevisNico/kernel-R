# M4: instrument fixes, the D4 bound, and the Lean trace calibration (9801, 9802)

**Development only, nothing preregistered.** Reruns at the fixed instrument, on the same dev seeds, with the solo
comparison on (`lcal.py run SPEC OUT SEED solo=1`). Records in `dev/cal4_not1` and `dev/cal4_andor3`. One mismatch
draw each, no noise.

Decision recorded in `DECISIONS.md`: the either cell keeps the max rule for testError.

## Fix (a): every scan reads its own FIRE and its own silence (D3)

`instrument.ScanCell` now keeps a bracket made of the scan's own reads only:
- L, the largest silent state read; U, the smallest firing state read.
- The training reads only choose the first targets: the stop state first (where the cell already is), then the last
  silent training state.
- When needed, an ascent by half a stage above the stop, or a descent below the last silence.

**Result.** All 6 groups have native brackets. ANDOR3's both cell c1_0, which M3 could not measure, now has its own
FIRE at s = 3.9955 and its own silence at 3.9866, so s* = 3.99106 ± 0.0044. Its crossing is indeed just below its
stop stage, 4.

**Cost.** The extra reads cost about 4 to 8 slots per scan (26–30 slots, against 18–25 in M2).

## Fix (b): D4, parallel scans against a solo scan

After the parallel scans, each cell is scanned again alone, from where the parallel scan left it.

| Cell | Gate | s* parallel | s* solo | \|Δ\| (stage) | half brackets (par + solo) |
|---|---|---|---|---|---|
| NOT1 c1_0 | copy | 3.60252 | 3.60401 | 0.0015 | 0.0068 |
| ANDOR3 c1_0 | both | 3.99106 | 3.99280 | 0.0017 | 0.0106 |
| c1_1 | copy | 2.96079 | 2.97454 | **0.0138** | 0.0102 |
| c2_0 line 1 | either | 3.96079 | 3.96038 | 0.0004 | 0.0116 |
| c2_0 line 2 | either | 2.71869 | 2.71193 | 0.0068 | 0.0066 |
| c3_0 | copy | 3.87986 | 3.88156 | 0.0017 | 0.0097 |

**Two differences exceed their combined half brackets:** c1_1 by 0.0036, and c2_0 line 2 by 0.0002. NOT1 has one
cell, so its "parallel" scan is solo: its 0.0015 is the repeat spread alone.

**The term.** D4 is turned into a budget term, `H_D4 = ⌈k · d · |Δ|⌉` (k = 2 for a both cell), with the cell's own
largest |Δ|. It adds 17 (NOT1) and 21 to 137 (ANDOR3) score units to both errors.

**Runs without solo scans** need a constant. `calibration.json` leaves `d4_stage` unset: it is the owner's choice.
The largest difference seen is 0.0138 stage over 6 groups. Without a solo scan and without `d4_stage`, a cell is not
measured.

## A third fix, found in the trace check: the same-edge rule

- **What happened.** In one ANDOR3 lesson replay, the layer-1 copy cell's latch showed a "second rise" 0 ns (rounded)
  after its first: the same rising edge crossing 0.9 V twice. The Lean trace then had two emissions, so the training
  checker's decoder clause was false. The kernel and the mirror agreed on that.
- **The rule.** `records.py`: a second rise less than 1 µs after the first is dropped as the same edge, and every drop
  is listed in the record. It occurs once per ANDOR3 record (M2 and M4), nowhere else.
- **New runs** re-measure a second rise from 1 µs after the first (`CalNetwork.slot`).

## Lean

| File | Content |
|---|---|
| `lean/LayeredReadCheckAt.lean` | new module: public `one_read_checker_iff` / `one_read_checker_sound`, the read calibration at one external pattern. A new file that repeats the private proofs of `LayeredMonotoneCheckerProofs.lean`; no existing file changed. Negative controls rejected: soundness claimed at the wrong pattern; a `sorry` |
| `leancal.py` | the instance file at K0 and at K3 (see below) |
| `tests/check_leancal.py` | per file: it compiles; `computes` uses only propext, Classical.choice, Quot.sound; a lesson score raised by 10 000 is rejected; where validity is asserted true, testError 99999 is rejected |

**What a `leancal.py` file contains.**
- The fitted cells: gains, help, dose, trainError, testError, maxWrites.
- The measured traces **with scores**: each read's `measuredScore` is its mapped Z, and `scoreAt` holds the four masks'
  Z at the same slot.
- Theorems stating the mirror's values of `checkLayeredValid`, `checkLayeredTrainingCalibration`, `Checker.oneRead`
  at every input pattern, and the prediction against the expected function.
- When all of these are true, the recognition theorem, applied: `computes y : circuit.Trained train ∧ observed = expect`.

## Verdicts, kernel against mirror

| Instance | K | checkLayeredValid | training calibration | read calibration (every pattern) | recognition theorem | kernel |
|---|---|---|---|---|---|---|
| NOT1 (9801) | K0 | true | true | true | **proved**: trained, both outputs correct | accepted (1.1 s), agrees |
| | K3 | true | true | true | **proved** | accepted (1.1 s), agrees |
| ANDOR3 (9802) | K0 | false | true | true | not emitted | accepted (2.6 s), agrees |
| | K3 | false | true | true | not emitted | accepted (2.8 s), agrees |

The per-cell partial files (`Fit*.lean`, `Checker.cellValid` and `Cell.stop` of every cell at K0 and K3) are also
accepted and agree with the mirror: 4 theorems for NOT1, 18 for ANDOR3. The kernel and the mirror agree on every
value stated.

## Per cell (θ = 100 000)

| Instance | Cell | Gate | need | ε | H, H_drift, H_D4 | errors K0 (train/test) | K0 | errors K3 | K3 |
|---|---|---|---|---|---|---|---|---|---|
| NOT1 | c1_0 | copy | 4 | 0 | 29, 4, 17 | 303 / 303 | **eligible**, anchor +4217 | 3758 / 3758 | **room**, anchor +762 |
| ANDOR3 | c1_0 | both | 4 | 1 | 110, 10, 44 | 722 / 722 | not eligible: stop margin −499 | 8323 / 8323 | no room: −8100 (expected; not tuned) |
| | c1_1 | copy | 3 | 0 | 58, 3, 137 | 420 / 420 | **not eligible: stop margin −30** | 3444 / 3444 | no room: −3054 |
| | c2_0 | either | 4, 3 | 7 | 88, 11, 102 | 544 / 876 | not eligible: anchor (1,) −302 | 5129 / 9983 | no room: −9409 |
| | c3_0 | copy | 4 | 1 | 48, 3, 21 | 342 / 342 | **eligible**, anchor +1094 | 4010 / 4010 | no room: −2574 |

- **c1_1 at K0 is flipped by the D4 term.** In M3, without H_D4, its tightest margin was +23. With H_D4 = 137 (its
  own |Δ| = 0.0138) it fails by 30.
- **c1_0 fails at K0 as well as K3.** Its crossing is 0.009 stage below its stop, worth 224 units at its dose,
  against a K0 budget of 722.
- **Every lesson, replay and test read is within its error at both K.** The exact decoder and the submask and anchor
  clauses hold. Every failure is a room clause of `Cell.Valid`.

**Instances.** NOT1 is eligible at K0 and has room at K3, and the recognition theorem is proved on its measured trace
at both K. ANDOR3 is measured, but neither eligible at K0 nor with room at K3.

## Cost at the fixed instrument (machine-minutes, one core)

| Instance | Setup | Training | Tests | Parallel scans | Solo scans (D4 check only) | Total |
|---|---|---|---|---|---|---|
| NOT1 | 0.25 | 0.69 | 0.23 | 1.12 (22 slots) | 0.74 (12 slots) | 3.0 |
| ANDOR3 | 0.27 | 12.7 | 3.7 | 14.6 (53 slots) | 12.6 (58 slots) | 43.8 |

The totals equal the CPU time of the run. Without the solo check, a campaign instance would cost about 2.3 min (NOT1)
and 31.2 min (ANDOR3). The parallel scans cost about 16.5 s per slot on ANDOR3, against about 30 s for a lesson slot.
Against M2, the native-bracket fix adds 12 slots, about 3 min, on ANDOR3.

## Open

- **XOR3 has not been run**, so the inverter-fed both cells (offset scan reads) are untested.
- **The one-sided set and the both-lines check** are not implemented.
- **`d4_stage` for runs without solo scans** is not fixed (the owner's choice).
- **The timing-chain theorems** (chain dates, intrinsic delays, the front end) are in lean.py's file of a run. They
  are not merged into the calibrated file, and the recognition theorem used (`layered_recognition_at`) takes the
  arrival windows from `ReadCalibration` directly.
