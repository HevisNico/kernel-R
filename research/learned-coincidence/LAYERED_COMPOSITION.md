# Layered composition: per-pattern recognition, the timing chain, and inverters

These files sit on top of the layered theory (`LayeredMonotone*.lean`) and the inverter front end
(`InverterTarget.lean`, `Inverters.lean`). The existing files are not modified. The run is
`python3 -B check_layered_composition.py`, with the pinned Lean 4.35.0 on `PATH`. It:

- builds the 15 new modules;
- runs `LayeredCompositionAudit.lean`, which checks that the allowed axioms are only `propext`,
  `Classical.choice` and `Quot.sound`, and checks the exact types of the main theorems;
- requires 16 weakened copies to fail.

## What is proved

| Theorem | Statement |
| --- | --- |
| `layered_recognition_at` | Validity, the training calibration and the read calibration **at one external pattern `x`** imply `Trained` and `observed = predict x`. The private lemmas of `LayeredMonotoneRecognition.lean` are copied unchanged. |
| `read_calibration_iff` | `ReadCalibration` at `x` holds exactly when three things hold: the external mask is `x`, `LayerReads` holds (the reads without their arrival windows), and `ArrivalWindows` holds. |
| `chain_windows`, `layered_recognition_chained` | `ChainDates s e f` (constants only), `Scheduled s` and `PulseWindows s e f` imply every arrival window, and hence the decisions. This is the general form with declared windows. |
| `layered_recognition_from_latency` | Per-cell latencies and the external window give the pulse windows, with `e = latencyLow λmin` and `f = latencyHigh w λmax`. The whole calendar then follows from constants. The output pulse lies in `[s L + λmin L, s L + λmax L]`. |
| `cell_latency_of_last_arrival` | The last-arrival form `[max(start, last arrival) + λmin, start + λmax]` implies the latency premise used. |
| `layered_recognition_from_deadlines` | The deadline-only instance, with `λmin = 0` and `λmax = deadline`. Its latencies come from the decoder clause of each read. |
| `latency_of_intrinsic`, `layered_recognition_from_intrinsic` | Suppose a cell's intrinsic delay, from the later of its start and its last arrival, lies in `[dmin, dmax]`, and its arrivals lie in its read window. Then the latency law holds with `λmin = dmin` and any `λmax ≥ skew + dmax`. The chain built on `λmax = skew + dmax` derives each layer's window first and then that layer's latency. |
| `chain_dates_checker_sound`, `chain_dates_checker_complete` | `checkChainDates` decides `ChainDates`. |
| `training_calibration_chained`, `layered_recognition_fully_chained` | The same chain for every training lesson, with a lesson clock `σ (layer, cell, group, round)`. No arrival window is assumed in training or at test. |
| `layered_inverters_compute` | For **any** valid layered cascade on `2 M` lines, read through the inverter front end at `y`, the answer is `predict (rails y)`. |
| `layered_inverters_chained` | The same with the front end as layer 0 of the chain: `s 0 = start + emitEarly`, and its width `w` bounds both the inverter input window and the inverter emission spread. |
| `every_function_layered_with_inverters` | Every Boolean function is computed by some valid layered cascade behind the inverters. |

### Checkers

- **Sound and complete:** `checkChainDates`. The four checkers of `LayeredMonotoneCheckerTargets.lean`
  (`checkLayeredValid`, `checkLayeredSeparation`, `checkLayeredTrainingCalibration`,
  `checkLayeredReadCalibration`) are also sound and complete, proved on main and reused unchanged.
- **Sound only, with no completeness proof:** `checkScheduled`, `checkLatencies`, `checkExternalWindow`,
  `checkPulseWindows`, `checkTrainingChainDates`, `checkTrainingScheduled`, `checkTrainingPulses`,
  `checkIntrinsicDelay` and `checkIntrinsicDelays`, `checkInverterRead`, `checkLayeredFront`.
  A `false` from one of these does not prove that the premise fails.

## The quantities and the inequalities they must satisfy

Layer `ℓ = 1..L`. Layer 0 is the external input, or the inverter front end.

1. **Slot timing per layer** (`SlotTiming.Valid`, part of `Cascade.Valid`): `0 ≤ skew ℓ ≤ deadline ℓ < duration ℓ`
   and `0 < deadline ℓ`.
2. **Latency per layer, a property of one cell:** `λmin ℓ ≤ λmax ℓ`. Every emission of a layer-`ℓ`
   read lies in `[s ℓ + λmin ℓ, s ℓ + λmax ℓ]`. This is checked on the trace by `checkLatencies`.
3. **External window:** every external pulse lies in `[s 0, s 0 + w]`.
4. **Wire delay `δ ≥ 0`** (part of `Node.Valid`) and **the chain**, on constants, checked by `checkChainDates`:
   - into layer 1: `s 1 ≤ s 0 + δ` and `s 0 + w + δ ≤ s 1 + skew 1`;
   - into layer `ℓ + 1`: `s (ℓ+1) ≤ s ℓ + λmin ℓ + δ` and `s ℓ + λmax ℓ + δ ≤ s (ℓ+1) + skew (ℓ+1)`.

   With equal delays, the downstream read window must absorb the upstream latency spread:
   `λmax ℓ − λmin ℓ ≤ skew (ℓ+1)`.
5. **The assumption on λmax.** λmax must cover the total arrival spread inside the read window
   plus the cell's intrinsic delay: **`skew ℓ + dmax ℓ ≤ λmax ℓ`**, and `λmin ℓ ≤ dmin ℓ`. Here
   `[dmin, dmax]` bounds the delay from the later of the read start and the last arrival to the
   emission. This is proved in `latency_of_intrinsic`. A measured cell value is checked by
   putting `λmax = skew + dmax` into `checkChainDates`, as `layered_recognition_from_intrinsic` does.
   On main's example, `dmin = dmax = 1` and `skew = 0` give `λmax = 1` (`example_from_intrinsic`).
6. **Inverters:** `0 ≤ window ≤ emitEarly < emitLate` (`InverterTiming.Valid`). The direct rails are
   delayed by `emitEarly`, so `s 0 = start + emitEarly`. Also `window ≤ w` and `emitLate − emitEarly ≤ w`.
   **How the front end enters the chain:** it is layer 0, with window `[s 0, s 0 + w]`.
   - The direct rails arrive at `external + emitEarly`, within `[start + emitEarly, start + emitEarly + window]`.
   - The inverter pulses lie in `(start + emitEarly, start + emitLate]`.
   - So with `s 0 = start + emitEarly`, both lie in `[s 0, s 0 + w]` once `w ≥ window` and
     `w ≥ emitLate − emitEarly` (`layered_front_window`, from `front_end_window`).

   Layer 1's chain inequalities `s 1 ≤ s 0 + δ` and `s 0 + w + δ ≤ s 1 + skew 1` then give
   `w ≤ skew 1 + (s 1 − s 0 − δ) ≤ skew 1`. **So `emitLate − emitEarly ≤ skew 1` and `window ≤ skew 1`
   are needed.** With unequal delays into layer 1, the spread of those delays is added on the left.
   This is the layered form of `windowFits`/`spreadFits` in `inverters_compute`.
7. **Training lessons:** the inequalities of item 4 hold per lesson, with `σ` in place of `s`.

**The deadline-only instance is conservative.** It requires `s (ℓ+1) ≤ s ℓ + δ` and
`deadline ℓ ≤ skew (ℓ+1)`. Combined with `skew ≤ deadline`, this forces deadlines to be non-decreasing
with depth. It **rejects the repository's own three-layer example** (`deadline_only_rejected`). There
the failing inequality is `s 2 ≤ s 1 + 0 + δ`, which reads `121 ≤ 120`. The latency form with
`λmin = λmax = 1` accepts the example (`latency_accepted`, `example_from_latency`,
`example_fully_chained`).

## Premises that remain assumed (not derived)

- **`TrainingSeparation` is used by none of these proofs.** The same holds for the frozen
  `layered_monotone_recognition_one_sided`, whose proof never uses that premise. Slot separation
  stays a premise of the protocol.
- The decoder clause of each read stays observed: at most one emission, between start and deadline,
  after its arrivals, with FIRE iff threshold ≤ measured score. So do the additive residual, the
  firing-submask comparison and the anchor bounds.
- The latency bounds, the external window and the inverter law are observed per read. They are
  checkable, but no physical argument for them is given.
- The training-lesson chain needs the lesson clock and the shared windows `e`, `f` as stated
  premises. The latency corollary for lessons is not stated separately: `latency_pulse_windows`
  applies to each lesson's replay.
- Physical existence of such executions, the calibration enclosure and the read-only gate of
  non-addressed cells are out of scope, as for the existing layered target.

## Witnesses

All three use `canonical` cells, delay 0, emission one unit after each read start, and
`λmin = λmax = 1`. Every premise is closed by `decide +kernel` through sound checkers.

| Witness | Network | Inputs, inverters | Module compile time, kernel included |
| --- | --- | --- | --- |
| `WitnessAndOr.computes` | `both(x0,x1)`, `copy(x2)` / `either` / `copy` | 3 inputs, none; both chains, plus the separation cross-check | 2.5 s |
| `WitnessNot.computes` | `copy(¬x)` / `copy` / `copy` | 1 input, 1 inverter | 1.0 s |
| `WitnessXor.computes` | `both(x0,¬x1)`, `both(¬x0,x1)` / `either` / `copy` | 2 inputs, 2 inverters | 1.8 s |

The times are the wall time of one `lean` call on the session's container, measured by
`check_layered_composition.py`. The inverter has window 1/4 and emits in (1/2, 3/4]. The front end
has width `w = 1/4`, and layer 1 has skew 1/4.

## Negative controls (`check_layered_composition.py`)

Each of the following must fail to compile:

- a project axiom; a `sorry`;
- `ChainDates` without its skew inequality, or without its start inequality;
- `CellLatency` without its lower bound;
- the lesson chain without the addressed cell's skew inequality;
- undelayed direct rails;
- a claim that the deadline-only chain accepts main's example;
- an inverter that fires on its input;
- a front width below the inverter spread;
- a wire delay that misses the next window;
- a latency bound below the emission date;
- a NOT cascade that reads the direct rail;
- an intrinsic chain whose λmax bound omits the skew;
- an intrinsic example whose `dmax` is below the observed delay;
- an XOR witness that claims OR.
