# Specification: native stop-learning with small doses

This note fixes what remains to be proved for the stop-learning result
to hold for every start gain, in the existing parameterized semantics.
It states the regime, the invariant between pulses, and the theorems to
prove. Nothing here is proved unless a section says so.

## Why a new regime

Training that stops at the first FIRE leaves the gain just above the
firing limit. The pulse that makes the cell fire therefore does so late,
close to the end of the pulse. At nominal thresholds the sensor's ERROR
phase can start 0.96 time units after the pulse arrives, so a late FIRE
can come after the write has begun. No existing construction covers a
FIRE later than 0.9 units.

Lowering the ERROR entry threshold makes the SILENT phase last longer
than the pulse. The write then always starts after the pulse has ended,
and each pulse has one of two clean outcomes.

## Regime

Thresholds of the trained port, other guards nominal:

| Threshold | Value | Consequence |
|---|---|---|
| ERROR entry `u` | 2/25 | SILENT lasts between 1.067 and 1.304 units in the ±10% box |
| ERROR exit `l` | `u − d/8` | Full dose `d`. For `d = 1/20`, `l = 59/800` |
| FIRE `F` | in `[19/20, 21/20]` | FAST lasts between 0.963 and 1.035 units |

Timeline of one pulse arriving at time 0 on port `p`:

| Event | Time |
|---|---|
| Sensor MARK contact | before 0.05 |
| Sensor SILENT entry | before 0.075 |
| Pulse expiry | 1 |
| Sensor ERROR entry | between 1.08 and 1.38 |
| Sensor ERROR exit | at most 0.01 later |
| FIRE, if any | in `(0.05, 1]` |
| FAST end, if fired | FIRE + 0.963 to FIRE + 1.035 |
| Return to READY, if fired | about 11.5 units after FAST end, at recovery rate 2/25 |

The write happens in the ERROR phase. If the cell has fired it is in
FAST or SLOW during that phase, so nothing is written. The MARK phase
ends before any FIRE, so the recovery rate never changes.

Pulses are at least 24 units apart. After a silent pulse the sensor
relaxes from `l` to its rest charge within `10⁻⁶`, and the main charge
to within `2 × 10⁻⁵` of 0.1.

## Invariant between pulses

```lean
structure RestState (θ : Fin 1 → Parameters) (s : Snapshot 1) : Prop where
  main : s.main 0 = .ready
  charge : s.x 0 .q ∈ Icc (1 / 10) (1 / 10 + 1 / 10000)
  sensors : ∀ q, s.aux 0 q = .ready ∧ RestBand (s.x 0 (.m q))
  raw : ∀ q, s.raw 0 q = none
  recovery : s.x 0 .b = 2 / 25
  reserve : 50 ≤ s.x 0 .energy ∧ s.x 0 .energy ≤ 100
  caps : ∀ q, s.x 0 (.z q) ≤ Real.log ((θ 0).cap q)
```

## Theorems to prove

All in `ParameterExecution θ (fun _ _ => [])`, for either fabrication
box, with `(θ 0).thresholds = trainingThresholds p u l F`.

**A. Silent step.** From a `RestState`, with one pulse due at `D` on port
`p` and later deliveries at least 24 units after it: if the pulse leaves
the main charge below `F` throughout the pulse, and the dose fits under
the gain cap, there is an execution complete through `D + 23` that ends
in a `RestState`, has no FIRE, adds exactly `8 * (u − l)` to the log-gain
of port `p`, and changes no other gain.

**B. Firing step.** Same setting: if the main charge reaches `F` during
the pulse, there is an execution complete through `D + 23` that ends in
a `RestState`, has exactly one FIRE at the first crossing, and changes
no gain and no recovery rate.

**C. Training loop.** From a `RestState` and a train of pulses 24 units
apart on port `p`, there is an execution in which some pulse is the
first to fire, every earlier pulse wrote a full dose, and every later
pulse fires and writes nothing. The final gain is the start gain times
`exp(d × n)` for that `n`.

**D. Joint read.** After C on two ports, one pulse on each port at the
same time makes the cell fire at a latency in the window of
`stopped_pair_read_latency`, widened for the residual rest charge.

**E. Every complete run.** By the uniqueness theorem of the
parameterized semantics, every run complete through the same horizon
has the same endpoint and the same FIRE dates as the constructed one.

## What is already proved

- The latency window, for the read equation at exact rest:
  [StopLearningLatency.lean](StopLearningLatency.lean).
- The same window with a rest charge within a stated distance of 0.1:
  `stopped_read_response_residual`, in the same file.
- Steps A and B at nominal thresholds and nominal dose, for gains at
  most 7/6 and gains in `[9/5, 11/5]`:
  [NativeStopLearning.lean](NativeStopLearning.lean).

## Reusable constructions

| Need | Existing code |
|---|---|
| MARK and SILENT entry under a main-charge margin | `first_input_mark_of_response_margin_until_exists`, `first_silent_of_response_margin_until_exists` |
| SILENT leg with realized guards | `TrainingSilentLeg` and `makeSilentLeg` in `TrainingRead.lean`, whose charge bound must become a hypothesis |
| ERROR discharge between realized thresholds, with the dose | `ExposedErrorSpan` and the first half of `error_read_handoff_of_gain` |
| Conversion to the parameterized semantics | `TrainingRead.parameterExecution` and its helpers in `ParameterTraining.lean` |
| Pulse expiry, FAST end and sensor contacts in time order after a FIRE | `CoincidenceProtectedTail.lean`, written for a latency between 0.35 and 0.40 |
| Uniqueness of complete runs | `ParameterExecution.observational_unique` |

## Open choices

- The recovery from SLOW takes about 11.5 units. The 24-unit spacing is
  kept from the existing modules and could be shortened.
- A dose of 1/20 needs about 14 silent pulses from a gain of 1.2. The
  theorems should hold for any dose `d` in a stated range.
