# Specification: native stop-learning with small doses

**Status.** This note was written as a specification, before the
proofs. Every theorem it lists, A to F below, is now proved; each section
names the Lean declarations. The note is kept as the statement of the
regime and the invariant between pulses that those theorems use. The
[map of the stop-learning results](README.md#map-of-the-stop-learning-results)
lists the strongest statement at each level.

It fixed what had to be proved for the stop-learning result to hold for
every start gain, in the existing parameterized semantics.

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
| ERROR entry `u` | in `[7/100, 2/25]` | SILENT lasts between 1 and 1.55 units in the ±10% box |
| ERROR exit `l` | `u − d/8`, at least 1/200 | Full dose `d`. For `u = 2/25` and `d = 1/20`, `l = 59/800` |
| FIRE `F` | in `[19/20, 21/20]` | FAST lasts between 0.963 and 1.035 units |

Timeline of one pulse arriving at time 0 on port `p`:

| Event | Time |
|---|---|
| Sensor MARK contact | before 0.05 |
| Sensor SILENT entry | before 0.075 |
| Pulse expiry | 1 |
| Sensor ERROR entry | after 1, before 1.6 |
| Sensor ERROR exit | at most 0.375 later |
| FIRE, if any | in `(0.05, 1]` |
| FAST end, if fired | FIRE + 0.963 to FIRE + 1.035 |
| Return to READY, if fired | about 11.5 units after FAST end, at recovery rate 2/25 |

The write happens in the ERROR phase. If the cell has fired it is in
FAST or SLOW during that phase, so nothing is written. The MARK phase
ends before any FIRE, so the recovery rate never changes.

Pulses are at least 22 units apart after a silent pulse. The sensor then
relaxes from `l` to its rest band, and the main charge to within `10⁻⁴`
of 0.1.

## Invariant between pulses

```lean
structure RestState (θ : Fin 1 → Parameters) (s : Snapshot 1) : Prop where
  main : s.main 0 = .ready
  aux : ∀ q, s.aux 0 q = .ready
  raw : ∀ q, s.raw 0 q = none
  charge : 1 / 10 ≤ s.x 0 .q ∧ s.x 0 .q ≤ 1 / 10 + 1 / 10000
  sensors : ∀ q, RestBand (s.x 0 (.m q))
  recovery : 0 ≤ s.x 0 .b ∧ s.x 0 .b ≤ 11 / 10
  energy : 50 ≤ s.x 0 .energy ∧ s.x 0 .energy ≤ 100
  caps : ∀ q, s.x 0 (.z q) ≤ Real.log ((θ 0).cap q)
```

This is the definition in [SilentStep.lean](SilentStep.lean). The firing
step may need a narrower condition on the recovery rate.

## Theorems (all proved)

All in `ParameterExecution θ (fun _ _ => [])`, for either fabrication
box, with `PortConfig θ p u l F`. That condition constrains the ERROR
levels of port `p` only, so one cell can satisfy it for several ports.
`two_port_training_exists` trains two ports in one execution.

**A. Silent step. Proved** as `silent_step_exists`. From a `RestState`
with one pulse due now on port `p` and later deliveries at or after a
chosen date `rest`, at least 22 units later: if the pulse leaves the main
charge below `F` throughout the pulse, and the gain after one dose is at
most 7/2, there is an execution that ends in a `RestState` at `rest`,
adds exactly `8 * (u − l)` to the log-gain of port `p`, and changes no
other gain and no recovery rate. The run has no FIRE event.

**B. Firing step. Proved** as `firing_step_exists`. Same setting, with a
recovery rate between 7/100 and 1/10: if the main charge reaches `F` at
some time of the pulse, there is an execution that ends in a `RestState`
at `rest`, with no gain and no recovery rate changed and the main charge
exactly at 1/10. The tail after the FIRE is `refractory_run_exists`,
which takes the pending events in their time order. The count of FIRE
events is one.

**C. Training loop. Proved** as `training_loop_exists` and
`stop_training_exists`. From a `RestState` and a train of pulses at
least 22 units apart on port `p`, there is an execution in which every
silent pulse writes a full dose and every firing pulse writes nothing.
A pulse that fires thanks to a residual rest charge may be followed by
one more silent pulse. If `r` doses reach a gain that always fires and
the train has at least `2 r + 2` pulses, the final gain fires from the
exact rest charge, and the gain one dose below it was silent unless no
dose was written.

**D. Joint read. Proved** as `staggered_read_exists`,
`stopped_staggered_read` and `trained_read_exists`. The second read pulse
arrives up to a quarter of a unit after the first. The phase before the
FIRE is `driven_until_exists` then `driven_run_exists`, which take the
MARK and SILENT entries of the two sensors in their time order. After C
on two ports with doses of at most 1/20, the cell fires later than 0.239
units after the first read pulse and no later than 0.256 units after the
second.

**F. Network contract. Proved** as `trained_coincidence_network`, with an
explicit witness of its hypotheses, `trained_coincidence_witness`.

**E. Every complete run. Proved for the training** as `rest_run_unique`,
and included in `stop_training_exists`: every run complete through the
horizon ends in the same state as the constructed one, with the same
number of FIRE events. `trained_read_exists` states it for training and
read together, with the FIRE dates.

## Proved before the training loop

- The latency window, for the read equation at exact rest:
  [StopLearningLatency.lean](StopLearningLatency.lean).
- The same window with a rest charge within a stated distance of 0.1:
  `stopped_read_response_residual`, in the same file.
- Steps A and B at nominal thresholds and nominal dose, for gains at
  most 7/6 and gains in `[9/5, 11/5]`:
  [NativeStopLearning.lean](NativeStopLearning.lean).
- Step A in the regime above, for any gain:
  [SilentStep.lean](SilentStep.lean).
- The refractory period for any order of events:
  [Refractory.lean](Refractory.lean).
- Step B in the regime above, for any gain:
  [FiringStep.lean](FiringStep.lean).
- The loop C for every start gain: [TrainingLoop.lean](TrainingLoop.lean).

## Reusable constructions

| Need | Existing code |
|---|---|
| MARK and SILENT entry under a main-charge margin | `first_input_mark_of_response_margin_until_exists`, `first_silent_of_response_margin_until_exists` |
| SILENT leg with realized guards | `TrainingSilentLeg` and `makeSilentLeg` in `TrainingRead.lean`, whose charge bound must become a hypothesis |
| ERROR discharge between realized thresholds, with the dose | `ExposedErrorSpan` and the first half of `error_read_handoff_of_gain` |
| Conversion to the parameterized semantics | `TrainingRead.parameterExecution` and its helpers in `ParameterTraining.lean` |
| Pulse expiry, FAST end and sensor contacts in time order after a FIRE | `CoincidenceProtectedTail.lean`, written for a latency between 0.35 and 0.40 |
| Uniqueness of complete runs | `ParameterExecution.observational_unique` |

## Open choices at the time of writing

- The recovery from SLOW takes about 11.5 units. The spacing after a
  firing pulse was not fixed yet. *Resolved:* the theorems use pulses at
  least 22 units apart.
- A dose of 1/20 needs about 14 silent pulses from a gain of 1.2. The
  theorems should hold for any dose `d` in a stated range. *Resolved:*
  the training theorems hold for doses up to 3/5; the read windows are
  stated for doses of at most 1/20.
