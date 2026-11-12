# Training that stops by itself

[Back to the native package](../README.md)

## Read latency after training that stops at the first FIRE

[StopLearningLatency.lean](StopLearningLatency.lean) studies the READY
read equation of a rested cell. It does not build a hybrid execution.

A training pulse of relative amplitude `c` acts on the main charge as a
canonical pulse at gain `c * gain`. In R, a training pulse that makes
the cell fire writes nothing, because the cell is protected during the
sensor's ERROR phase. Training by weakened pulses therefore stops at the
first FIRE. `StoppedTraining gain c fire d` describes that state: the
current gain fires on a weakened pulse, and the gain before the last
increment, of at most `d` in log-gain, did not.

`stopped_read_response` gives the response level `h(t)` reached at the
FIRE of a later full-amplitude read:

```text
c * exp(-d) * h(1)  <  h(t)  ≤  c * h(1)
```

The gain and the FIRE threshold do not appear. The increments may be
unequal and inexact, as long as each is positive and at most `d`.
`stopped_read_latency` turns the two levels into a latency window, and
`stopped_read_skew` bounds the latency difference of two cells by the
width of that window, whatever their gains and FIRE thresholds.
`stopped_read_exists` shows that a cell which fires on a weakened pulse
fires on a full one.

For `c = 2/3` and `d = 1/20`, `stopped_read_latency_two_thirds` gives a
read FIRE between 0.355 and 0.385 model units after the pulse, and
`stopped_read_skew_two_thirds` a difference below 0.03 units between two
cells. The coincidence theorem uses a window of 0.0495 units and needs
an exact birth gain and a FIRE threshold within ±3%.

The stopping rule is the stop-learning principle of Brader et al.,
which Noack et al. implement in switched capacitors. These theorems
state its consequence for the R read equation.

**The ratio from two ports.** The kernel adds the currents of the ports,
so the amplitude ratio need not come from the pulses. Train two ports
separately with canonical pulses until each makes the cell fire, then
read with one pulse on each port at the same time. `stopped_pair` shows
that the pair is in the stopped state at relative amplitude one half.
The ratio is exact because it counts ports. With increments of at most
`1/20`, `stopped_pair_read_latency` gives a read FIRE between 0.239 and
0.256 model units, and `stopped_pair_read_skew` a difference below 0.017
units between two cells, whatever their four gains and two FIRE
thresholds.

**Training ends.** `training_stops` takes any sequence of log-gain
increments between a positive lower bound and `d`, starting from a gain
whose pulse is silent. Some pulse is the first to fire, every earlier
pulse was silent, and the cell is then in the stopped state.

**A rest charge that is only close to nominal.** Between pulses the main
charge relaxes toward 0.1 without reaching it.
`stopped_read_response_residual` takes rest charges within `δ` above
0.1, at the firing pulse, at the last silent pulse and at the read. The
window keeps its form, with the two levels multiplied by factors that
tend to one with `δ`. The gain and the charges do not appear in it.

What they assume and do not prove:

- The cell is at its rest charge 0.1 before each training pulse and
  before the read.
- For a ratio taken from the pulses, `c` is exact and the same for every
  cell. For two ports, the two read pulses arrive at the same instant.
- The sequence of gains is given. No hybrid execution is constructed in
  which a silent pulse writes an increment and a firing pulse writes none.
- The pulse shape is canonical.

## Native training that stops at the first FIRE

[NativeStopLearning.lean](NativeStopLearning.lean) constructs the
stopping rule as an execution of the kernel, at nominal thresholds. It
reuses the existing weak-pulse and learned-FIRE constructions and adds no
definition to the kernel.

- `silent_slot_exists`: a pulse on a port whose gain is at most `7/6`
  leaves the cell silent and writes the full dose `3/5` on that port.
- `firing_slot_exists`: a pulse on a port whose gain lies in
  `[9/5, 11/5]` makes the cell fire once, between the pulse and one unit
  later. No gain changes and the recovery rate stays at `2/25`.

In both cases the cell is READY again 23 units after the pulse.

`native_stop_training_of_target` chains these over a train of pulses at
least 24 units apart. Suppose `n` doses bring the gain of the port into
`[9/5, 21/10]`. Then for any train of at least `n` pulses, the first `n`
are silent, every later one makes the cell fire, and the final log-gain
is the start value plus `3/5 * n`. The other gains and the recovery rate
are unchanged, and the number of FIREs is the number of pulses minus `n`.

The number `n` is not fixed by the protocol. It depends on the start
gain, and two cells that need different numbers of doses end in the same
band `[9/5, 21/10]` after the same pulse train.

Scope:

- **Covered start gains.** A start gain `g` is covered when `g * exp(3n/5)`
  lies in `[9/5, 21/10]` for some `n`. That is a band of width about 0.15
  in log-gain out of each period of 0.6. The other start gains pass
  through gains between `7/6` and `9/5`, where no existing construction
  applies. The firing limit, about 1.61, lies in that gap.
- **Nominal thresholds and the nominal dose.** The FIRE threshold is 1.
  Small doses and inexact thresholds are not covered.
- **One port.** The joint read of two trained ports is proved for the
  read equation only, in `StopLearningLatency.lean`.

The [specification](../STOP_LEARNING_SPEC.md) states the regime and the
theorems that remain for every start gain to be covered with small doses.

### A silent training step for any gain

[SilentStep.lean](SilentStep.lean) proves the first of those theorems,
`silent_step_exists`, in the parameterized semantics. The ERROR entry
threshold of the trained port lies between 7/100 and 2/25. SILENT then
lasts longer than the pulse for every cell of either fabrication box
(`low_entry_silent_duration`), so the write starts with no input current
left.

The start state is any `RestState`: main charge within `10⁻⁴` above 0.1,
sensors in their rest band, gains under their caps, any admissible
recovery rate and energy reserve. The hypotheses on the pulse are:

- the main charge stays below the realized FIRE level, between 19/20 and
  21/20, for the whole pulse;
- the gain after one dose stays at most 7/2.

No gain band is assumed. The conclusion is an execution that ends in a
`RestState` at any chosen date at least 22 units after the pulse. The
log-gain of the pulsed port has moved by exactly `8 × (entry − exit)`.
The other gains and the recovery rate are unchanged.

The main charge may exceed 1 during the pulse when the realized FIRE
level is above 1. The flows are therefore built directly with realized
guards (`silent_leg_of_margin`, `quietDynamics`) and do not go through
the nominal kernel.

The agreement of every complete run with the construction is stated
once, for the whole training, in `TrainingLoop.lean`.

### The refractory period for any order of events

[Refractory.lean](Refractory.lean) treats the cell after a FIRE. While
the main cell is in FAST or SLOW and no sensor is in MARK, the main
charge and each sensor evolve on their own: the input current reaches
neither, no gain is written and the recovery rate is constant.
`refractoryDynamics` is the explicit flow of that regime, for any number
of busy sensors.

`refractory_run_exists` turns it into an execution of the parameterized
semantics. From a refractory state it runs to the reopening of the main
cell. The pending events are the end of FAST, the ERROR entry and exit
of each busy sensor and the end of each live pulse. They are taken in
their time order by induction on their number, so no order and no tie
between them is assumed. The hypotheses are:

- each threshold is positive and below the one that precedes it;
- every busy sensor is READY again, and every pulse has ended, before
  the main cell reopens;
- a pulse ends before its sensor reopens.

The conclusion gives the reopening date, the main charge at its reopen
threshold, every sensor READY on an explicit relaxation, and unchanged
gains, recovery rate and queue.

The theorem is the common tail of the firing training step and of a read
on several ports.

### A firing training step

[FiringStep.lean](FiringStep.lean) proves `firing_step_exists`, in the
same regime and from the same `RestState` as the silent step. The
hypothesis is the negation of the silent one: at some time of the pulse
the main charge of the rested cell reaches the realized FIRE level. The
recovery rate lies between 7/100 and 1/10.

The construction takes the first contact with the FIRE level, which
happens while the pulsed sensor is SILENT, fires there, and hands the
state to `refractory_run_exists`. The ERROR phase of the sensor then
falls inside the refractory period, whatever its order with the end of
FAST. The conclusion is an execution that ends in a `RestState` at any
chosen date at least 22 units after the pulse, with every gain and the
recovery rate unchanged and the main charge exactly at 1/10.

Together the two steps cover every pulse on a rested cell: it either
stays below the FIRE level and writes one dose, or reaches it and writes
nothing. Neither theorem assumes a gain band.

The run has exactly one FIRE event. The silent step and the refractory
period have none. Each construction carries its count (`Runs`).

### The training loop, for every start gain

[TrainingLoop.lean](TrainingLoop.lean) chains the two steps over a train
of pulses on one port, at least 22 units apart.

- `training_step_exists` joins the two steps. No hypothesis on the gain
  remains: a silent pulse always leaves room for one more dose under the
  cap (`silent_room`).
- `training_loop_exists` builds the execution through the whole train.
  Its conclusion is a `Trained` record: for each pulse, whether it was
  silent and wrote one dose, or fired and wrote nothing.
- `stop_training_exists` is the stopping rule. If `r` doses bring the
  start gain to a value that always fires, and the train has at least
  `2 r + 2` pulses, then the final gain fires from the exact rest charge
  1/10, and it equals the start gain times `exp(k × dose)` for some `k`
  at most the number of pulses. Unless no dose was written, the gain one
  dose below the final one was silent from a rest charge within `10⁻⁴`
  above 1/10.

The factor 2 has a physical cause. A pulse may fire only thanks to the
residual rest charge left by the previous silent pulse. The next pulse
starts from the exact rest charge and may then be silent once more.
After a FIRE from the exact rest charge, every later pulse fires
(`Trained.stable`).

Every run agrees with the constructed one. `rest_run_unique` applies
the uniqueness theorem of the parameterized semantics: any run from the
same rested start that is complete through the horizon ends in the same
state, with the same number of FIRE events. `stop_training_exists`
includes that statement, and each pulse is either one of its `k` doses
or one of its `f` FIRE events.

### Two ports of one cell

The thresholds are no longer required to equal a single-port
configuration. `PortConfig θ p upper lower level` states what a pulse on
port `p` needs: nominal main, MARK and SILENT levels, the realized FIRE
level, and the two ERROR levels of port `p`. The other ports keep any
ordered ERROR levels, so one cell satisfies it for several ports, each
with its own dose. `PortConfig.of_training` recovers the single-port
configuration of the earlier modules.

`two_port_training_exists` trains two ports one after the other in one
execution. The second train waits in the queue during the first. Both
final gains fire from the exact rest charge, each is at most one dose
above a silent gain unless no dose was written on it, and every complete
run agrees with the constructed one.

### The driven period before a FIRE

[Driven.lean](Driven.lean) is the counterpart of `Refractory.lean` for
the time before a FIRE. While the main cell is READY and no sensor is in
ERROR, no gain is written. The main charge follows the sum of the live
pulses weighted by their gains, and each sensor follows its own pulse or
its own decay. `drivenDynamics` is that explicit flow for any number of
live pulses.

A `Plan` states what holds up to a horizon: the main charge stays below
the FIRE level, the live pulses last, no delivery is due, and a SILENT
sensor stays above its ERROR entry threshold. Two theorems run it.

- `driven_until_exists` runs to a date at which sensors may still be on
  their way. The plan holds again there, so a new pulse can be admitted.
- `driven_run_exists` runs to a horizon by which every busy sensor is
  SILENT.

In both, the MARK and SILENT entries of the sensors are taken in their
time order by induction. Two pulses on two ports need no assumption on
which sensor moves first.

### The read of two ports, and training and read in one execution

[JointRead.lean](JointRead.lean) reads two ports. The second read pulse
arrives up to a quarter of a unit after the first, or at the same
instant.

- `fire_rest_exists` is the FIRE and the return to rest with any number
  of SILENT sensors. It uses `refractory_run_exists`.
- `staggered_read_exists`: if the first pulse alone stays below the FIRE
  level until the second arrives, and the two together reach it later,
  the cell fires exactly once, at the first contact, and returns to rest
  with every gain unchanged. The date of the FIRE is part of the
  statement (`Emits`).
- `stopped_staggered_read`: when each gain fires alone from the exact
  rest charge and was silent one dose below, with doses of at most 1/20,
  the FIRE comes later than 0.239 units after the first read pulse and
  no later than 0.256 units after the second. Every complete run fires
  at that same date.
- `trained_read_exists` is the whole experiment in one execution. Two
  ports start from gains that do not fire. Each is trained by its own
  train of pulses until it stops by itself, then one pulse on each port
  reads the cell. The read FIRE lies in the same window, whatever the
  start gains and the FIRE level between 19/20 and 21/20. Every complete
  run has the same FIRE dates and the same end state.

### The coincidence decision of two trained cells

[TrainedCoincidence.lean](TrainedCoincidence.lean) restates the network
contract of `CoincidenceNetworkContract` with trained cells.

- `TrainedCell` gathers the hypotheses on one cell: its parameters in
  the fabrication box, its thresholds, its rested start, its two pulse
  trains and its two read pulses.
- `trained_coincidence_network`: two such cells form a two-cell network.
  Each has its own parameters, its own start gains and its own FIRE
  level. The right cell is read 0.3 units before, at the same date as, or
  0.3 units after the left one, and within each cell the second read
  pulse is at most 1/10 after the first. In every complete run of the
  network, each cell's last FIRE is its read FIRE, and the two dates are
  closer than 3/20 exactly when the two cells are read at the same date.
- `trainedCell_witness` and `trained_coincidence_witness`: an explicit
  cell and an explicit schedule satisfy every hypothesis. The cell is
  nominal with ERROR thresholds 2/25 and 59/800, start gains 6/5 and two
  trains of 22 pulses. The contract is therefore not vacuous.

This replaces the two hand-set hypotheses of the earlier coincidence
result, an exact birth gain and a FIRE level within 3%, by a training
rule that absorbs both. The earlier result also showed that no setting
of a constant-current timer meets the same receiver contract at its
registered corner. That comparison is not redone here.

Limits of these statements:

- **Order of the read pulses.** In each cell the pulse on the first
  trained port arrives no later than the pulse on the second, by at most
  a quarter of a unit, and by at most 1/10 for the network decision.
- **Doses of at most 1/20 for the window.** The training theorems hold
  for any dose up to 3/5. The window constants are for doses up to 1/20.
- **Recovery rate between 7/100 and 1/10**, sensors within `10⁻⁵` of
  their rest charge, pulses at least 22 units apart.
- **Two independent cells.** The network has no wire between the cells.
  The receiver that compares the two FIRE dates is outside the model.
- **Circuit quantities.** Gain mismatch and FIRE level are covered. The
  pulse amplitude, the unit response and the thresholds other than FIRE
  and the two ERROR levels are those of the model.

### A lag between a pulse and its effect

[ReadLag.lean](ReadLag.lean) treats one departure of a circuit from the
model. The element that applies a gain takes a short time to settle, so
a pulse acts on the main charge a little after it arrives. A lag that is
the same for every pulse of a cell shifts every FIRE date of that cell
by that lag, and changes nothing else.

- `trained_dates_decide_lag`: the two read FIRE dates of the coincidence
  decision are observed later than the model gives them, each by the lag
  of its cell. If the two lags differ by at most 3/100 of a unit, the
  observed dates are closer than 3/20 exactly when the two cells are
  read at the same date.
- `trained_network_lag`: the same for any number of trained cells, each
  with its own lag, in every complete run.

In the wired networks and the searches a common lag adds to the delay of
each wire, which those theorems already leave free.

Limits:

- **One lag per cell.** A lag that depends on the pulse, on the port or
  on the slope of the charge is not covered.
- **A statement on dates.** The lag is applied to the FIRE dates of the
  model. A semantics in which a pulse acts late is not constructed.
