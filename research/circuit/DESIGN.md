# The circuit and the design choices

## Question

A pulse arrives. The cell fires or stays silent. Its sensor discharges
between two thresholds and writes a dose, unless the cell has fired.
The circuit takes these decisions: to fire or not, when the write
starts and ends, how much it writes, and whether it writes.

The circuit does not detect the arrival of a pulse. Three ideal timing
signals come with each pulse. They are listed in
[what the stimulus provides](#what-the-stimulus-provides).

**Does a cell that receives a train of identical pulses, each with the
same timing signals, raise its gain and stop by itself, with device
mismatch and noise? Does it hold its gain when the stored voltage
leaks?**

## The circuit

A cell has two ports. Each port has its own gain, sensor and
integrator. The two ports share the main capacitor, the FIRE comparator
and the protection latch.

```text
 pulse ──┬─► gain mirror ──► main capacitor ──► FIRE comparator ──► protection latch
         │        ▲                                                      │
         │   stored voltage                                              │ blocks the write
         │        ▲                                                      ▼
         └─► sensor capacitor ──► discharge ──► window comparator ──► steering ──► integrator
```

| Block | Model counterpart | Realization |
|---|---|---|
| Gain mirror | gain `exp(z)` | Subthreshold NMOS pair, 40 µm / 2.5 µm. The stored voltage sets the source of the output device: a lower stored voltage is a higher gain |
| Main capacitor and leak | charge `q` | 5 pF, with a leak to rest of time constant two units |
| FIRE comparator and protection latch | READY, then protected | The comparator sets a latch when the main capacitor crosses the FIRE level. The latch moves the reference to a reopen level. It clears when the charge is back |
| Sensor capacitor | charge `m` | 400 fF, precharged to 1.3 V when a pulse arrives, then discharged by a mirrored current of 8.2 nA |
| Window comparator | SILENT, then ERROR | One comparator whose reference moves from the entry level (0.6 V) to the exit level (0.5 V) |
| Steering | ERROR writes only while READY | Between entry and exit the discharge current goes to the integrator if the protection latch is clear. Otherwise it goes to a dump node |
| Integrator | log-gain `z` | A two-stage op-amp with a feedback capacitor of 30 pF. Its output is the stored voltage |

Devices are the 1.8 V transistors of the open SKY130 primitive library.
The supply is 1.8 V. One time unit is 20 µs.

The netlists are [`cell.spice`](cell.spice) and
[`blocks.spice`](blocks.spice).

## One pulse

Times are in units after the start of the pulse, on the nominal cell.

| Time | What happens |
|---|---|
| 0 to 1 | The pulse current, multiplied by the gain, charges the main capacitor. The sensor capacitor starts to discharge |
| before 1 | If the main capacitor crosses the FIRE level, the protection latch is set. This is a FIRE |
| 1.78 | The sensor crosses the entry level |
| 1.78 to 2.04 | ERROR phase. If the latch is clear, the discharge current is integrated: the stored voltage steps by one dose |
| 5.59 | After a FIRE, the main capacitor is back to the reopen level and the latch clears |
| 22 | Next pulse |

## Design choices

Each choice is given with its reason.

### Gain

- **A subthreshold mirror, with the stored voltage on a source.** In
  subthreshold the current of a transistor is exponential in its source
  voltage. A step of the stored voltage is then a step of log-gain, and
  equal steps multiply the gain by equal factors. In the nominal cell
  26.9 mV of stored voltage is one unit of log-gain.
- **Sources near 0.4 V, not at ground.** The stored voltage is the
  output of an op-amp, which cannot reach ground.
- **Long and wide devices, 40 µm / 2.5 µm.** They limit the mismatch of
  the pair. What mismatch remains changes the number of pulses a cell
  needs, and training absorbs it.
- **A standing current of 50 nA in the input device.** The gate of the
  mirror stays charged between pulses.

### Main charge and FIRE

- **5 pF and 0.5 V per unit of charge.** With a time unit of 20 µs the
  peak of the pulse current is 173 nA, inside the subthreshold range of
  the mirror.
- **The main capacitor discharges downward from a rest level.** Rest is
  1.25 V, a charge of 0.1. FIRE is 0.80 V, a charge of 1. The mirror
  sinks its current from the capacitor. The leak is a resistance of
  8 MΩ to the rest level.
- **Admission by a switch.** During a pulse, and only while the cell is
  not protected, the output of the mirror goes to the main capacitor.
  At any other time it goes to the rest level. A protected cell receives
  nothing, as in the model.
- **One comparator with a moving reference.** When the cell fires, the
  reference of the FIRE comparator moves from the FIRE level to the
  reopen level, 1.20 V, a charge of 0.2. The same comparator then
  detects the return of the charge.
- **A latch between the comparator and the protection.** A comparator
  that moves its own reference can undo its decision while the
  reference moves. The latch accepts a FIRE only after the cell has
  been READY for 200 ns, and a release only after it has been protected
  for 200 ns. A glitch of the comparator can neither undo a FIRE nor
  fake one.
- **A larger input pair for the FIRE comparator**, 16 µm × 4 µm against
  4 µm × 1 µm for the window comparator. Its offset moves the FIRE
  level directly.

### Sensor and window

- **The dose is a charge between two thresholds.** The sensor capacitor
  gives up `C_s × (V_entry − V_exit)` between the entry and the exit,
  whatever the discharge current. That charge lands on the feedback
  capacitor. The step of the stored voltage is
  `(C_s / C_f) × (V_entry − V_exit)`.
- **400 fF, 30 pF and a window of 100 mV.** The step is 1.33 mV by
  design and 1.3465 mV in the nominal cell. That is 0.05 in log-gain,
  the dose of the read-window theorems.
- **A window of 100 mV.** It is large against the noise of the
  comparator, 0.5 mV rms.
- **One comparator for the entry and the exit.** Its offset moves both
  thresholds by the same amount and leaves their difference unchanged.
- **Entry at 1.78 units.** The write starts after the pulse has ended,
  so the decision to fire is always taken before the write. The
  precharge to 1.3 V and the discharge current of 8.2 nA set this time.
- **Exit at 2.04 units.** The write ends long before the protection
  does, at 5.59. A cell that has fired is protected during its whole
  ERROR phase.
- **A dump node at the voltage of the summing node.** The discharge
  device sees the same voltage whether its current is integrated or
  dumped, so the current does not change when the steering switches.
- **Sequencing latches.** The entry and the exit are each latched, and
  the exit is armed only after the comparator has settled on the exit
  level. Each event happens once per pulse. A glitch of the comparator
  when its reference moves cannot close the window.

### Integrator

- **A two-stage op-amp.** Its output drives the source of the mirror and
  has to sink the mirror current.
- **A preset at the start of a run.** Every cell starts from the same
  stored voltage, about 4.5 doses short of the firing gain of the
  nominal cell. A cell with mismatch then needs more or fewer pulses.

### Timing

- **Pulses 22 units apart**, as in the theorems. The main charge is
  back to rest before the next pulse.

## What differs from the model

- **The protected phase is the recovery of the main charge.** The model
  has FAST and SLOW phases with a learned recovery rate. Here the main
  capacitor returns to rest through its leak, and the cell is protected
  until it has. The property that matters for the write is kept: the
  cell is protected from its FIRE until well after the ERROR phase.
- **No MARK phase.** The learning of the recovery rate is not built.
- **One discharge rate.** The model has different rates in SILENT and
  ERROR. The dose does not depend on them.
- **The thresholds are scaled to the supply.**
- **The joint read is outside the proved window.** Two trained ports of
  this circuit fire together near 0.267. The window proved for the
  ideal model is (0.239, 0.256]: theorem `stopped_pair_read_latency` in
  [`StopLearningLatency.lean`](../recursive-learning/native/StopLearningLatency.lean).
  The mirror and the comparator add a delay that the ideal model does
  not have.
- **The arrival of a pulse is not detected.** See the next section.

## What the stimulus provides

With each pulse the stimulus gives the pulsed port three timing
signals. They are ideal sources. They are the same for every pulse and
do not depend on what the cell does.

| Signal | Timing | What it does |
|---|---|---|
| Admission | High during the pulse, one unit | Lets the output of the mirror reach the main capacitor |
| Reset of the sequencing latches | Released 1 µs before the pulse, applied again at the end of the period | Clears the entry and exit latches of the sensor |
| End of precharge | At the start of the pulse, until the end of the period | The sensor capacitor stops being precharged and starts to discharge |

- **No pulse detector is built.** A cell that works alone would have to
  derive these three signals from the pulse itself. The delay, the
  jitter and the mismatch of such a detector are not in this study.
- **The reset comes before the pulse.** A detector could not release a
  reset 1 µs before the pulse that it detects. A real cell would clear
  its latches at the end of the previous cycle, or after the detection.
- **The duration of the admission is given.** It is one unit, the
  length of the pulse, set by the stimulus.
- **What is not given.** No signal tells the circuit whether it fired,
  when to start the write or when to end it. The sensor crossing the
  exit level ends the write.
- **The statement of the model that there is no clock** is therefore
  only partly carried by this circuit. The end of the write needs no
  clock here. The start of a sensor cycle is taken from an ideal
  signal.

The stimulus also selects which port is pulsed in each period, and
presets the integrator once at the start of a run.

## Stimulus

A run starts with one period at rest. It gives the reference read of
the stored voltages, and nothing may fire in it.

- **Cell run:** 10 pulses on port 1, 10 pulses on port 2, then one pulse
  on both ports. All pulses are identical. The start gain is the same
  for every cell.
- **Refresh run:** pulses on port 1 only, 100 to 560 of them. An
  optional resistance from the summing node of the integrator to ground
  makes the stored voltage leak toward a lower gain.

The pulse is an ideal current with the canonical shape of the model: it
falls by a factor of four over the pulse.

## Noise

ngspice adds no device noise to a transient. Each block is analysed
alone with a small-signal noise analysis ([`noise.py`](noise.py)), and
its noise is injected in the transient at its input.

| Source | rms | of which flicker |
|---|---|---|
| Window comparator of each port, input-referred | 0.50 mV | 0.11 mV |
| FIRE comparator, input-referred | 0.34 mV | 0.11 mV |
| Integrator op-amp of each port, input-referred | 0.27 mV | 0.04 mV |
| Mirror current of each port (shot noise at 300 nA) | 0.49 nA | none |

- **Sources sampled every 0.4 µs**, a band of 1.25 MHz. The cost of a
  run follows the number of noise samples. Each source keeps the total
  rms of its block. This puts more of the op-amp noise at low frequency
  than the block has, which overstates the noise of a read of the
  stored voltage.
- **One seed per run** sets the mismatch sample and the noise sample.

## Solver

Every run uses the same netlist, the same options and the same largest
step. ngspice 42, trapezoidal integration.

| Setting | Value | Reason |
|---|---|---|
| `reltol`, `chgtol` | 1e-4, 1e-17 C | With the default values, equal pulses write steps that differ by 1.7%. With these the steps are equal within 0.04% |
| `abstol`, `vntol` | 1e-13 A, 1e-7 V | The currents are nanoamperes and a dose is about a millivolt |
| `gmin` | 1e-16 S | ngspice puts a conductance `gmin` across every junction, 1e-12 S by default. On the summing node of the integrator that is a leak of 0.4 pA, far above the leakage of the device models. It would look like a loss of the stored voltage |
| Largest step | 200 ns | Half the sample time of the noise. With a larger step a noisy run fails |
| Stimulus edges | Ramps of 1 ns from pulse sources | The solver puts a time point on both ends of a declared edge. With an edge computed by a behavioural source, the solver can step across it, and a latch was seen to rise for 130 ns inside such a step with both its inputs inactive. It did not rise with a step of 100 ns or with Gear integration |
| Noise sources | All voltage sources | A netlist that mixes voltage and current noise sources makes the solver stall. The mirror noise is a voltage noise source that drives a controlled current |
| Edges and noise samples | Every edge 0.1 µs from a noise sample | An edge that falls on a noise sample makes the solver stall |
| Noise injection | Through 1 kΩ and 20 fF | Needed for a noisy transient to run |

On a noisy run of 1.4 ms the time points were audited: all 3 499 noise
instants and all 26 edge corners are time points of the solution, and
no step is longer than 200 ns.

## Resolution of the measures

The runner prints each measure with six significant digits. This sets
the resolution of every time and every voltage in the results.

| Measure | Resolution |
|---|---|
| A time in the first 10 ms of a run: every pulse of a cell run of 22 periods | 10 ns, 0.0005 unit |
| A time between 10 ms and 100 ms: refresh runs from pulse 22 on, and the long nominal run | 100 ns, 0.005 unit |
| A time after 100 ms: the 1 TΩ refresh run from pulse 227 on | 1 µs, 0.05 unit |
| A stored voltage | 1 µV, 0.0007 dose |

Whether a pulse fired does not depend on this resolution. A latency
does. In the refresh runs a FIRE that comes in the last 100 ns of the
pulse is printed with a latency of exactly 1.

One such pulse was replayed with the internal nodes saved, with a
largest step of 200 ns, with 100 ns, and with Gear integration. The
FIRE comparator trips and the latch rises 50 ns, 48 ns and 57 ns before
the end of the pulse. The printed latencies were 1.000, 1.000 and
0.995.

## Measures

| Quantity | Definition |
|---|---|
| FIRE | The protection latch rises during the period |
| Latency | Time from the start of the pulse to that rise, in units |
| Stored voltage | Mean of the integrator output over the last 40 µs of the period |
| Step | Change of the stored voltage from one period to the next, positive toward a higher gain |
| Read noise | Sigma of the step of a port that receives no pulse in that period |
| Relapse | A silent pulse after the first FIRE of a port |
| Band | Largest minus smallest stored voltage after the stop, in doses |

## The guard

The analysis looks at the protection latch in every period of every
run. It reports two kinds of event. Neither is dropped silently.

| Event | Kind | Treatment |
|---|---|---|
| The latch rises within 0.05 unit of the pulse edge, or before it | Not a FIRE: the main capacitor cannot reach the FIRE level that early | Reported. The run is left out of the statistics |
| The latch rises in the period at rest | Not a FIRE: there is no pulse | Reported. The run is left out of the statistics |
| The latch rises later than 1.02 units, after the end of the pulse | Against the mechanism: a late FIRE comes closer to the write | Reported. The run stays in the statistics |
| The latch rises twice in one period | Against the mechanism | Reported. The run stays in the statistics |
| The latch does not clear before the next pulse | Against the mechanism | Reported. The run stays in the statistics |

The limit of 1.02 leaves 0.01 unit for the 200 ns of the latch and
0.01 unit for the resolution of a latency up to 100 ms. After 100 ms,
in the 1 TΩ refresh run, a latency is printed to 0.05 unit, and the
guard cannot tell a FIRE at 1.00 from one at 1.02 there.

The test that a firing pulse writes nothing (P10) is made on every run
that produced a result, whatever the guard says of it. A run that the
simulator aborts writes no result and is listed as failed.

`PREDICTION.md` was written with one class of anomaly, all left out of
the statistics. The split above was made afterwards. Prediction P19 is
judged as written: it fails if the guard reports any event of either
kind.

## Not modelled

- Detection of the pulse. The admission, the reset of the sequencing
  latches and the end of the precharge are ideal signals given with
  each pulse.
- Layout parasitics and coupling between nodes.
- Supply and ground: the supply is an ideal source. A bounce of the
  supply at a pulse edge could raise a latch in a real circuit, and
  this study cannot see it.
- Leakage of the stored voltage beyond the device models. The refresh
  runs impose a leak instead.
- Mismatch and noise of the references and of the bias currents. They
  are ideal sources.
- Capacitor mismatch.
- The sampling noise of the precharge of the sensor, about 0.1 mV rms
  on 400 fF.
- Temperature changes between training and reading. Each run is
  trained and read at one temperature.

These are simulations. No chip was built and no layout was drawn.
