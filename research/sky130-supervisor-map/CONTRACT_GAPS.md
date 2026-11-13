# Contract map before a SKY130 supervisor experiment

This is an exploratory audit of the existing netlist and v5 contract, not a
preregistration or a physical certificate. The equations below specify what
must be established before the discrete theorem can be applied. Nominal
transistor trials may support feasibility; they cannot establish universal
bounds over mismatch, noise, process corners or temperature.

## 1. State, sign and the service predicate

The output device of the gain mirror has `vmem` as its source. **Lower stored
voltage means higher gain.** A useful voltage margin therefore has the sign
`V_service - Vmem`, not `Vmem - V_service`.

For this first map, service concerns port 1 alone, with port 2 inactive. Define
one successful service as exactly one protection-latch rise during the declared
20 microsecond service pulse, with the required reset/recovery conditions
before the following action. A maintenance FIRE is never counted as service.
This is not the separate ideal two-port read-window specification.

Let `Theta` contain the admitted main-charge initial state, latch/sensor state,
clock timing, port configuration, process and temperature. A robust service
threshold `V_S` must support the implication

```
state in Theta and Vmem <= V_S  =>  the service pulse succeeds by its deadline.
```

A threshold observed after a 440 microsecond rest cannot silently be reused
after an interleaved maintenance pulse. The main capacitor and protection latch
are shared. Even after the latch reopens, residual main charge may change the
next read threshold. `Theta` must be shown to recur for the actual schedule.
The nominal design reports reopen around 5.59 time units (111.8 microseconds),
which is a timing observation, not a worst-case recovery guarantee.

For a fixed positive voltage scale `delta` (volts per reserve unit), use

```
x = S + (V_S - Vmem) / delta
C = S + (V_S - Vmem_min) / delta.
```

Then `x >= S` implies the voltage part of the service guard. The offset `S`
is a coordinate convention, whereas `V_S`, `Vmem_min`, and the validity domain
of the implication need physical justification. A nominal write of 1.3465 mV
can be a convenient scale; it is not thereby a fixed delivered dose on every
pulse. The v5 values 100, 440 and 660 do not acquire physical meaning merely
by rescaling the voltage axis.

`Vmem_min` must describe a safe operating range with justified behavior of the
integrator and gain mirror. An op-amp rail is not a proof of the exact clipped
update `min(C, x + D)`. A conservative bridge can instead avoid the nonlinear
region, with a verified upper-state guard.

The default initial preset is below the firing gain: the original nominal cell
requires four silent learning pulses. Initialization must be a declared,
charged preparation phase, followed by a measured entry certificate. Those
pulses cannot be counted as successful service from an already-ready state.

## 2. Actions and the missing dose guarantee

Keep distinct ledgers for mandatory service pulses, optional analog probes,
optional maintenance pulses, and waiting. Waiting skips supervisor actions;
it does not skip the service obligation at each service period.

Two candidate maintenance stimuli are weaker versions of the service pulse
(e.g. amplitude factors 0.95 or 0.9). They are candidates, not established
actuators. Another candidate is a clock-only pulse with no applied signal
current during admission. In the existing behavioral stimulus, zero amplitude
still changes the 50 nA standing input current to zero during admission; it is
not equivalent to leaving the port untouched. Sensor clocks, sequencing and
main-charge transients must still be checked. All these actions require the
explicit external clock/stimulus interface already used by this simulation;
no autonomous pulse detector is present in the cell.

For a maintenance stimulus with an uncertain firing threshold, let `V_M_max`
be an upper bound on that threshold over its admitted starting states. Since
higher voltage means lower gain, the useful interval is

```
V_M_max < Vmem <= V_S.
```

The right inequality supports service; the strict left inequality supports
maintenance silence. In reserve coordinates the maintenance silence ceiling is

```
M = S + (V_S - V_M_max) / delta,
write admissibility: certified upper reserve < M.
```

The ceiling must include sensor/readout errors and movement between the probe
and maintenance admission. A nonempty nominal threshold gap is not enough if
its robust gap disappears after those margins.

A silent maintenance pulse must also complete its write window before the next
service. A firing maintenance pulse normally blocks its own write, so a
commanded maintenance action does **not** imply that a full dose arrived.
V5's Boolean `delivered` and `+220` cannot be inferred merely from issuing the
command. Either prove maintenance is silent on every state where writing is
chosen, or measure delivery and use a contract with bounded failed/partial
actuation. A clock-only maintenance pulse might avoid a reserve-dependent
silence ceiling, but only after showing silence and dose delivery throughout
the admitted state box.

## 3. Charge balance, units and chronology

The feedback capacitor is between the summing node and the stored-voltage
output. With the indicated polarity its charge is

```
Q_f = C_f * (Vsum - Vmem).
```

If `I_write` enters the summing node and `I_leak` leaves it, collect every other
current into a signed residual `I_other`, positive into the node. Then the
ideal capacitor identity gives

```
Delta Vmem = Delta Vsum
             - (integral I_write dt - integral I_leak dt
                + integral I_other dt) / C_f.
```

For the imposed resistor, `I_leak = Vsum / R_leak`, not `Vmem / R_leak`.
The conversion from a current integral to reserve units divides by
`C_f * delta`. Report current in A, integrated charge in C (or fC), voltage
change in V (or mV), and time in seconds. Save the voltage on both capacitor
terminals and the actual steering current; a whole-period net voltage step is
not an independent gross delivered dose.

For example, the nominal resistor approximation at `Vsum = 0.4 V`,
`R_leak = 1e11 ohm`, `C_f = 30 pF`, and period 440 microseconds gives

```
I_leak = 4 pA
Q_leak = 1.76 fC per period
Delta V_leak = 58.6667 microvolts per period.
```

This agrees in scale with the existing refresh records, but remains a model
calculation: summing-node movement, parasitics, supply dynamics and numerical
error still need enclosure. Do not add this loss twice to an already net dose.

A usable discrete balance can be written

```
x[n+1] = x[n] - loss[n] + write[n] * dose[n],
loss[n] <= H,   D_min <= dose[n] <= D_max,
```

only after fixing the two sampling dates and assigning *all* effects exactly
once. The loss envelope must include service-pulse effects, idle leakage,
probe effects if modeled, maintenance overhead, and the signed residual above.
A noisy or settling trajectory can have negative effective loss. V5 currently
assumes nonnegative loss; either justify this for the chosen coordinate and
sampling rule, or generalize the contract with a lower bound such as
`loss >= -J`. In the latter case the no-saturation guard needs the possible
beneficial drift too, e.g. `upper + J + D_max <= C` over the action segment.

In the current netlist a silent pulse's write occurs about 35.6–40.8
microseconds after its start, after the service decision. It cannot repair
that same missed service retroactively. Maintenance must happen early enough
for the next required service, including settling and protection recovery.
A bound per whole period does not justify proportional fractional-period
bounds without an additional rate or cumulative-loss envelope.

## 4. Feasibility guards and the v5 proof changes

Use `L(t0,t1)` for a justified cumulative loss upper bound, not an extrapolation
from observed mean leakage. At a probe with certified lower reserve `lower`,
a conservative plan that waits until another probe and may then need a repair
must reserve enough for both portions:

```
lower >= S + L(now, next_probe) + L(next_probe, repair_complete).
```

The service/read phase may need an additional transient guard in `Theta`.
For a one-period repair latency and per-period bound `H`, this reduces to
`lower >= S + (k+1)*H` before waiting `k` periods. This explains the v5
`Ready >= S+H` structure; it does not establish that a physical maintenance
pulse has precisely that latency.

In a simplified model with at most one maintenance delivery per period,
`D_min >= H` is necessary for an indefinite guarantee over an independent
box that allows loss H and dose D_min on every tick. Failure of this box test
is not proof of physical impossibility if the extrema cannot occur together.
The inequality is not sufficient: the safe operating interval,
write-silence guard, observation errors, recovery and latency must also fit.
For repair every `q` periods, the corresponding worst-case balance is
`D_min >= q*H`. A finite-horizon feasibility claim must be labeled separately
if this steady-service condition fails.

An early-refill guard must protect both the upper operating boundary and the
actuator's silence domain, for example

```
upper + D_max <= C     and     upper < M,
```

with the appropriate loss/timing margins added. The lower-state recurrence
uses `D_min`, while a post-delivery upper bound uses `D_max`. The same nominal
dose must not be used for both ends of an uncertain interval.

The present `research/fixed-boundary-v5/Model.lean` is specialized to fixed
integers: H=150, dose=220, capacity=660, floor=100, errors=2/1, and one-period
write delivery. `postDelivery`, `freshLower`, `freshUpper`, `carry`, `Ready`,
`Certified`, `samples`, and `Physics` all encode those choices. A physical
port requires a parameterized/generalized contract, including variable doses,
physical action admissibility, observation timing and a refinement theorem
from circuit observations to service. Merely changing constants in the bridge
or rescaling measured voltages does not reuse the existing theorem as stated.
The state also needs the timing/recovery certificate `Theta`, even if the
runtime policy sees only its verified projection onto reserve bounds.

## 5. Observer A, observer B, and honest refusal

**A: analog voltage readout.** Declare the sampling instant, quantization and
error budget. Direct simulator access to `Vmem` is instrumentation, not a
modeled ADC. The reserve error must include voltage-readout error, threshold
calibration uncertainty, scale uncertainty if applicable, and numerical
integration/interpolation uncertainty. A finite-step comparison is evidence
about convergence, not a universal solver-error proof.

A voltage probe alone does not supply v5's independent instantaneous
`rateReport`. Two voltage samples, with the intervening dose accounted for,
give a cumulative loss or average rate; their endpoint errors add. A very
recent leakage jump can be diluted in that window. If an extra current probe
or known resistor value is used, declare that extra observation explicitly;
reading a scenario's hidden leakage setting is not a voltage-only observer.

For a rate estimate with `abs(report - actual) <= epsilon_rate`, the sound
refusal test is

```
report - epsilon_rate > H.
```

This cannot detect every arbitrarily small excess over H. A pointwise guarantee
for every allowed measurement error needs `actual > H + 2*epsilon_rate` at
the observation (and a suitable full observation window for an averaged rate).
Thus "refuse at the first probe after leaving H" requires a separated,
appropriately timed outside-boundary control, or must be weakened to "refuse
at the first probe that certifies a violation." No service guarantee is
claimed after leaving H, including before its detection.

**B: FIRE/silence only.** One bit identifies an inequality relative to a
stimulus- and state-dependent threshold. It does not reveal a numerical
reserve or leakage rate. Multiple calibrated probe amplitudes/timings could
narrow an interval, but those probes consume time and can write or leave the
cell protected. Their effects and costs need a new observer contract. A
silence observed during mandatory service is already a service failure, so it
cannot be used as a harmless trigger for the zero-miss guarantee.

## 6. Price and stopping criteria

Report the separate counts of successful/failed service pulses, maintenance
commands, actual writes, analog probes and elapsed periods. Use symbolic
prices such as

```
Cost = N_service*c_service + N_probe*c_probe
       + N_maintenance*c_maintenance + T*c_idle.
```

Avoid adding a second write price if the maintenance price already includes
the write's energy. A priced comparison must use the same service schedule,
state boundary, observer and terminal-inventory convention for early and
prudent policies. V5's arbitrary probe/write weights 1/10 are not measured
circuit costs. If cell supply energy is integrated, identify which ideal
stimulus sources, clock drivers and ADC costs are excluded; do not call that
partial value total hardware energy. The cheapest feasible safe policy in this
new action family may differ from the existing v5 prudent policy.

Stop before preregistration if there is no maintenance stimulus with a
certified safe-service / silent-write overlap and adequate timing, if the
worst-case loss/dose/observation envelopes make the guards infeasible, or if
the estimated campaign exceeds the time budget after choosing an explicit
horizon and cell count. A failure of one nominal candidate is not proof that
no possible stimulus exists. Publish the tested candidate family and scope
of any negative result. The user reviews this phase-0 map before a prospective
protocol, controller implementation or new jump campaign is authorized.
