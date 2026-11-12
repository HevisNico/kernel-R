# Coincidence timing with realized thresholds

[Back to the native package](../README.md)

## Coincidence timing with an ERROR exit near 0.01

[CoincidenceTiming.lean](CoincidenceTiming.lean) brackets the actual read
FIRE using the charge at read, the learned gain, and the FIRE threshold.
The lower time uses the largest charge and gain and the smallest
threshold. The upper time uses the opposite bounds. The exponential
estimates are proved over the reals in Lean.

`training_read_exit_001_benchmark` fixes the trained port's birth gain
exactly at `exp (gains p) = 6/5`. This satisfies the earlier birth band
`[7/6, 1.2]`. The timing certificate uses the exact value. With a
read at least 16.65 units after training, it gives one FIRE between
0.3485 and 0.398 units after the read in every run complete through
the first FIRE. Both fabrication boxes are covered. With radii `e`
and `f`, the entry and exit tolerances are `0.1e` and `0.025e`
around 0.1 and 0.01 respectively, and the FIRE tolerance is `f`
around 1. All other guards are nominal.

| Maximum ERROR radius `e` | Maximum FIRE radius `f` |
| ---: | ---: |
| 1% | 3% |
| 2% | 2% |
| 3% | 1% |

Lean counts 22 of the 36 registered grid points in these sufficient
rectangles. At 100 microseconds per unit and nominal exit 0.01, these
are exactly the same 22 ERROR/FIRE pairs that passed in the
[recorded sweep](https://github.com/HevisNico/kernel-R/blob/8ff0540cab31f55831ffd3698b36bd2940c872d1/research/recursive-learning/coincidence/results/exit-tradeoff.csv.xz)
at each of its three fabrication settings. The Lean count gives
coverage on this grid. A full characterization of the passing region
would also require proving where the timing contract fails.

`coincidence_of_trained_latency` is an arithmetic lemma with two
latency intervals as hypotheses. At 100 microseconds per unit,
with a common wire delay and independent jitter of up to 5
microseconds, the skew is at most 14.95 microseconds at zero
offset and at least 15.05 microseconds at offsets of −30 or +30
microseconds. These bounds give a certified margin of 0.05
microseconds around the 15 microsecond aperture. The certificate
uses the declared uncertainties only.

The execution theorem is for a single trained-port read through its
first FIRE. A joint two-cell execution, wrong-port trials, the rest
of the observation horizon, and a native receiver have separate
proof obligations. The comparison below addresses the reduced timing contract.

### Constant-current timing obstruction

[TimedCurrentSeparation.lean](TimedCurrentSeparation.lean) uses the
[registered constant-current rule](https://github.com/HevisNico/kernel-R/blob/1f04221262694383b1505a8d064f62903a85a34a/research/recursive-learning/COINCIDENCE_BENCHMARK.md#comparators)
and the same `readyPulse` equation as the R latency theorem. In the
reduced runner, a shared current and duration give a common dose
`d = I * D`, scaled by each device's current multiplier and clipped at
its realized gain cap. The runner requires silent training and positive
reserve. The protocol requires the timer to finish by time 16.

At 100 microseconds per unit, use the wide fabrication box, 10%
current error, 3% FIRE error, ERROR entry 0.1 and exit 0.01. Put the
high-current, high-cap, low-FIRE corner on the early read and reverse
all three signs on the late read. The two reads are at 16.95 and
17.05 with zero offset. Lean proves that for **every shared dose**
this positive trial either lacks a report or has skew at least
15 microseconds. The proof includes capped writes. For doses up to
0.36 it rules out the slow report directly. Seven bounded dose
intervals and one unbounded interval cover the remaining doses.

The obstruction applies to the constant-current **reduced** timing
model with eligible writes, quiet relaxation after training, and a
frozen learned gain during the read pulse. Its training endpoint charge
lies in [0.1, 1.03]. The timed rule has no separate hybrid execution
construction here.

### Two-cell execution assembly

[ParameterExecutionProduct.lean](ParameterExecutionProduct.lean) weaves
two independent parameterized executions at a common clock. The joint
queue retains both cells' deliveries, and the two FIRE lists retain
their exact dates. Local completeness through the same horizon gives
joint completeness.

[CoincidenceReadTail.lean](CoincidenceReadTail.lean) proves that a
trained-port FIRE cannot be followed by another FIRE in any legal
finite continuation of the task. The read pulse ends before FAST can
end. After pulse expiry the cell has no drive and any return to READY
starts below FIRE.

[CoincidenceNetworkContract.lean](CoincidenceNetworkContract.lean)
derives the registered receiver decision at time 20 for every complete
joint run, given two local witnesses complete through that horizon
with the declared FIRE lists. The receiver uses the 0.35 wire delay
and 20.35 arrival deadline.

[CoincidenceLocalExecution.lean](CoincidenceLocalExecution.lean)
constructs a complete wrong-port trial through time 20 with an empty
FIRE list. It retains the actual training trajectory, retargets only
the queued read and bounds the charge during the live-pulse overlap
with ERROR. The wrong port uses its nominal auxiliary guards. The
birth-gain, fabrication and threshold hypotheses of the 0.01 timing
certificate cover the registered read dates from 16.65 to 17.35.

[CoincidenceProtectedTail.lean](CoincidenceProtectedTail.lean) advances
a trained-port run to time 20 after its FIRE. The construction processes
pulse expiry, FAST exit and sensor contacts in time order, including
ties. SLOW remains above its reopening threshold through the horizon.

[CoincidenceSeparation.lean](CoincidenceSeparation.lean) proves
`coincidence_exit_001_full_contract` for two independent cells. A
complete run exists for every admissible pair of read dates and ports.
In every complete run each trained-port read gives exactly one report
and each other read gives none. The receiver accepts exactly when both
ports match the training and the offset is zero. The 0.35 delays and
the coincidence test are applied to the emitted dates by the receiver
contract.

The combined theorem `coincidence_exit_001_separation` uses 100 µs per
model unit, ±10% fabrication and ±3% FIRE threshold error. On each
trained port, the ERROR entry can vary by up to 0.001 around 0.1 and
the exit by up to 0.00025 around 0.01 (radius `e ≤ 0.01` in Lean).
The other ports keep their nominal auxiliary thresholds. Native R
satisfies the full receiver contract throughout this box.

For the reduced constant-current rule with ±10% current variation, one
positive trial with nominal ERROR endpoints excludes every common
current and duration, including settings that touch the gain cap.
Those endpoints belong to every admitted ERROR box. The proof uses
the exact trained birth gain 1.2. The receiver is an observation of
two native runs and the comparator uses the reduced READY equation.


## Common threshold offset and reaction delay

[OffsetAndDelay.lean](OffsetAndDelay.lean) refines the one-pulse training
theorem in two ways. Both use the parameterized first-contact semantics
and the sixteen-unit schedule. The FIRE threshold lies in `[0.95, 1.05]`,
the trained port's birth gain in `[7/6, 1.2]`, the other guards are
nominal, and both fabrication boxes are covered.

**A common shift cancels.** Write the realized ERROR entry as
`0.1 + δ + a` and the exit as `0.025 + δ + b`. With `|δ| ≤ 0.004` and
`|a|, |b| ≤ 0.001`, `training_read_common_offset` gives a complete run,
and in every complete run the log-gain increment is `0.6 + 8 * (a - b)`.
The common shift `δ` does not appear. It may reach 4% of the entry level
and 16% of the exit level. With `a = b = 0`,
`training_read_pure_common_offset` gives exactly `0.6` for `|δ| ≤ 0.005`.

The earlier theorems bound each endpoint separately. This one separates
the part of the error that the two endpoints share from the part they do
not. Only the second part changes the dose. A cell that detects both
endpoints with one comparator has mostly shared error.

**A reaction delay bounds the dose.** Suppose the cell reacts a fixed
time `d` after each ERROR endpoint crossing. The sensor keeps decaying
during that time, at the SILENT rate `ls` before the entry and at the
ERROR rate `le` before the exit. The realized endpoints are then
`0.1 * exp(-ls * d)` and `0.025 * exp(-le * d)`. For `0 ≤ d ≤ 0.01`,
`training_read_reaction_delay` gives a complete run, and in every
complete run the increment `Δz` satisfies

```text
-0.8 * ls * d  ≤  Δz - 0.6  ≤  0.2 * le * d        and        |Δz - 0.6| ≤ 2.4 * d
```

The exact increment is `8 * (0.1 * exp(-ls * d) - 0.025 * exp(-le * d))`.
With a reaction delay the dose depends on the discharge rates, and the
dependence vanishes linearly with `d`. The nominal ERROR phase lasts 0.15
model units, so `d = 0.01` is about 7% of it.

The delay is represented through the realized thresholds.
`delayedLevel_of_decay` shows that an exponential decay which meets a
level reaches `level * exp(-rate * d)` after a further time `d`. The
semantics still jumps at guard equality. A semantics with delayed jumps
is not constructed, and the delay is the same at both endpoints and
fixed in time.
