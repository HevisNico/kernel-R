# Phase 0: can the simulated SKY130 cell accept a v5 supervisor?

**Exploratory action map, for review before any preregistration.** There is no
new `PREDICTION.md`, jump campaign, v5-driven transistor run, or physical safety
certificate in this change. All completed probes are nominal TT, 27 C, without
noise. The original circuit and all historical campaigns remain unchanged.

The immediate actuator question has a positive **nominal** answer. A weaker
input can remain silent and write while an ordinary service input still FIREs.
A second candidate, the existing ideal timing signals with zero input current,
also writes before the next successful service. No transistor was changed.
The voltage observer, physical envelopes and generalized Lean contract remain
to be qualified. Merely replacing v5's constants would not close that bridge.

## Actions, chronology, and observed effects

Only port 1 is serviced; port 2 is idle. A service means exactly one FIRE in
the 20 us input window. A later silent-pulse write cannot rescue that service.
The service period remains 440 us. The diagnostic paired schedule is service
at 444.1 us, maintenance at 664.1 us, service at 884.1 us, after initial rest.
Maintenance is explicitly not a requested service. The original reset,
precharge and admission clocks are reused at 220 us slot spacing. This changes
the stimulus schedule, not the transistor design, and requires new timing
qualification. The ammeter is a zero-volt source at the integrator input.

| Action | Ideal stimulus | Observed effect | Physical timing |
|---|---|---|---|
| Service | Original amplitude, 20 us | FIRE if sufficient margin; otherwise a failed service followed by a write | FIRE must occur by 20 us; sensor write window about 35.55–40.80 us |
| Reduced maintenance | 95% of the original input-current waveform | Silent and writes near service threshold; FIRE and no write at higher reserve | Same sensor window; recovery checked before next service |
| Clock-only maintenance | Same timing signals, input current zero during admission | Silent and writes in the tested states | Same sensor window; does not require a service failure |
| Wait | No selected port/timing cycle | Stored voltage rises with imposed leakage | Throughout the 440 us service period; mandatory service may not be omitted in a future controller |

Clock-only means an externally selected ideal timing cycle, not an autonomous
pulse detector already implemented on silicon. These ideal signals existed in
the original testbench. A future chip needs a means to request that action.

Selected observations from [all results](RESULTS.json):

| Probe | Before action, mV | Outcome | Net reserve gain over action observation interval, mV |
|---|---:|---|---:|
| Ordinary service | 384.570523 | FIRE | -0.058124 |
| Ordinary service | 384.770515 | Silent, failed service | +1.288582 |
| Reduced maintenance alone | 384.070543 | Silent, writes | +1.288527 |
| Reduced maintenance alone | 382.070622 | FIRE, no write | -0.05812 |
| Clock-only between two services, R=1e11 ohm | 384.099946 | Silent, writes; both services FIRE | +1.317967 |
| Clock-only between two services, R=1e10 ohm | 383.897853 | Silent, writes; both services FIRE | +1.060108 |

The paired action intervals are approximately half a service period, unlike
the isolated full-period action intervals. Their different net increments
must not be interpreted as different gross doses without accounting for loss.
The 11-action timing diagnostic has six successful services but only **one
write from five reduced-maintenance attempts**: the other four maintenance
inputs FIRE. Thus the capacity guard alone does not guarantee actuation.
Clock-only is the simpler candidate to qualify next; it is not yet proved
silent over a continuous state/noise/corner domain.

Protection is low before the paired actions, but the main node before a
subsequent pulse is about 1.2465 V, not the fully rested 1.25 V. The old rest
certificate cannot be reused unchanged. A service-threshold enclosure must
cover this residual charge and the whole new calendar.

For comparison, saved self-refresh has seven silent periods among the 146
periods at/after first FIRE, indices 9,32,55,78,101,124,146. Those are service
failures, not successful supervision. The first four training silences are
additional setup failures. [Saved evidence](SAVED_EVIDENCE.md) retains the
other original cells and noise records too.

## State, observation, and the proposed operating domain

Lower `Vmem` means **higher** gain. The reserve coordinate has the opposite
sign to stored voltage:

`reserve_mV = 1000 * (V_service_reference - Vmem)`.

Dividing by 1.3465 mV expresses nominal doses; dividing by 1.3465/220 mV
reproduces the old abstract scaling, but does not establish a physical state
correspondence. FIRE depends also on the main charge, protection and timing.

The isolated nominal probes give a passing point at 384.570523 mV and a failing
point at 384.770515 mV. Calling their midpoint 384.670519 mV a reference gives
a 0.10 mV **finite diagnostic bracket**, conditional on a monotone threshold;
it is not a uniform service theorem. A proposed 4 mV operating reserve band
corresponds to about 380.670519–384.670519 mV. This is a selected operating
domain to qualify, **not a measured op-amp rail or a hard clipping law**.
The clock-only probe at 380.070703 mV reaches 378.782184 mV: the actuator has
no demonstrated automatic clamp at the proposed capacity.

Set S=0 in this coordinate, with threshold/observer uncertainty subtracted
from the certified lower reserve. For the original paired probe the initial
read is about 0.600 mV above the nominal reference; it is not enough for the
proposed stronger H=0.65 mV contract. The price example's initial reserve
2 mV is a **target requiring separately costed preparation**, not inherited
from the original preset. Service must begin only after preparation is
certified; no training silence may be hidden inside guaranteed operation.

**Observer A is first:** read `Vmem` from the simulator, with explicitly
declared observation error and no simulated ADC. This does not measure chip
energy, ADC error, or instantaneous leakage. Threshold uncertainty and solver
error are additional obligations. Two voltage readings estimate accumulated
loss only after accounting for all intervening writes and transients.

**Observer B is different:** a FIRE/silence bit gives a threshold inequality,
not a numeric reserve. Its pulses disturb charge and may write. It needs an
interval observer and enough discriminating maintenance probes, with their
cost and latency. The A results must not be presented as a B implementation.

## Charge balance and what is still missing

The feedback capacitor is 30 pF between `sum` and `vmem`. The imposed resistor
draws `Vsum/R`, not `Vmem/R`. Save both capacitor terminal voltages and use
`Delta Vmem = Delta Vsum - (Qwrite - Qleak + Qother)/Cf`.

Idle observations give 0.058806 mV loss per 440 us at R=1e11 ohm, and
0.586735 mV at R=1e10 ohm. Integrated imposed-resistor contributions are
0.058683 and 0.586828 mV respectively. These are finite nominal measurements.
The net-plus-resistor write proxy is about 1.3465–1.3467 mV. It is **not** an
independent delivered-dose bound.

There is a numerical obstacle worth retaining. The ammeter has trapezoidal
ringing. Integrating it with arbitrary interpolated endpoints produced
spurious multi-dose answers in the first auxiliary extractor. Those legacy
`gross_write_*` metadata fields from `probe.py` are explicitly discarded by
`analyze_saved.py`. The authoritative results use complete native solver
intervals, report the omitted tail duration, and make no enclosure claim.
For paired clock-only maintenance, this current integral corresponds to
1.347799 mV at 200 ns and 1.351102 mV at 100 ns: a 0.003303 mV difference.
The net-plus-resistor proxy changes by about 0.000002 mV instead. Stable
voltage steps alone therefore do not validate a precise current-dose bound.
Phase 1 must close the integration tails/residual balance and solver margin.

| Quantity | Phase-0 status | Required before a physical contract |
|---|---|---|
| H | Finite nominal losses; analytic resistor contribution conditional on Vsum | Whole-period and within-period loss envelope, other currents, corners, mismatch and declared noise domain |
| Dose | Observed net steps and independently instrumented but numerically sensitive current | Dmin/Dmax with charge-balance residual and integration margin |
| Sensor error | Simulator node access; no ADC model | Declared bounded observation model, threshold/timing error, rounding and numerical allowance |
| Capacity | Proposed safe operating interval | Prove/qualify operation throughout it and guard against overshoot; do not assume clipping |
| Service threshold | Passing/failing nominal points | New-calendar threshold enclosure including main-charge and protection state |
| Initial reserve | Preset measured; stronger target unprepared | Preparation sequence, its cost, and service-start certificate |

A finite collection of corner/noise runs cannot prove universal extrema.
Unbounded Gaussian noise cannot satisfy an unconditional finite error bound.
Phase 1 must identify which enclosures are model assumptions, justified
analytic bounds, finite-path measurements, or probabilistic statements.

## Price of the boundary

The observed 880 us diagnostics cost 326.998 nJ for idle, 339.056 nJ for one
successful service, and 342.616 nJ for one silent reduced-maintenance input
at the same preset. These are integrated **whole-run supply energies**,
including initialization and continuously biased analog circuitry. Their
differences are only nominal incremental diagnostics. They exclude ideal
stimulus/clock generators, instrumentation/ADC and any digital supervisor.
Do not identify these energies with v5's arbitrary probe/write prices 1/10.

[PRICE_INPUT.json](PRICE_INPUT.json) is an engineering qualification target:
H=0.65, Dmin=1.30, Dmax=1.40, C=4.0, epsilon=0.10 mV, S=0. The resistor
component would be at most 0.601333 mV if Vsum<=0.41 V and R>=1e10 ohm;
the remaining 0.048667 mV is a **proposed allowance, not a justified bound**.
The dose interval similarly surrounds observations but is not certified.

Under these hypothetical envelopes, the arithmetic leaves 3.8 mV of fresh
lower reserve at capacity versus 1.3 mV needed for one wait plus one repair
period. Dmin exceeds H by 0.65 mV. Thus the numerical target is not ruled out
by these guards. Timing, actuator silence, negative effective drift and actual
enclosures are still required. [Contract gaps](CONTRACT_GAPS.md) spells them out.

For 40 periods at worst loss, equal initial/terminal targets 2 mV require
26 mV gross replacement: at least 19 maximum-size writes, or 20 minimum-size
doses before saturation. Assuming the **same feasible** 20-write schedule and
matched final inventory, 20 spaced decision probes instead of 40 prudent
probes give a ledger of 261 versus 281 at declared service/probe/maintenance
prices 1/1/10, including one terminal observation. This is a **conditional
ledger, not an achieved 7.12% physical saving or a policy cost bound**. In
particular, the initial lower reserve 1.8 mV cannot immediately support the
selected two-period wait requiring 1.95 mV; preparation or a shorter first
action is needed. The same terminal target alone also does not ensure equal
unused stock: uncertain doses give an unsaturated terminal interval [2,4] mV.

The physically achieved early/prudent ratio remains open. To compute it,
qualify the action/observer domain, implement the generalized kernel and fix
the preparation and terminal-stock convention. If observations are priced
zero in simulation, the illustrated probe-only saving disappears entirely.

## Runtime estimate and review gate

Sixteen nominal waveform diagnostics completed, plus three retained setup
failures before any transient (temporary-file setup, then a missing global
stimulus node). Aggregate charged wall times are about 912 s; some jobs ran
concurrently. The 11-action case took 140 s for 6.5 original periods.
Observed ratios are 15–34.1 s per original 440 us period, including startup
and varying contention. This is not a noisy-corner timing guarantee.

A provisional budget uses 35 s/period, a declared 1.5 noise factor, 25% reserve,
and 30 s extra startup per run. Six sequences of 32 service periods plus one
setup period cost about **3.66 aggregate machine-hours**. Splitting between
two machines may reduce elapsed time, not this total. A possible allocation
is nominal supervisor/prudent, two mismatch supervisor runs, one outside
control and one self-refresh control. No seeds, jump times or new trajectories
have been calculated for that candidate campaign. This horizon is intentionally
shorter than hundreds of periods **per cell**; hundreds per cell do not fit
the conservative serial estimate.

The unmeasured noise factor must be checked with phase-1 calibration timing
before preregistration. If the updated estimate exceeds four hours, reduce
the horizon/cell count before publishing `PREDICTION.md`; never trim afterward.

**Review decision:** a nominal maintenance actuator exists, so the immediate
"no actuator" stop is not triggered. Uniform enclosures, a physical controller
cost bound and its Lean refinement are not closed. Stop at this phase-0 draft
for owner review. No registered campaign is authorized by this document.
Future refusal can be sound for a measured lower loss above H; it cannot be
promised for every arbitrarily small or very recent excursion at the first
voltage-only probe. Specify a separated outside control and observation window.

## Reproduce and check

[REPRODUCE.md](REPRODUCE.md) gives the exact simulator setup, diagnostic commands
and every waveform SHA-256. Exploratory raw traces stay uncommitted. No command
here launches the old v5 campaign or a new registered jump campaign.

```sh
python3 -B research/sky130-supervisor-map/saved_evidence.py --check
python3 -B -m unittest discover -s research/sky130-supervisor-map -p 'test_*.py' -v
python3 -B research/sky130-supervisor-map/analyze_saved.py --check
```

The last command requires the original local diagnostic evidence. A regenerated
copy uses `--check-traces` instead, which checks the exact 16-file waveform
inventory and hashes while ignoring new execution times and old setup failures.
