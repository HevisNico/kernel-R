# Previously saved evidence for the SKY130 supervisor map

This is a descriptive phase-0 read of historical records. No simulator or
controller is run. Regenerate or verify from the repository root:

```sh
python3 -B research/sky130-supervisor-map/saved_evidence.py
python3 -B research/sky130-supervisor-map/saved_evidence.py --check
```

[SAVED_EVIDENCE.json](SAVED_EVIDENCE.json) contains every silent index,
gap, range, timing, and SHA-256 of every input used here.

## Service loss and voltage proxies

| Saved record | Periods from first FIRE | Silent service periods | Mean loss proxy (mV/period) | Inferred gross dose (mV) |
|---|---:|---:|---:|---:|
| refresh_lk11 | 146 | 7 | 0.058899 | 1.346899 |
| refresh_lk11_nz | 146 | 7 | 0.060094 | 1.364236 |
| refresh_lk12 | 556 | 3 | 0.006096 | 1.347096 |
| refresh_mm_3001 | 94 | 4 | 0.062189 | 1.362439 |
| refresh_mm_3002 | 95 | 4 | 0.059330 | 1.371330 |
| refresh_mm_3003 | 97 | 4 | 0.056495 | 1.345995 |
| refresh_mm_3004 | 96 | 4 | 0.060609 | 1.411109 |
| refresh_mm_3005 | 96 | 4 | 0.058815 | 1.381815 |
| refresh_mm_3006 | 97 | 4 | 0.059860 | 1.382360 |
| refresh_mm_3007 | 97 | 4 | 0.058613 | 1.368113 |
| refresh_mm_3008 | 94 | 5 | 0.064022 | 1.431622 |
| refresh_none | 146 | 0 | 0.000226 | none |
| refresh_none_nz | 146 | 0 | -0.000144 | none |

At 0.1 Tohm, the first FIRE is pulse index 4 (zero based).
The later silent indices are [9, 32, 55, 78, 101, 124, 146], with gaps
[23, 23, 23, 23, 23, 22]. A silent service period is a failure even
though it also recharges the cell. The initial training silences are excluded
from the table and require an explicit service-start convention.

The firing-period loss proxy is the negative of the recorded full-period
`step1_mV`. The silent step is a **net** increment. Adding the mean firing
loss gives an inferred gross dose under a comparable-drift assumption, not
a separate delivered-charge measurement. Using that net increment as a
gross dose would subtract leakage twice.

The voltage is an end-of-period average. Its range is not capacity, and
noisy differences are not instantaneous leakage measurements. These data
supply neither a service threshold at pulse arrival nor a sensor-error
bound. Finite extrema do not establish universal bounds.

## Historical runtime, before a local estimate

| Saved replay | Max step (ns) | Calendar periods | Wall seconds | Linear 200-period estimate (minutes) |
|---|---:|---:|---:|---:|
| nominal_200ns_retry1 | 200 | 22 | 147.96 | 22.42 |
| nominal_100ns_retry1 | 100 | 22 | 190.25 | 28.83 |
| mm2064_quiet_retry1 | 200 | 22 | 147.44 | 22.34 |
| mm2064_noise_1_retry1 | 200 | 22 | 216.03 | 32.73 |
| mm2064_noise_2_retry1 | 200 | 22 | 200.67 | 30.40 |

The successful ngspice42 replays simulated 0.00968 seconds each. Four
started together on the historical host; the second noisy repeat started
later. Millisecond failed starts that produced no transient are excluded.
At the slowest saved rate, eight 200-period sequences cost 4.36
serial hours, or 2.18 hours under ideal two-machine balancing,
**before any reserve**. These are extrapolations, not current-host budget
guarantees. Two policies count as two sequences. Added maintenance pulses
and waveform instrumentation may change runtime. A local representative
timing plus an explicit margin must replace this estimate before preregistration.

## Cost and state conventions still to fix

Count mandatory service pulses, maintenance attempts, actual writes, analog
observations, preparation and elapsed service periods separately. A firing
maintenance attempt still costs an action. The old weights probe1/write10
are discrete prices, not transistor energy; an energy claim requires supply
power integration including idle/bias and observer overhead.

Any prudent comparison needs the same service schedule, physical action
library, hard boundary, initial state and terminal-inventory convention.
Inserting maintenance within a former 440-us period also changes main-charge
recovery. The old pre-pulse rest band must not be imported without checking
`vq` and the protection state under the new schedule.
