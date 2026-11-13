# R refresh calibration from existing records

Descriptive analysis performed after the v2 experiment. No circuit run, v1/v2
rerun or tuning was performed. This analysis does not change either protocol.

## Method and units

`circuit/run.py` defines a period as 440 microseconds; its 20-microsecond
latency unit is different. `step1_mV = 1000*(previous_vmem1-current_vmem1)`:
positive steps move toward higher gain. All recorded steps span a complete
period. We use only periods at/after the first FIRE, exactly as the existing
`refresh_view` analysis does. Silent periods thereafter are relapses.

Leakage proxy = negative of the step on a firing period. A relapse step is
the **net** write increment after that period's losses. An inferred gross dose
adds the mean firing-period leakage proxy to the mean relapse increment.
That addition assumes comparable drift in firing and writing periods; it
does not measure the delivered write charge independently.

| Record | Relapses | Mean gap (periods) | Mean leakage proxy (mV/period) | Mean net relapse step (mV) | Inferred gross dose (mV) |
|---|---:|---:|---:|---:|---:|
| refresh_lk11 | 7 | 22.833333 | 0.058899 | 1.288000 | 1.346899 |
| refresh_lk11_nz | 7 | 22.833333 | 0.060094 | 1.304143 | 1.364236 |
| refresh_lk12 | 3 | 221.000000 | 0.006096 | 1.341000 | 1.347096 |
| refresh_mm_3001 | 4 | 21.666667 | 0.062189 | 1.300250 | 1.362439 |
| refresh_mm_3002 | 4 | 22.666667 | 0.059330 | 1.312000 | 1.371330 |
| refresh_mm_3003 | 4 | 23.666667 | 0.056495 | 1.289500 | 1.345995 |
| refresh_mm_3004 | 4 | 23.666667 | 0.060609 | 1.350500 | 1.411109 |
| refresh_mm_3005 | 4 | 24.000000 | 0.058815 | 1.323000 | 1.381815 |
| refresh_mm_3006 | 4 | 23.000000 | 0.059860 | 1.322500 | 1.382360 |
| refresh_mm_3007 | 4 | 22.666667 | 0.058613 | 1.309500 | 1.368113 |
| refresh_mm_3008 | 5 | 22.250000 | 0.064022 | 1.367600 | 1.431622 |
| refresh_none | 0 | — | 0.000226 | — | — |
| refresh_none_nz | 0 | — | -0.000144 | — | — |

## Nominal 0.1 teraohm interpretation

Observed relapse gaps: [23, 23, 23, 23, 23, 22]; mean 22.833333 periods.
Observed firing-period loss proxy ranges from 0.058000 to 0.059000 mV,
with mean 0.058899281 mV/period.
Net relapse step is 1.288000 mV. The inferred gross dose is
1.346899281 mV, close to the separately stated nominal dose 1.3465 mV.
The inferred gross-dose/leak ratio is 22.867839 periods.
Using 1.288 mV as both a net increment and an independent delivered dose would
double-count leakage in a model that already subtracts it every period.

With 220 units representing the declared 1.3465 mV nominal dose, the mean loss
proxy is 9.623351 abstract units per period, versus the
preregistered approximation 10. This is a voltage scale calibration only:
it does not map the service floor 100, initial reserve 440 or capacity 660 to
the physical two-port read specification.

The 1-teraohm record supplies an independent consistency comparison:
gaps [221, 221], mean loss 0.006095841 mV/period, inferred gross dose
1.347095841 mV. Quantization/rounding is material at this smaller drift.

## What this does not establish

- Observed minima/maxima are finite-sample extrema, not universal physical bounds.
- Noisy firing-step proxies can be negative; they combine read noise and drift.
  They cannot be used directly as a nonnegative per-tick leakage oracle.
- The CSVs summarize periods and do not certify intra-period safety, delivered
  dose timing, a sensor error bound or the scalar-to-hybrid state correspondence.
- These constant-leak runs do not establish B=10 over H=41 under temperature
  changes, ageing or an injected leakage jump.
- The next physical bridge must obtain waveform-based dose/loss enclosures,
  justify the observer and state map, then preregister a transistor jump trial.

The accompanying JSON records every source hash, relapse index, gap and range.
Regenerate with `python3 -B calibrate_refresh.py`; this reads stored records only.
