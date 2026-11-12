# The circuit against the need theorem

Written by `bridge_application.py` from the pushed results. Theorem: `needAlong_of_circuit_tolerances` in
[`lean/CircuitNeed.lean`](lean/CircuitNeed.lean), the variant of `needAlong_of_circuit_residual` with `sigma` and `e`.

## Summary

1. **Certified:** the theorem, its cumulative variant `needAlong_of_cumulative_tolerance`, the lemma `ChargeWindow.local_slope_step` that bounds the calibration error by `epsilon` times the step, and their audits: no `sorry`, no project axiom, eight negative controls rejected.
2. **Verified on the five replays:** the rest band (105 of 105 states), one FIRE of the latch per read, one write per silent pulse and none on a firing pulse.
3. **Supported, on the replays only:** `k*eta`, `sigma` and `e`. On the nominal replays their sum is 5.0e-03 per write, a quarter of `d0/2`, half of it calibration error. `m*b` is the largest term of the budget on 180 ports; for the median port `b` would have to be divided by 2.0.
4. **Not certified:** no port of the 100 cells is in the certified domain, 0 of 200: the original trajectories have no waveform, `a` and `d0` are proxies, `ell` is measured for one cell. Under estimates only, the room is positive on 19 ports with the per-write budget and on 69 with the cumulative budget; the observed count equals `m` on all of them.
5. **`mc_2064`, port 1:** historical room +0.000233 with `ell = 0`; -0.000100 with `ell_static` measured on the cell. Its count stays 3 against `m` = 4, and its historical status is not changed. The three replays of its mismatch seed give 4.

## Hypotheses

Verified: established on the available data. Supported: measured on a finite set of replays, on nominal devices, or through a proxy. To measure: no measure exists for the ports in question. Out of reach: cannot come from a finite simulation.

| Hypothesis | Class | Bound | Source and limit |
|---|---|---|---|
| `scale`: `0 <= k`, with `k = beta / Cf` | verified | `beta` = 31.377 per V at 27 °C; all 324 adjacent-grid secants of the nine DC curves are negative | `bridge_check/local_summary.json`. Nominal devices, finite grid |
| `fire`, `fire0`: `19/20 <= level`, `level0` | verified for `level0`; for `level`, on cell 2064 only | `level0` from 0.9682 to 1.0338 over the 200 ports; smallest level at a FIRE in the replays of cell 2064: 1.00042 | `need_budget_ports.csv`, `bridge_check/level_summary.json` |
| `windows`: integral charge balances of the sensor and of the storage capacitor | supported | holds for the two ideal capacitors of the netlist; the device capacitances on the same nodes are counted in the residual | `cell.spice`, `bridge_check/GAIN_PROTOCOL.md` |
| `residual`: transferred-charge error, `k * eta` | supported | 1.32e-03 on the nominal replays, 1.38e-03 on cell 2064 without noise, 1.40e-03 with noise | `bridge_check/window_samples.csv`. Five replays; not measured on the 100 original runs |
| `sensorTol`: sensor-dose error `sigma` | supported | 7.47e-05 nominal, 9.37e-05 on cell 2064 without noise, 4.69e-04 with noise, around `beta * (Cs/Cf) * 0.1` = 0.04184 | `bridge_check/window_samples.csv`. Five replays |
| `handoff`: linkage error `e`, window to read-to-read increment | supported | 9.83e-04 not explained by the window, plus 2.61e-03 of local calibration (`epsilon` = 1.937 per V times the step): 3.59e-03 on the nominal replays. With noise the first term is 2.33e-02, a sample of one draw | `bridge_check/window_samples.csv`, Lean `ChargeWindow.local_slope_step`. Piecewise-linear DC curves of nominal devices |
| `stepPos`: the gain does not fall at a write | supported | every read-to-read increment of a silent pulse is positive in the five replays (43 of 43); all 824 silent steps of the stored voltage are positive in the 100 original runs; `epsilon < beta` | `bridge_check/local_summary.json`, `lean/README.md`. A voltage proxy for the original runs |
| `gain`: start distance `a` to the centre of need `m` | to measure | only the peak-based proxy `a_proxy` exists. It assumes the ideal gain-to-swing relation and uses the outcomes of the same run | `need_budget_ports.csv`, `NEED_BUDGET.md` |
| `levelTol`: threshold error `ell` | supported for cell 2064, to measure for the 99 others | `ell_static` = 0.00028, measured on the replay of cell 2064 without noise; `ell_dynamic` = 0.00241, a statistic of two noisy replays, not certified for the original trajectory | `bridge_check/level_summary.json`, `bridge_check/LEVEL_PROTOCOL.md` |
| `room`: `a + m*(k*eta + sigma + e) + (20/17)*ell + 1/8000 < d0/2` | to measure | on the nominal replays `k*eta + sigma + e` = 4.99e-03 per write, against `d0/2` = 0.0209. The historical table uses another `b`, the spread of peak ratios, and `ell = 0` | this file, `need_budget_ports.csv` |
| Rest band: main charge in `[0.1, 0.1001]` before each pulse | verified on the replays, supported for the original runs | 105 of 105 pre-pulse states inside, `q` from 0.10000019 to 0.10003652, the two noisy replays included | `bridge_check/rest_samples.csv` |
| FIRE of the circuit is one event per read | verified on the replays | the protection latch rises at most once per period; the raw comparator has 6 transitions in a period with a FIRE, all within 3 ns of a latch transition, none inside an ERROR window | `bridge_check/latch_events.csv`, `bridge_check/LOCAL_RESULTS.md` |
| A silent pulse writes once, a firing pulse writes nothing | verified on the available data | steering switch turned on once per silent window and on 0 firing windows of the replays; capacitor change on a firing window at most 3.2e-07 in log-gain without noise, 1.7e-05 with noise; 0 of 3 526 firing pulses steer in the original campaign | `bridge_check/local_summary.json`, `VERDICTS.md`, `COMPLEMENT.md` |
| Scalar read equation: the main charge is the gain times one pulse shape, with a FIRE at a fixed level | to measure | not established. The slope of the gain law moves by up to 6.2% with the input current and the drain voltage, and the level at a FIRE moves with the read | `bridge_check/local_summary.json`, `bridge_check/level_samples.csv` |
| The original noisy trajectory of each of the 100 runs | out of reach | no waveform of the original runs was kept, and the seed of a run does not reproduce its noise | `COMPLEMENT.md` |
| Every future pulse under any noise; the transistor netlist as a kernel execution | out of reach | a finite simulation gives sample values, not uniform bounds | `lean/README.md` |

## The 200 ports

In the certified domain: **0 of 200**. The observed count equals `m` on 190 ports and differs on 10; a count that agrees outside the certified domain is an observation, not a consequence of the theorem.

Reasons, with the ports they apply to:

- no waveform of the original run, so `eta`, `sigma`, `e` and the rest state are not bounded on its trajectory: 200 ports;
- `a` and `d0` are peak-based proxies, and the gain law is calibrated on nominal devices only: 200 ports;
- `ell` is not measured for the cell: 198 ports;
- `ell_static` measured on the cell and room not positive: 2 ports, those of `mc_2064`;
- historical room not positive even with `ell = 0`: 105 ports; not evaluable: 1.

The full table is [`bridge_ports.csv`](bridge_ports.csv). The historical columns are those of [`need_budget_ports.csv`](need_budget_ports.csv), unchanged.

| Run | Port | Observed | m | Agrees | Historical room, `ell = 0` | Room with `ell_static` | In the certified domain | Reason |
|---|---|---|---|---|---|---|---|---|
| `mc_2001` | 1 | 5 | 5 | yes | -0.00027 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2001` | 2 | 4 | 4 | yes | -0.00973 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2002` | 1 | 5 | 5 | yes | -0.01221 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2002` | 2 | 5 | 5 | yes | -0.00502 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2003` | 1 | 5 | 5 | yes | -0.00889 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2003` | 2 | 5 | 5 | yes | +0.00466 | — | no | no waveform; proxies; ell not measured |
| `mc_2004` | 1 | 4 | 4 | yes | +0.01132 | — | no | no waveform; proxies; ell not measured |
| `mc_2004` | 2 | 3 | 3 | yes | +0.00315 | — | no | no waveform; proxies; ell not measured |
| `mc_2005` | 1 | 5 | 5 | yes | -0.02517 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2005` | 2 | 4 | 4 | yes | +0.01008 | — | no | no waveform; proxies; ell not measured |
| `mc_2006` | 1 | 3 | 3 | yes | +0.00493 | — | no | no waveform; proxies; ell not measured |
| `mc_2006` | 2 | 3 | 3 | yes | +0.01789 | — | no | no waveform; proxies; ell not measured |
| `mc_2007` | 1 | 2 | 2 | yes | +0.01812 | — | no | no waveform; proxies; ell not measured |
| `mc_2007` | 2 | 5 | 5 | yes | -0.01574 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2008` | 1 | 5 | 5 | yes | -0.01160 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2008` | 2 | 3 | 3 | yes | -0.00465 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2009` | 1 | 3 | 3 | yes | +0.01195 | — | no | no waveform; proxies; ell not measured |
| `mc_2009` | 2 | 4 | 4 | yes | -0.00239 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2010` | 1 | 4 | 4 | yes | -0.00729 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2010` | 2 | 4 | 4 | yes | -0.01399 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2011` | 1 | 5 | 5 | yes | +0.00364 | — | no | no waveform; proxies; ell not measured |
| `mc_2011` | 2 | 4 | 4 | yes | +0.00108 | — | no | no waveform; proxies; ell not measured |
| `mc_2012` | 1 | 6 | 6 | yes | -0.03495 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2012` | 2 | 4 | 4 | yes | -0.01037 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2013` | 1 | 5 | 5 | yes | +0.00790 | — | no | no waveform; proxies; ell not measured |
| `mc_2013` | 2 | 3 | 3 | yes | +0.00223 | — | no | no waveform; proxies; ell not measured |
| `mc_2014` | 1 | 6 | 6 | yes | +0.00203 | — | no | no waveform; proxies; ell not measured |
| `mc_2014` | 2 | 4 | 4 | yes | -0.00088 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2015` | 1 | 5 | 5 | yes | +0.00538 | — | no | no waveform; proxies; ell not measured |
| `mc_2015` | 2 | 5 | 5 | yes | -0.02154 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2016` | 1 | 2 | 2 | yes | +0.01595 | — | no | no waveform; proxies; ell not measured |
| `mc_2016` | 2 | 3 | 3 | yes | +0.00467 | — | no | no waveform; proxies; ell not measured |
| `mc_2017` | 1 | 3 | 3 | yes | -0.00317 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2017` | 2 | 4 | 4 | yes | +0.01172 | — | no | no waveform; proxies; ell not measured |
| `mc_2018` | 1 | 5 | 5 | yes | +0.00083 | — | no | no waveform; proxies; ell not measured |
| `mc_2018` | 2 | 4 | 4 | yes | +0.00681 | — | no | no waveform; proxies; ell not measured |
| `mc_2019` | 1 | 5 | 5 | yes | -0.00732 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2019` | 2 | 4 | 4 | yes | -0.00320 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2020` | 1 | 3 | 3 | yes | -0.00851 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2020` | 2 | 3 | 3 | yes | -0.00575 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2021` | 1 | 5 | 5 | yes | -0.01442 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2021` | 2 | 5 | 5 | yes | +0.00082 | — | no | no waveform; proxies; ell not measured |
| `mc_2022` | 1 | 4 | 4 | yes | +0.01281 | — | no | no waveform; proxies; ell not measured |
| `mc_2022` | 2 | 3 | 4 | no | -0.01401 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2023` | 1 | 4 | 4 | yes | -0.00591 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2023` | 2 | 5 | 5 | yes | -0.00033 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2024` | 1 | 4 | 4 | yes | +0.00668 | — | no | no waveform; proxies; ell not measured |
| `mc_2024` | 2 | 4 | 4 | yes | -0.01230 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2025` | 1 | 4 | 4 | yes | -0.00930 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2025` | 2 | 3 | 3 | yes | +0.01277 | — | no | no waveform; proxies; ell not measured |
| `mc_2026` | 1 | 4 | 4 | yes | -0.00571 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2026` | 2 | 4 | 4 | yes | -0.02978 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2027` | 1 | 4 | 4 | yes | +0.00518 | — | no | no waveform; proxies; ell not measured |
| `mc_2027` | 2 | 1 | 1 | yes | — | — | no | no waveform; proxies; ell not measured; historical room not evaluable |
| `mc_2028` | 1 | 3 | 4 | no | -0.00622 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2028` | 2 | 3 | 3 | yes | +0.01755 | — | no | no waveform; proxies; ell not measured |
| `mc_2029` | 1 | 4 | 4 | yes | +0.01054 | — | no | no waveform; proxies; ell not measured |
| `mc_2029` | 2 | 4 | 4 | yes | -0.00172 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2030` | 1 | 5 | 5 | yes | -0.01121 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2030` | 2 | 5 | 5 | yes | +0.00183 | — | no | no waveform; proxies; ell not measured |
| `mc_2031` | 1 | 3 | 3 | yes | +0.00486 | — | no | no waveform; proxies; ell not measured |
| `mc_2031` | 2 | 4 | 4 | yes | -0.01604 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2032` | 1 | 5 | 5 | yes | +0.00769 | — | no | no waveform; proxies; ell not measured |
| `mc_2032` | 2 | 3 | 3 | yes | +0.00001 | — | no | no waveform; proxies; ell not measured |
| `mc_2033` | 1 | 4 | 4 | yes | +0.00242 | — | no | no waveform; proxies; ell not measured |
| `mc_2033` | 2 | 4 | 4 | yes | +0.00543 | — | no | no waveform; proxies; ell not measured |
| `mc_2034` | 1 | 3 | 3 | yes | +0.00183 | — | no | no waveform; proxies; ell not measured |
| `mc_2034` | 2 | 5 | 5 | yes | -0.01013 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2035` | 1 | 3 | 3 | yes | +0.01008 | — | no | no waveform; proxies; ell not measured |
| `mc_2035` | 2 | 4 | 4 | yes | +0.00655 | — | no | no waveform; proxies; ell not measured |
| `mc_2036` | 1 | 5 | 5 | yes | -0.01178 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2036` | 2 | 6 | 6 | yes | -0.02777 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2037` | 1 | 4 | 4 | yes | -0.01232 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2037` | 2 | 5 | 5 | yes | -0.01291 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2038` | 1 | 6 | 6 | yes | -0.00949 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2038` | 2 | 4 | 4 | yes | -0.01381 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2039` | 1 | 5 | 5 | yes | -0.00387 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2039` | 2 | 6 | 6 | yes | -0.01727 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2040` | 1 | 3 | 3 | yes | +0.00510 | — | no | no waveform; proxies; ell not measured |
| `mc_2040` | 2 | 4 | 4 | yes | +0.00432 | — | no | no waveform; proxies; ell not measured |
| `mc_2041` | 1 | 3 | 3 | yes | -0.00625 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2041` | 2 | 3 | 3 | yes | -0.00099 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2042` | 1 | 5 | 5 | yes | -0.02285 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2042` | 2 | 5 | 5 | yes | +0.00286 | — | no | no waveform; proxies; ell not measured |
| `mc_2043` | 1 | 4 | 4 | yes | -0.00658 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2043` | 2 | 3 | 3 | yes | +0.00868 | — | no | no waveform; proxies; ell not measured |
| `mc_2044` | 1 | 4 | 4 | yes | -0.00843 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2044` | 2 | 2 | 2 | yes | +0.01896 | — | no | no waveform; proxies; ell not measured |
| `mc_2045` | 1 | 4 | 4 | yes | -0.01547 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2045` | 2 | 4 | 4 | yes | +0.00026 | — | no | no waveform; proxies; ell not measured |
| `mc_2046` | 1 | 3 | 3 | yes | -0.01124 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2046` | 2 | 5 | 5 | yes | -0.00247 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2047` | 1 | 3 | 3 | yes | -0.00279 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2047` | 2 | 3 | 3 | yes | +0.00552 | — | no | no waveform; proxies; ell not measured |
| `mc_2048` | 1 | 4 | 4 | yes | -0.00420 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2048` | 2 | 4 | 4 | yes | +0.00936 | — | no | no waveform; proxies; ell not measured |
| `mc_2049` | 1 | 4 | 4 | yes | -0.00293 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2049` | 2 | 3 | 3 | yes | +0.00755 | — | no | no waveform; proxies; ell not measured |
| `mc_2050` | 1 | 3 | 3 | yes | +0.00566 | — | no | no waveform; proxies; ell not measured |
| `mc_2050` | 2 | 4 | 4 | yes | -0.01223 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2051` | 1 | 5 | 5 | yes | +0.00403 | — | no | no waveform; proxies; ell not measured |
| `mc_2051` | 2 | 5 | 5 | yes | -0.00741 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2052` | 1 | 6 | 6 | yes | -0.01200 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2052` | 2 | 4 | 4 | yes | -0.00058 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2053` | 1 | 4 | 4 | yes | +0.00024 | — | no | no waveform; proxies; ell not measured |
| `mc_2053` | 2 | 3 | 3 | yes | +0.01021 | — | no | no waveform; proxies; ell not measured |
| `mc_2054` | 1 | 3 | 3 | yes | -0.00143 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2054` | 2 | 6 | 6 | yes | -0.02717 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2055` | 1 | 4 | 4 | yes | -0.00597 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2055` | 2 | 4 | 4 | yes | -0.00415 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2056` | 1 | 5 | 5 | yes | -0.00134 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2056` | 2 | 4 | 4 | yes | -0.00434 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2057` | 1 | 3 | 3 | yes | +0.00144 | — | no | no waveform; proxies; ell not measured |
| `mc_2057` | 2 | 4 | 4 | yes | -0.01599 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2058` | 1 | 3 | 3 | yes | -0.00252 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2058` | 2 | 3 | 3 | yes | +0.00376 | — | no | no waveform; proxies; ell not measured |
| `mc_2059` | 1 | 5 | 5 | yes | +0.00160 | — | no | no waveform; proxies; ell not measured |
| `mc_2059` | 2 | 3 | 3 | yes | +0.00212 | — | no | no waveform; proxies; ell not measured |
| `mc_2060` | 1 | 5 | 5 | yes | -0.01371 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2060` | 2 | 3 | 3 | yes | +0.00899 | — | no | no waveform; proxies; ell not measured |
| `mc_2061` | 1 | 4 | 4 | yes | -0.00919 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2061` | 2 | 4 | 4 | yes | +0.00294 | — | no | no waveform; proxies; ell not measured |
| `mc_2062` | 1 | 4 | 4 | yes | +0.00990 | — | no | no waveform; proxies; ell not measured |
| `mc_2062` | 2 | 3 | 4 | no | -0.00388 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2063` | 1 | 4 | 5 | no | -0.02729 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2063` | 2 | 4 | 4 | yes | -0.00313 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2064` | 1 | 3 | 4 | no | +0.00023 | -0.00010 | no | no waveform; proxies; ell_static: room not positive |
| `mc_2064` | 2 | 5 | 5 | yes | -0.01231 | -0.01265 | no | no waveform; proxies; ell_static: room not positive; historical room not positive |
| `mc_2065` | 1 | 6 | 6 | yes | -0.02206 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2065` | 2 | 4 | 4 | yes | +0.00943 | — | no | no waveform; proxies; ell not measured |
| `mc_2066` | 1 | 4 | 4 | yes | +0.01450 | — | no | no waveform; proxies; ell not measured |
| `mc_2066` | 2 | 5 | 5 | yes | -0.01279 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2067` | 1 | 5 | 5 | yes | -0.00051 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2067` | 2 | 4 | 4 | yes | -0.00473 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2068` | 1 | 5 | 5 | yes | +0.00062 | — | no | no waveform; proxies; ell not measured |
| `mc_2068` | 2 | 5 | 5 | yes | +0.00859 | — | no | no waveform; proxies; ell not measured |
| `mc_2069` | 1 | 4 | 4 | yes | +0.01220 | — | no | no waveform; proxies; ell not measured |
| `mc_2069` | 2 | 5 | 5 | yes | -0.00437 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2070` | 1 | 6 | 6 | yes | -0.02288 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2070` | 2 | 5 | 5 | yes | +0.00380 | — | no | no waveform; proxies; ell not measured |
| `mc_2071` | 1 | 4 | 5 | no | -0.02900 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2071` | 2 | 3 | 3 | yes | +0.01011 | — | no | no waveform; proxies; ell not measured |
| `mc_2072` | 1 | 5 | 5 | yes | +0.00355 | — | no | no waveform; proxies; ell not measured |
| `mc_2072` | 2 | 5 | 5 | yes | -0.02124 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2073` | 1 | 4 | 4 | yes | +0.01079 | — | no | no waveform; proxies; ell not measured |
| `mc_2073` | 2 | 5 | 5 | yes | -0.01618 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2074` | 1 | 4 | 4 | yes | -0.00951 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2074` | 2 | 4 | 4 | yes | +0.01529 | — | no | no waveform; proxies; ell not measured |
| `mc_2075` | 1 | 5 | 5 | yes | +0.00002 | — | no | no waveform; proxies; ell not measured |
| `mc_2075` | 2 | 3 | 2 | no | -0.00063 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2076` | 1 | 2 | 2 | yes | +0.00041 | — | no | no waveform; proxies; ell not measured |
| `mc_2076` | 2 | 2 | 2 | yes | +0.00776 | — | no | no waveform; proxies; ell not measured |
| `mc_2077` | 1 | 4 | 4 | yes | -0.01315 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2077` | 2 | 4 | 4 | yes | +0.00376 | — | no | no waveform; proxies; ell not measured |
| `mc_2078` | 1 | 5 | 5 | yes | -0.04010 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2078` | 2 | 5 | 5 | yes | -0.02324 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2079` | 1 | 3 | 3 | yes | +0.00947 | — | no | no waveform; proxies; ell not measured |
| `mc_2079` | 2 | 4 | 4 | yes | +0.00611 | — | no | no waveform; proxies; ell not measured |
| `mc_2080` | 1 | 5 | 5 | yes | +0.00012 | — | no | no waveform; proxies; ell not measured |
| `mc_2080` | 2 | 4 | 4 | yes | -0.00094 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2081` | 1 | 4 | 4 | yes | -0.00087 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2081` | 2 | 5 | 5 | yes | -0.00867 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2082` | 1 | 3 | 3 | yes | +0.01136 | — | no | no waveform; proxies; ell not measured |
| `mc_2082` | 2 | 4 | 4 | yes | -0.00801 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2083` | 1 | 5 | 5 | yes | -0.01186 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2083` | 2 | 3 | 3 | yes | +0.00321 | — | no | no waveform; proxies; ell not measured |
| `mc_2084` | 1 | 2 | 2 | yes | +0.02045 | — | no | no waveform; proxies; ell not measured |
| `mc_2084` | 2 | 3 | 3 | yes | -0.00201 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2085` | 1 | 4 | 4 | yes | +0.00626 | — | no | no waveform; proxies; ell not measured |
| `mc_2085` | 2 | 2 | 2 | yes | +0.01701 | — | no | no waveform; proxies; ell not measured |
| `mc_2086` | 1 | 4 | 4 | yes | +0.00176 | — | no | no waveform; proxies; ell not measured |
| `mc_2086` | 2 | 4 | 4 | yes | +0.00584 | — | no | no waveform; proxies; ell not measured |
| `mc_2087` | 1 | 5 | 5 | yes | -0.00442 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2087` | 2 | 5 | 5 | yes | -0.01184 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2088` | 1 | 5 | 5 | yes | +0.01038 | — | no | no waveform; proxies; ell not measured |
| `mc_2088` | 2 | 3 | 3 | yes | +0.00734 | — | no | no waveform; proxies; ell not measured |
| `mc_2089` | 1 | 5 | 5 | yes | +0.01213 | — | no | no waveform; proxies; ell not measured |
| `mc_2089` | 2 | 4 | 4 | yes | +0.00581 | — | no | no waveform; proxies; ell not measured |
| `mc_2090` | 1 | 4 | 4 | yes | +0.01096 | — | no | no waveform; proxies; ell not measured |
| `mc_2090` | 2 | 3 | 3 | yes | +0.01328 | — | no | no waveform; proxies; ell not measured |
| `mc_2091` | 1 | 3 | 3 | yes | -0.00231 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2091` | 2 | 3 | 3 | yes | +0.00983 | — | no | no waveform; proxies; ell not measured |
| `mc_2092` | 1 | 4 | 4 | yes | +0.00540 | — | no | no waveform; proxies; ell not measured |
| `mc_2092` | 2 | 6 | 6 | yes | -0.01394 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2093` | 1 | 5 | 5 | yes | -0.00637 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2093` | 2 | 5 | 5 | yes | -0.00842 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2094` | 1 | 4 | 4 | yes | +0.00140 | — | no | no waveform; proxies; ell not measured |
| `mc_2094` | 2 | 4 | 4 | yes | +0.00811 | — | no | no waveform; proxies; ell not measured |
| `mc_2095` | 1 | 4 | 5 | no | -0.04576 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2095` | 2 | 5 | 5 | yes | -0.01309 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2096` | 1 | 5 | 5 | yes | -0.01315 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2096` | 2 | 5 | 5 | yes | -0.00402 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2097` | 1 | 5 | 5 | yes | -0.00390 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2097` | 2 | 4 | 4 | yes | +0.00492 | — | no | no waveform; proxies; ell not measured |
| `mc_2098` | 1 | 5 | 4 | no | -0.02873 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2098` | 2 | 4 | 4 | yes | -0.00264 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2099` | 1 | 3 | 3 | yes | +0.01427 | — | no | no waveform; proxies; ell not measured |
| `mc_2099` | 2 | 4 | 5 | no | -0.02266 | — | no | no waveform; proxies; ell not measured; historical room not positive |
| `mc_2100` | 1 | 5 | 5 | yes | +0.00202 | — | no | no waveform; proxies; ell not measured |
| `mc_2100` | 2 | 3 | 3 | yes | +0.00554 | — | no | no waveform; proxies; ell not measured |

## After this result: a new rule

The result above, no port in the certified domain, is not changed by what follows. [`bridge_check/CUMULATIVE_PROTOCOL.md`](bridge_check/CUMULATIVE_PROTOCOL.md) was declared after it and pushed before its numbers were computed. The numbers are in [`bridge_check/CUMULATIVE_RESULTS.md`](bridge_check/CUMULATIVE_RESULTS.md).

- **Which term fails.** With `b` = 0.00499 per write, measured on the nominal replays, `m*b` is the largest term on 180 ports and `a` on 20. The room is positive on 19 ports under these estimates. The port with the largest room is `mc_2084`, port 1: +0.01048. For the median port `b` would have to be divided by 2.0.
- **Cumulative budget.** With the cumulated gain read on the stored voltage of each original run, 69 ports are inside under estimates, 128 outside, 3 not evaluable. The observed count disagrees with `m` on 0 of the ports inside. The median `B` is 0.01376, of which 0.01050 is calibration: the calibration error is proportional to the cumulated step, so reading the cumulated gain does not reduce it.
- **Neither is a certificate.** `a` and `d0` are peak-based proxies, `ell` is measured for one cell, the calibration is that of nominal devices, and the scalar read equation is not established.
