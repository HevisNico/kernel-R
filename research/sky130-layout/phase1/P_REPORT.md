# Stage P: report

Written by `p_analyze.py report` under [`../PREDICTION.md`](../PREDICTION.md) and its four amendments. **Simulations** of the cell of `cell.spice` with the source and drain areas of the layout and its extracted capacitances, capacitance only; typical corner; the primary list of capacitances ([`../AMENDMENT_3.md`](../AMENDMENT_3.md)). No chip is built.

**11 hold, 2 fail, 0 not evaluable, of 13.**

- Against the layout bet (L1, L5 or L11 failing): none.
- A shift and not a failure (L2, L3, L8, L9 or L12 outside its range): L12.

| | Prediction | Measured | Verdict |
|---|---|---|---|
| L1 | The nominal cell stops by itself: silent pulses, then a FIRE on every later pulse of each series | first FIRE after 4 and 4 silent pulses; no silent pulse after it | holds |
| L2 | The nominal count of silent pulses is 3, 4 or 5, the same on both ports | 4 and 4 | holds |
| L3 | A silent pulse of the nominal cell writes between 1.33 and 1.42 mV | 8 silent steps from 1.343 to 1.358 mV | holds |
| L4 | A firing pulse of the nominal cell moves the stored voltage by at most 0.005 mV | 14 steps of firing pulses, largest 0.014 mV | fails |
| L5 | The guard reports nothing on any run | nothing | holds |
| L6 | Under 0.1 TΩ the nominal cell falls silent once every 20 to 25 periods | silent after the stop at pulses [26, 49, 72, 95]; intervals [23, 23, 23] | holds |
| L7 | The static FIRE level of the nominal cell and of each cell moves by less than 0.002 level unit | 9 cells; largest move -0.00001 (t6002) | holds |
| L8 | The gap of the nominal cell moves by −0.005 to +0.030; each port follows within ±0.004 | nominal shift +0.01401 (port 1) and +0.01252 (port 2); 16 ports, largest distance to the nominal shift +0.00054 (t6002 port 1) | holds |
| L9 | The need of each port changes by 0 or +1 | 16 ports: 11 unchanged, 5 at +1 | holds |
| L10 | The observed count equals the post-layout need on at least 13 of 16 ports | 14 of 16 | holds |
| L11 | No port certified post-layout, at status 3 or by rule A1, has a count different from its need | 0 certified ports of 16 (0 at status 3, 0 by rule A1); contradicted: none | holds |
| L12 | Of the 4 evaluable status-3 ports with the largest room, at least 3 are certified again at status 3 | 0 of 4: none | fails |
| L13 | At 125 °C the nominal cell stops, then falls silent again once every 4 to 15 periods | silent after the stop at pulses [15, 22, 29, 36, 43, 50, 57]; intervals [7, 7, 7, 7, 7, 7] | holds |

**The earlier 125 °C result, a stop with no relapse after it, was an artifact of netlists without junction areas.** This rests on a nominal simulation, with the source and drain areas of the layout.

## What the verdicts rest on

- Constants: calibrated on 8 cells and 3 leak scans. `d0` = 0.042280, `kappa` = 0.076036, `mu` = +0.000917, `h_mu` = 0.001369; in the campaign 0.042093, 0.074607, +0.000394, 0.001512.
- Evaluable cells: 8 of 8 (t6065, t6002, t6074, t6051, t6082, t6003, t6031, t6030); evaluable ports: 16.
- L11 can fail on one port and cannot establish a rate: with no contradiction among n certified ports the 95% upper bound on the rate is 1 − 0.05^(1/n) (53% for 4, 31% for 8, 17% for 16).

## Ports

Schematic: the committed values of the same cell and port. Post-layout: this stage, constants of this stage.

| Cell | Port | Static level, move | Gap, schematic | Gap, post-layout | Need, schematic | Need, post-layout | Count | Status 3, schematic | Status 3, post-layout | Room at status 3 | Rule A1 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `t6065` | 1 | +0.00000 | +0.14726 | +0.16137 | 4 | 4 | 4 | certified, count confirmed | outside the certified domain | -0.00647 | not eligible: rest charge; silence room; FIRE room |
| `t6065` | 2 | +0.00000 | +0.09147 | +0.10420 | 3 | 3 | 3 | outside the certified domain | outside the certified domain | +0.00728 | not eligible: rest charge |
| `t6002` | 1 | -0.00001 | +0.06292 | +0.07747 | 2 | 2 | 2 | certified, count confirmed | outside the certified domain | -0.01051 | not eligible: rest charge; silence room; FIRE room |
| `t6002` | 2 | -0.00001 | +0.16788 | +0.18034 | 4 | 5 | 5 | outside the certified domain | outside the certified domain | -0.00306 | not eligible: rest charge; FIRE room |
| `t6074` | 1 | -0.00000 | +0.10416 | +0.11847 | 3 | 3 | 3 | certified, count confirmed | outside the certified domain | -0.00344 | not eligible: rest charge; FIRE room |
| `t6074` | 2 | -0.00000 | +0.08394 | +0.09619 | 2 | 3 | 3 | outside the certified domain | outside the certified domain | +0.00033 | not eligible: rest charge |
| `t6051` | 1 | -0.00000 | +0.15806 | +0.17224 | 4 | 5 | 4 | outside the certified domain | outside the certified domain | -0.01593 | not eligible: rest charge; silence room; FIRE room |
| `t6051` | 2 | -0.00000 | +0.10481 | +0.11724 | 3 | 3 | 3 | certified, count confirmed | outside the certified domain | -0.00353 | not eligible: rest charge; silence room |
| `t6082` | 1 | -0.00000 | +0.17433 | +0.18796 | 5 | 5 | 5 | outside the certified domain | outside the certified domain | -0.00290 | not eligible: rest charge; silence room |
| `t6082` | 2 | -0.00000 | +0.14255 | +0.15473 | 4 | 4 | 4 | certified, count confirmed | outside the certified domain | -0.00099 | not eligible: rest charge |
| `t6003` | 1 | -0.00000 | +0.18706 | +0.20085 | 5 | 5 | 5 | certified, count confirmed | outside the certified domain | -0.00152 | not eligible: rest charge |
| `t6003` | 2 | -0.00000 | +0.17008 | +0.18240 | 5 | 5 | 5 | outside the certified domain | outside the certified domain | -0.00275 | not eligible: rest charge |
| `t6031` | 1 | -0.00000 | +0.14382 | +0.15801 | 4 | 4 | 4 | certified, count confirmed | outside the certified domain | -0.00452 | not eligible: rest charge; FIRE room |
| `t6031` | 2 | -0.00000 | +0.19958 | +0.21221 | 5 | 6 | 5 | outside the certified domain | outside the certified domain | -0.01541 | not eligible: rest charge; silence room; FIRE room |
| `t6030` | 1 | -0.00000 | +0.10694 | +0.12104 | 3 | 3 | 3 | certified, count confirmed | outside the certified domain | -0.00443 | not eligible: rest charge; silence room; FIRE room |
| `t6030` | 2 | -0.00000 | +0.16774 | +0.18046 | 4 | 5 | 5 | outside the certified domain | outside the certified domain | -0.00585 | not eligible: rest charge; silence room; FIRE room |

## The same with the constants of the campaign

Declared second analysis (decision D6). It decides no prediction.

| | Measured | Would be |
|---|---|---|
| L8 | nominal shift +0.01343 (port 1) and +0.01194 (port 2); 16 ports, largest distance to the nominal shift +0.00053 (t6002 port 1) | holds |
| L9 | 16 ports: 11 unchanged, 5 at +1 | holds |
| L10 | 14 of 16 | holds |
| L11 | 0 certified ports of 16 (0 at status 3, 0 by rule A1); contradicted: none | holds |
| L12 | 0 of 4: none | fails |

## Nominal cell: primary list and secondary list

The secondary list keeps the plate term: an upper bound ([`../AMENDMENT_3.md`](../AMENDMENT_3.md)). It decides no prediction.

| Reading | Primary | Secondary, upper bound |
|---|---|---|
| Silent pulses before the first FIRE, port 1 and port 2 (27 °C) | 4 and 4 | 5 and 5 |
| Stops with no silent pulse after its first FIRE | yes | yes |
| Silent steps (mV) | 1.343 to 1.358 | 1.342 to 1.357 |
| Largest step of a firing pulse (mV) | 0.014 | 0.014 |
| Static level, move against the schematic | -0.00000 | +0.00001 |
| Under 0.1 TΩ: silent pulses after the stop | [26, 49, 72, 95] | [10, 34, 58, 83] |
| 125 °C: silent pulses before the first FIRE | 9 and 10 | 10 and 10 |
| 125 °C, no imposed leak: silent pulses after the stop | [15, 22, 29, 36, 43, 50, 57] | [16, 23, 31, 38, 45, 53] |
| Guard | nothing | nothing |

Gap of the nominal cell, primary list: +0.01401 and +0.01252 against the schematic (ports 1 and 2). With the secondary list no calibration is made, so no gap is given.

## Supply current of the nominal cell

Reported, not predicted. A nominal simulation at 27 °C; the references, bias sinks and clocks are ideal sources outside the cell.

Mean current delivered by the 1.8 V source, power, and energy over one period of 440 µs.

| | Schematic | Post-layout, primary list |
|---|---|---|
| At rest | 206.43 µA, 371.6 µW, 163.50 nJ per period | 206.43 µA, 371.6 µW, 163.50 nJ per period |
| Period with a silent pulse | 226.05 µA, 406.9 µW, 179.03 nJ per period (+15535.9 pJ against rest) | 225.96 µA, 406.7 µW, 178.96 nJ per period (+15466.2 pJ against rest) |
| Period with a firing pulse | 223.02 µA, 401.4 µW, 176.63 nJ per period (+13136.7 pJ against rest) | 222.92 µA, 401.3 µW, 176.55 nJ per period (+13055.4 pJ against rest) |

## Runs

| Run | Analysis | Result | Wall time |
|---|---|---|---|
| `nom_cell` (machine A) | primary | result | 159 s |
| `nom_ramp` (machine A) | primary | result | 18 s |
| `nom_read` (machine A) | primary | result | 25 s |
| `nom_leak` (machine A) | primary | result | 306 s |
| `c5001_train` (machine A) | primary | result | 162 s |
| `c5001_ramp` (machine A) | primary | result | 19 s |
| `c5001_leak` (machine A) | primary | result | 303 s |
| `t6065_ramp` (machine A) | primary | result | 20 s |
| `t6065_read` (machine A) | primary | result | 27 s |
| `u6065_leak` (machine A) | primary | result | 292 s |
| `u6065_train` (machine A) | primary | result | 156 s |
| `t6065_train` (machine A) | primary | result | 247 s |
| `c5003_train` (machine A) | primary | result | 152 s |
| `c5003_ramp` (machine A) | primary | result | 17 s |
| `t6031_ramp` (machine A) | primary | result | 18 s |
| `t6031_read` (machine A) | primary | result | 26 s |
| `u6031_leak` (machine A) | primary | result | 298 s |
| `u6031_train` (machine A) | primary | result | 154 s |
| `t6031_train` (machine A) | primary | result | 239 s |
| `c5005_train` (machine A) | primary | result | 160 s |
| `c5005_ramp` (machine A) | primary | result | 20 s |
| `t6074_ramp` (machine A) | primary | result | 19 s |
| `t6074_read` (machine A) | primary | result | 27 s |
| `u6074_leak` (machine A) | primary | result | 299 s |
| `u6074_train` (machine A) | primary | result | 163 s |
| `t6074_train` (machine A) | primary | result | 250 s |
| `c5007_train` (machine A) | primary | result | 163 s |
| `c5007_ramp` (machine A) | primary | result | 19 s |
| `t6082_ramp` (machine A) | primary | result | 20 s |
| `t6082_read` (machine A) | primary | result | 29 s |
| `u6082_leak` (machine A) | primary | result | 295 s |
| `u6082_train` (machine A) | primary | result | 157 s |
| `t6082_train` (machine A) | primary | result | 241 s |
| `s_nom_cell` (machine A) | secondary | result | 160 s |
| `s_nom_ramp` (machine A) | secondary | result | 18 s |
| `s_nom_read` (machine A) | secondary | result | 28 s |
| `s_nom_leak` (machine A) | secondary | result | 301 s |
| `nom_refresh` (machine B) | primary | result | 636 s |
| `nom_cell125` (machine B) | primary | result | 117 s |
| `nom_refresh125` (machine B) | primary | result | 369 s |
| `c5002_train` (machine B) | primary | result | 133 s |
| `c5002_ramp` (machine B) | primary | result | 14 s |
| `c5002_leak` (machine B) | primary | result | 235 s |
| `t6030_ramp` (machine B) | primary | result | 16 s |
| `t6030_read` (machine B) | primary | result | 21 s |
| `u6030_leak` (machine B) | primary | result | 247 s |
| `u6030_train` (machine B) | primary | result | 121 s |
| `t6030_train` (machine B) | primary | result | 197 s |
| `c5004_train` (machine B) | primary | result | 133 s |
| `c5004_ramp` (machine B) | primary | result | 15 s |
| `t6002_ramp` (machine B) | primary | result | 14 s |
| `t6002_read` (machine B) | primary | result | 22 s |
| `u6002_leak` (machine B) | primary | result | 251 s |
| `u6002_train` (machine B) | primary | result | 133 s |
| `t6002_train` (machine B) | primary | result | 200 s |
| `c5006_train` (machine B) | primary | result | 127 s |
| `c5006_ramp` (machine B) | primary | result | 15 s |
| `t6003_ramp` (machine B) | primary | result | 14 s |
| `t6003_read` (machine B) | primary | result | 20 s |
| `u6003_leak` (machine B) | primary | result | 241 s |
| `u6003_train` (machine B) | primary | result | 123 s |
| `t6003_train` (machine B) | primary | result | 219 s |
| `c5008_train` (machine B) | primary | result | 119 s |
| `c5008_ramp` (machine B) | primary | result | 16 s |
| `t6051_ramp` (machine B) | primary | result | 14 s |
| `t6051_read` (machine B) | primary | result | 21 s |
| `u6051_leak` (machine B) | primary | result | 230 s |
| `u6051_train` (machine B) | primary | result | 133 s |
| `t6051_train` (machine B) | primary | result | 205 s |
| `s_nom_refresh` (machine B) | secondary | result | 610 s |
| `s_nom_cell125` (machine B) | secondary | result | 109 s |
| `s_nom_refresh125` (machine B) | secondary | result | 340 s |
