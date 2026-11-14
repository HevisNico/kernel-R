# Layout 2.2: the stage on the 8 cells, C1 to C3

Written by `phase1/c_stage.py report` under [`PREDICTION.md`](PREDICTION.md) and [`C_STAGE.md`](C_STAGE.md). **Simulations** of the cell of `cell.spice` with the source and drain areas and the extracted capacitances of layout 2.2, capacitance only, primary list; typical corner; 8 cells with mismatch, each with one noisy test run; 8 calibration cells. No chip is built.

**Confirmatory**: X1 to X7 and S1 to S5 hold on layout 2.2 ([`X_REPORT.md`](X_REPORT.md), [`S_REPORT.md`](S_REPORT.md)), and the declaration was pushed before the first run.

**1 hold, 1 fail, 0 not evaluable, 1 without a prediction, of 3.**

| | Prediction | Layout 2.2 | First layout, read the same way | Verdict |
|---|---|---|---|---|
| C1 | No port is refused for its rest state | 3 of 16 ports refused for their rest state: t6051 port 1, t6082 port 1, t6031 port 1 | 16 of 16 ports refused for their rest state: t6065 port 1, t6065 port 2, t6002 port 1, t6002 port 2, t6074 port 1, t6074 port 2, t6051 port 1, t6051 port 2, t6082 port 1, t6082 port 2, t6003 port 1, t6003 port 2, t6031 port 1, t6031 port 2, t6030 port 1, t6030 port 2 (fails) | fails |
| C2 | No certified port has a count different from its need, and at least 2 of the 16 ports are certified, at status 3 or by rule A1 | 7 certified ports of 16 (4 at status 3, 7 by rule A1); contradicted: none | 0 certified ports of 16 (0 at status 3, 0 by rule A1); contradicted: none (fails) | holds |
| C3 | No prediction on the four ports of L12 unless S3 gives a shift below 0.004 on both ports; if it does, at least 2 of the 4 are certified again at status 3 | S3 gave +0.00909 and +0.00909; 1 of 4 evaluable ports of L12 certified again at status 3: t6074 port 1 | 0 of 4 evaluable ports of L12 certified again at status 3 (a reading, not a verdict) | no prediction |

## What the verdicts rest on

- Constants: calibrated on 8 cells and 3 leak scans. `d0` = 0.042422, `kappa` = 0.075736, `mu` = +0.001042, `h_mu` = 0.001277; in the campaign on the schematic 0.042093, 0.074607, +0.000394, 0.001512.
- Evaluable cells: 8 of 8 (t6065, t6002, t6074, t6051, t6082, t6003, t6031, t6030); evaluable ports: 16.
- C2 can fail on one port and cannot establish a rate: with no contradiction among n certified ports the 95% upper bound on the rate is 1 − 0.05^(1/n) (53% for 4, 31% for 8, 17% for 16).
- One layout, one extraction by Magic's rules, capacitance only; 8 cells drawn by the mismatch models of the PDK, one noise draw each. Nothing about silicon.
- The seven nominal runs were made again in this stage: 7 of 7 give the rows of the nominal stage, byte for byte.

## Ports

Schematic: the committed values of the same cell and port. Layout 2.2: this stage, constants of this stage.

| Cell | Port | Static level, move | Gap, schematic | Gap, layout 2.2 | Need, schematic | Need, layout 2.2 | Count | Status 3, schematic | Status 3, layout 2.2 | Room at status 3 | Rule A1 | Rooms of rule A1, silence and FIRE |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `t6065` | 1 | +0.00001 | +0.14726 | +0.15653 | 4 | 4 | 4 | certified, count confirmed | outside the certified domain | -0.00210 | eligible | +0.00119 and +0.00351 |
| `t6065` | 2 | +0.00001 | +0.09147 | +0.10082 | 3 | 3 | 3 | outside the certified domain | certified, count confirmed | +0.00251 | eligible | +0.00839 and +0.00469 |
| `t6002` | 1 | -0.00001 | +0.06292 | +0.07239 | 2 | 2 | 2 | certified, count confirmed | outside the certified domain | -0.00608 | not eligible: silence room; FIRE room | -0.00417 and -0.00102 |
| `t6002` | 2 | -0.00001 | +0.16788 | +0.17708 | 4 | 5 | 5 | outside the certified domain | outside the certified domain | -0.00688 | not eligible: silence room; FIRE room | -0.00146 and -0.00676 |
| `t6074` | 1 | +0.00000 | +0.10416 | +0.11353 | 3 | 3 | 3 | certified, count confirmed | certified, count confirmed | +0.00210 | eligible | +0.00634 and +0.00328 |
| `t6074` | 2 | +0.00000 | +0.08394 | +0.09304 | 2 | 3 | 3 | outside the certified domain | outside the certified domain | -0.00332 | not eligible: silence room | -0.00141 and +0.00197 |
| `t6051` | 1 | +0.00000 | +0.15806 | +0.16736 | 4 | 4 | 4 | outside the certified domain | outside the certified domain | -0.01672 | not eligible: rest charge; silence room; FIRE room | -0.01456 and -0.01556 |
| `t6051` | 2 | +0.00000 | +0.10481 | +0.11399 | 3 | 3 | 3 | certified, count confirmed | outside the certified domain | -0.00019 | eligible | +0.00256 and +0.00354 |
| `t6082` | 1 | +0.00000 | +0.17433 | +0.18338 | 5 | 5 | 5 | outside the certified domain | outside the certified domain | -0.00761 | not eligible: rest charge; silence room; FIRE room | -0.00571 and -0.00354 |
| `t6082` | 2 | +0.00000 | +0.14255 | +0.15160 | 4 | 4 | 4 | certified, count confirmed | certified, count confirmed | +0.00253 | eligible | +0.00462 and +0.00570 |
| `t6003` | 1 | -0.00000 | +0.18706 | +0.19617 | 5 | 5 | 5 | certified, count confirmed | certified, count confirmed | +0.00272 | eligible | +0.00686 and +0.00623 |
| `t6003` | 2 | -0.00000 | +0.17008 | +0.17919 | 5 | 5 | 5 | outside the certified domain | outside the certified domain | -0.00872 | not eligible: silence room | -0.00404 and +0.00058 |
| `t6031` | 1 | +0.00000 | +0.14382 | +0.15315 | 4 | 4 | 4 | certified, count confirmed | outside the certified domain | +0.00123 | not eligible: rest charge | +0.00680 and +0.00135 |
| `t6031` | 2 | +0.00000 | +0.19958 | +0.20886 | 5 | 5 | 5 | outside the certified domain | outside the certified domain | -0.01258 | not eligible: silence room; FIRE room | -0.01067 and -0.00757 |
| `t6030` | 1 | -0.00000 | +0.10694 | +0.11620 | 3 | 3 | 3 | certified, count confirmed | outside the certified domain | -0.00059 | eligible | +0.00270 and +0.00355 |
| `t6030` | 2 | -0.00000 | +0.16774 | +0.17706 | 4 | 5 | 5 | outside the certified domain | outside the certified domain | -0.01079 | not eligible: silence room; FIRE room | -0.00499 and -0.01067 |

## The predictions of stage P, read on layout 2.2

**Not predictions of this stage, and no verdict of it.** L1 to L13 were made for the first layout ([`../PREDICTION.md`](../PREDICTION.md)); they are read here by the script of stage P, unchanged, so that the two layouts can be compared.

| | Prediction of stage P | Layout 2.2 | Would be | First layout | Was |
|---|---|---|---|---|---|
| L1 | The nominal cell stops by itself: silent pulses, then a FIRE on every later pulse of each series | first FIRE after 4 and 4 silent pulses; no silent pulse after it | holds | first FIRE after 4 and 4 silent pulses; no silent pulse after it | holds |
| L2 | The nominal count of silent pulses is 3, 4 or 5, the same on both ports | 4 and 4 | holds | 4 and 4 | holds |
| L3 | A silent pulse of the nominal cell writes between 1.33 and 1.42 mV | 8 silent steps from 1.361 to 1.361 mV | holds | 8 silent steps from 1.343 to 1.358 mV | holds |
| L4 | A firing pulse of the nominal cell moves the stored voltage by at most 0.005 mV | 14 steps of firing pulses, largest 0.001 mV | holds | 14 steps of firing pulses, largest 0.014 mV | fails |
| L5 | The guard reports nothing on any run | nothing | holds | nothing | holds |
| L6 | Under 0.1 TΩ the nominal cell falls silent once every 20 to 25 periods | silent after the stop at pulses [5, 29, 52, 75, 98]; intervals [24, 23, 23, 23] | holds | silent after the stop at pulses [26, 49, 72, 95]; intervals [23, 23, 23] | holds |
| L7 | The static FIRE level of the nominal cell and of each cell moves by less than 0.002 level unit | 9 cells; largest move -0.00001 (t6002) | holds | 9 cells; largest move -0.00001 (t6002) | holds |
| L8 | The gap of the nominal cell moves by −0.005 to +0.030; each port follows within ±0.004 | nominal shift +0.00923 (port 1) and +0.00923 (port 2); 16 ports, largest distance to the nominal shift +0.00025 (t6002 port 1) | holds | nominal shift +0.01401 (port 1) and +0.01252 (port 2); 16 ports, largest distance to the nominal shift +0.00054 (t6002 port 1) | holds |
| L9 | The need of each port changes by 0 or +1 | 16 ports: 13 unchanged, 3 at +1 | holds | 16 ports: 11 unchanged, 5 at +1 | holds |
| L10 | The observed count equals the post-layout need on at least 13 of 16 ports | 16 of 16 | holds | 14 of 16 | holds |
| L11 | No port certified post-layout, at status 3 or by rule A1, has a count different from its need | 7 certified ports of 16 (4 at status 3, 7 by rule A1); contradicted: none | holds | 0 certified ports of 16 (0 at status 3, 0 by rule A1); contradicted: none | holds |
| L12 | Of the 4 evaluable status-3 ports with the largest room, at least 3 are certified again at status 3 | 1 of 4: t6074 port 1 | fails | 0 of 4: none | fails |
| L13 | At 125 °C the nominal cell stops, then falls silent again once every 4 to 15 periods | silent after the stop at pulses [9, 16, 23, 30, 37, 44, 51, 58]; intervals [7, 7, 7, 7, 7, 7, 7] | holds | silent after the stop at pulses [15, 22, 29, 36, 43, 50, 57]; intervals [7, 7, 7, 7, 7, 7] | holds |

## Readings outside any verdict

- **At 125 °C the two ports of the nominal cell fire after 8 and 10 silent pulses, not after the same number.** No prediction covers it: a reading outside any verdict. The joint pulse fires. In the nominal stage of layout 2.2: 8 and 10.
- At 27 °C: 4 and 4 silent pulses before the first FIRE; silent steps 1.361 to 1.361 mV.
- Shift of the gap of the nominal cell: +0.00909 and +0.00909 with the constants of stage P (S3); +0.00923 and +0.00923 with the constants of this stage.
- Supply current of the nominal cell, reported and not predicted: 206.43 µA at rest, 226.01 µA in a period with a silent pulse.

## Runs

In the order of the queue, four at a time.

| Group | Run | Result | Wall time |
|---|---|---|---|
| 1 | `nom_cell` | result | 140 s |
| 1 | `nom_ramp` | result | 16 s |
| 1 | `nom_read` | result | 24 s |
| 1 | `nom_leak` | result | 253 s |
| 2 | `nom_refresh` | result | 618 s |
| 2 | `nom_cell125` | result | 110 s |
| 2 | `nom_refresh125` | result | 357 s |
| 2 | `c5001_train` | result | 129 s |
| 3 | `c5001_ramp` | result | 16 s |
| 3 | `c5001_leak` | result | 257 s |
| 3 | `t6065_ramp` | result | 15 s |
| 3 | `t6065_read` | result | 25 s |
| 4 | `u6065_leak` | result | 239 s |
| 4 | `u6065_train` | result | 125 s |
| 4 | `t6065_train` | result | 216 s |
| 4 | `c5002_train` | result | 127 s |
| 5 | `c5002_ramp` | result | 16 s |
| 5 | `c5002_leak` | result | 231 s |
| 5 | `t6030_ramp` | result | 14 s |
| 5 | `t6030_read` | result | 21 s |
| 6 | `u6030_leak` | result | 235 s |
| 6 | `u6030_train` | result | 131 s |
| 6 | `t6030_train` | result | 183 s |
| 6 | `c5003_train` | result | 121 s |
| 7 | `c5003_ramp` | result | 16 s |
| 7 | `t6031_ramp` | result | 16 s |
| 7 | `t6031_read` | result | 19 s |
| 7 | `u6031_leak` | result | 230 s |
| 8 | `u6031_train` | result | 122 s |
| 8 | `t6031_train` | result | 198 s |
| 8 | `c5004_train` | result | 121 s |
| 8 | `c5004_ramp` | result | 14 s |
| 9 | `t6002_ramp` | result | 14 s |
| 9 | `t6002_read` | result | 24 s |
| 9 | `u6002_leak` | result | 248 s |
| 9 | `u6002_train` | result | 132 s |
| 10 | `t6002_train` | result | 200 s |
| 10 | `c5005_train` | result | 130 s |
| 10 | `c5005_ramp` | result | 15 s |
| 10 | `t6074_ramp` | result | 17 s |
| 11 | `t6074_read` | result | 20 s |
| 11 | `u6074_leak` | result | 242 s |
| 11 | `u6074_train` | result | 128 s |
| 11 | `t6074_train` | result | 210 s |
| 12 | `c5006_train` | result | 131 s |
| 12 | `c5006_ramp` | result | 16 s |
| 12 | `t6003_ramp` | result | 15 s |
| 12 | `t6003_read` | result | 24 s |
| 13 | `u6003_leak` | result | 243 s |
| 13 | `u6003_train` | result | 127 s |
| 13 | `t6003_train` | result | 207 s |
| 13 | `c5007_train` | result | 130 s |
| 14 | `c5007_ramp` | result | 16 s |
| 14 | `t6082_ramp` | result | 16 s |
| 14 | `t6082_read` | result | 22 s |
| 14 | `u6082_leak` | result | 253 s |
| 15 | `u6082_train` | result | 131 s |
| 15 | `t6082_train` | result | 204 s |
| 15 | `c5008_train` | result | 124 s |
| 15 | `c5008_ramp` | result | 16 s |
| 16 | `t6051_ramp` | result | 17 s |
| 16 | `t6051_read` | result | 21 s |
| 16 | `u6051_leak` | result | 245 s |
| 16 | `u6051_train` | result | 129 s |
| 17 | `t6051_train` | result | 196 s |
