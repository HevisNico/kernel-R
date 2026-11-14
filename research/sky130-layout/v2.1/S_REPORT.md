# Layout 2.1: the nominal stage, S1 to S5

Written by `phase1/s_stage.py report` under [`PREDICTION.md`](PREDICTION.md) and [`S_STAGE.md`](S_STAGE.md). **Simulations** of the nominal cell with the source and drain areas and the extracted capacitances of layout 2.1, capacitance only, primary list; typical corner; no noise, no mismatch. No chip is built.

**5 hold, 0 fail, 0 not evaluable, of 5.**

X1 and X3 of the extraction failed ([`X_REPORT.md`](X_REPORT.md)); they are not amended, and the stage on the 8 cells stays blocked.

| | Prediction | Layout 2.1 | Second layout, read the same way | Verdict |
|---|---|---|---|---|
| S1 | The rest charge before every pulse of the nominal train is between 0.1 and 0.1001 | 21 pulses, from 0.100000 to 0.100039 | 21 pulses, from 0.100000 to 0.100039 (holds) | holds |
| S2 | No step of a port at rest or of a firing pulse above 0.005 mV; first silent step within 0.003 mV of the later ones | largest step of a port at rest 0.001 mV, of a firing pulse 0.001 mV; first silent step against the later ones: 0.000 mV and 0.000 mV | largest step of a port at rest 0.001 mV, of a firing pulse 0.001 mV; first silent step against the later ones: 0.000 mV and 0.000 mV (holds) | holds |
| S3 | The gap of the nominal cell moves by −0.002 to +0.010, the two ports within 0.0005 of each other | +0.00910 (port 1) and +0.00909 (port 2); between the ports 0.00000 | +0.00758 (port 1) and +0.00756 (port 2); between the ports 0.00002 (holds) | holds |
| S4 | L1, L2, L3, L5, L6, L7 and L13 hold on the nominal runs | L1 holds; L2 holds; L3 holds; L5 holds; L6 holds; L7 holds; L13 holds | L1 holds; L2 holds; L3 fails; L5 holds; L6 holds; L7 holds; L13 holds (fails) | holds |
| S5 | Every silent step of the nominal cell is between 1.350 and 1.385 mV | 8 silent steps from 1.361 to 1.361 mV | 8 silent steps from 1.309 to 1.309 mV (fails) | holds |

S5 is not the S5 of the second layout. **By the range of the second layout, 1.340 to 1.365 mV, the silent step of layout 2.1 holds** (1.361 to 1.361 mV).

## S4, prediction by prediction

| | Layout 2.1 | Verdict | Second layout |
|---|---|---|---|
| L1 | first FIRE after 4 and 4 silent pulses; no silent pulse after it | holds | first FIRE after 4 and 4 silent pulses; no silent pulse after it (holds) |
| L2 | 4 and 4 | holds | 4 and 4 (holds) |
| L3 | 1.361 to 1.361 mV | holds | 1.309 to 1.309 mV (fails) |
| L5 | nothing | holds | nothing (holds) |
| L6 | silent after the stop at pulses [5, 29, 52, 75, 98]; intervals [24, 23, 23, 23] | holds | silent after the stop at pulses [25, 47, 70, 92]; intervals [22, 23, 22] (holds) |
| L7 | static level moves by +0.00002 | holds | static level moves by -0.00003 (holds) |
| L13 | silent after the stop at pulses [9, 16, 23, 30, 37, 44, 51, 58]; intervals [7, 7, 7, 7, 7, 7, 7] | holds | silent after the stop at pulses [14, 20, 27, 34, 41, 48, 55]; intervals [6, 7, 7, 7, 7, 7] (holds) |

## Other readings

- At 125 °C: 8 and 10 silent pulses before the first FIRE; the joint pulse fires.
- Rest charge of the nominal train: 0.100034 after a period of port 1, 0.100034 after a period of port 2.
- Supply current of the nominal cell, reported and not predicted: 206.43 µA at rest, 226.01 µA in a period with a silent pulse.

## Runs

| Run | Result | Wall time |
|---|---|---|
| `nom_cell` | result | 129 s |
| `nom_ramp` | result | 14 s |
| `nom_read` | result | 21 s |
| `nom_leak` | result | 251 s |
| `nom_refresh` | result | 608 s |
| `nom_cell125` | result | 113 s |
| `nom_refresh125` | result | 341 s |
| `nom_train` | result | 126 s |
