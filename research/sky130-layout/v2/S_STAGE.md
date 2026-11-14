# Second layout: declaration of the nominal stage

Declared on 2026-11-13, **before any simulation of the second layout.**
[`PREDICTION.md`](PREDICTION.md) is not edited.

The owner read [`X_REPORT.md`](X_REPORT.md): X1 fails (0.049 fF between
`vq` and `vrefmn`, limit 0.03 fF), X2 to X5 hold. **X1 is not amended.
The stage on the 8 cells stays blocked.** The owner gave the go for the
nominal stage S1 to S5 only.

## Runs

Nominal cell, typical corner, no noise, no mismatch. The netlist is
built as in stage P ([`../AMENDMENT_4.md`](../AMENDMENT_4.md)): the
runners of the campaigns unchanged, through the harness
`../phase1/p_run.py`, with the primary list of capacitances of the
second layout.

| Input | File | sha256 |
|---|---|---|
| Capacitances, primary list | `phase1/p_caps_primary.csv` | `c678ae9641adccf1920cfa2d57910c49f47070381d804965b648e045819d4edc` |
| Source and drain areas | `phase1/p_areas.csv` | `19bd1f27e174c22c7b8b2eea9afb8d81fe4a744993539763ab46b819dd88542a`, the same file as for the first layout |

**Eight runs, one more than [`PREDICTION.md`](PREDICTION.md) says.** The
seven nominal runs of stage P: `nom_cell`, `nom_ramp`, `nom_read`,
`nom_leak`, `nom_refresh` (100 pulses, 0.1 TΩ), `nom_cell125`,
`nom_refresh125`. And `nom_train`, the nominal train of `cert_run.py`:
S1 is worded on "the nominal train" and on the rest charge, which
`run.py` does not write. It is the run on which the diagnostic read
0.100983 for the first layout.

One machine, this one, four runs at a time, by the launcher of stage P
(`../phase1/execute.py`): the attempt marker `phase1/RUN_ATTEMPT_S.json`
pushed before the first run, the name of each run pushed as started
before it begins, a run that started never made again. No secondary
list: the stage is declared on the primary list only.

## How S1 to S5 are read

`phase1/s_stage.py`, committed with this file.

| | Read on | Rule |
|---|---|---|
| S1 | `nom_train` | The column `c_pre` of every one of its 21 pulses is between 0.1 and 0.1001 |
| S2 | `nom_cell` | Every step of a port in a period where it is not pulsed, and every step of a pulsed port on a firing pulse, the joint pulse included, is at most 0.005 mV in size. For each port, its first silent step is within 0.003 mV of each of its later silent steps |
| S3 | `nom_ramp`, `nom_read` | The gap of each port by the formula of `cert_analyze.py predict`, **with the constants calibrated on the first layout in stage P** (`phase1/constants_stage_p.json`: `d0`, `kappa`, `mu`), against the schematic gap of stage P. Both shifts in the range, and within 0.0005 of each other |
| S4 | the eight runs | L1, L2, L3 on `nom_cell`; L5 on every row of the eight runs; L6 on `nom_refresh`; L7 on `nom_ramp`; L13 on `nom_refresh125`. Each read as in stage P. S4 holds if the seven hold |
| S5 | `nom_cell` | Every step of a silent pulse of the pulsed port is between 1.340 and 1.365 mV |

A prediction whose run has no result is not evaluable.

No calibration is made on the second layout: no cell with mismatch is
run. The shift of S3 therefore carries the constants of the first
layout, as [`PREDICTION.md`](PREDICTION.md) said it would.

The analysis was tried on the results of the first layout before this
stage (no simulation): it gives again 0.100983 for the rest charge,
0.014 mV for the step, +0.0140 and +0.0125 for the shift.

The report is written once, after the last run, and pushed as it comes.
Then the work stops.
