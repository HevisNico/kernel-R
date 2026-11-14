# Layout 2.2: declaration of the nominal stage

Declared on 2026-11-14, **before any simulation of layout 2.2.**
[`PREDICTION.md`](PREDICTION.md) is not edited.

The owner read [`X_REPORT.md`](X_REPORT.md): X1 to X7 hold, on the one
extraction, with the prediction, the generator and the report pushed in
that order. The owner gave the go for the nominal stage S1 to S5,
exactly as preregistered. **The stage on the 8 cells needs a separate
go.**

## Runs

Those of layout 2.1 ([`../v2.1/S_STAGE.md`](../v2.1/S_STAGE.md)), made
the same way: nominal cell, typical corner, no noise, no mismatch; the
runners of the campaigns unchanged, through the harness
`../phase1/p_run.py`, with the primary list of capacitances of
layout 2.2.

| Input | File | sha256 |
|---|---|---|
| Capacitances, primary list | `phase1/p_caps_primary.csv` | `e7f753d59c5a5e1203472627fcf538e18b4a380b1062f916ba6d3a7216e286e6`, the file of the extraction (`layout/SHA256SUMS_X`) |
| Source and drain areas | `phase1/p_areas.csv` | `19bd1f27e174c22c7b8b2eea9afb8d81fe4a744993539763ab46b819dd88542a`, the same file as for the earlier layouts |
| Constants of stage P | `phase1/constants_stage_p.json` | `6a453a3227503d9b6767424ded43c0c466c34bae65b980cd976365bc766c1306`, the same file as for the second layout and layout 2.1 |

**Eight runs**: `nom_cell`, `nom_ramp`, `nom_read`, `nom_leak`,
`nom_refresh` (100 pulses, 0.1 TΩ), `nom_cell125`, `nom_refresh125`,
`nom_train`.

One machine, this one, four runs at a time, by the launcher of stage P
(`../phase1/execute.py`): the attempt marker `phase1/RUN_ATTEMPT_S.json`
pushed before the first run, the name of each run pushed as started
before it begins, a run that started never made again. Primary list
only.

## How S1 to S5 are read

`phase1/s_stage.py`, committed with this file: a copy of the script of
layout 2.1 with two changes, said in its first lines. **The rules and
the ranges are those of layout 2.1.**

| | Read on | Rule |
|---|---|---|
| S1 | `nom_train` | `c_pre` of every one of its 21 pulses between 0.1 and 0.1001 |
| S2 | `nom_cell` | No step of a port at rest or of a firing pulse above 0.005 mV; for each port, its first silent step within 0.003 mV of each later one |
| S3 | `nom_ramp`, `nom_read` | The gap by the formula of `cert_analyze.py predict` with the constants of stage P, against the schematic gap; both shifts between −0.002 and +0.010, within 0.0005 of each other |
| S4 | the eight runs | L1, L2, L3, L5, L6, L7 and L13 |
| S5 | `nom_cell` | Every step of a silent pulse of the pulsed port between 1.350 and 1.385 mV. The report also says whether it is in the range of the second layout, 1.340 to 1.365 mV |

A prediction whose run has no result is not evaluable. The column of
comparison of the report is layout 2.1, read by the same script on its
committed results (`../v2.1/phase1/results_s/`).

The analysis was tried on those results before this stage (no
simulation): it gives again what the report of layout 2.1 says,
0.100000 to 0.100039 for the rest charge, +0.00910 and +0.00909 for the
shift, 1.361 mV for the silent step.

The report is written once, after the last run, and pushed as it comes.
Then the work stops.
