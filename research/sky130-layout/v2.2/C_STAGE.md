# Layout 2.2: declaration of the stage on the 8 cells

Declared on 2026-11-14, **before any run of this stage.** No cell with
mismatch has been simulated on layout 2.2.
[`PREDICTION.md`](PREDICTION.md) is not edited.

The owner read [`X_REPORT.md`](X_REPORT.md) and
[`S_REPORT.md`](S_REPORT.md): X1 to X7 and S1 to S5 hold on layout 2.2,
each with its declaration pushed before. **By
[`PREDICTION.md`](PREDICTION.md) the stage on the 8 cells is
confirmatory.** The owner gave the go for it, on one machine, once this
file is pushed and the checks of the repository are green.

## What is predicted

C1 to C3 of [`../v2/PREDICTION.md`](../v2/PREDICTION.md), unchanged.

| | Prediction | First layout |
|---|---|---|
| C1 | No port is refused for its rest state | 16 of 16 refused |
| C2 | No certified port has a count different from its need, and at least 2 of the 16 ports are certified, at status 3 or by rule A1 | none contradicted; 0 certified |
| C3 | No prediction on the four ports of L12 unless S3 gives a shift below 0.004 on both ports. If it does: at least 2 of the 4 are certified again at status 3 | 0 of 4 |

**C3 makes no prediction here**: S3 gave +0.0091 on both ports of
layout 2.2. The number of the four ports certified again is reported as
a reading.

## Scope: the cells, the runs and the calibration of stage P

Unchanged ([`../AMENDMENT_2.md`](../AMENDMENT_2.md),
[`../AMENDMENT_4.md`](../AMENDMENT_4.md), `../phase1/p_plan.py`): the
65 runs of the primary analysis of stage P, with the primary list of
capacitances of layout 2.2. No secondary list, no run with resistance.

| | Runs | Count |
|---|---|---|
| Nominal cell | cell run, ramp, read, leak scan at 27 °C; refresh under 0.1 TΩ; cell run and refresh at 125 °C | 7 |
| Calibration | cells `5001` to `5008`: noiseless train and ramp of each; leak scan of `5001` and `5002` | 18 |
| The 8 cells | `6065`, `6002`, `6074`, `6051` (large room on the schematic) and `6082`, `6003`, `6031`, `6030` (small room): ramp, read, leak scan, noiseless gain run, and one noisy test run with the noise identifier 700000 + the seed | 40 |

| Input | File | sha256 |
|---|---|---|
| Capacitances, primary list | `phase1/p_caps_primary.csv` | `e7f753d59c5a5e1203472627fcf538e18b4a380b1062f916ba6d3a7216e286e6`, the file of the extraction and of the nominal stage |
| Source and drain areas | `phase1/p_areas.csv` | `19bd1f27e174c22c7b8b2eea9afb8d81fe4a744993539763ab46b819dd88542a`, the same file as for the earlier layouts |

- The runners of the campaigns are unchanged, run through the harness
  of stage P (`../phase1/p_run.py`).
- **The calibration is made on layout 2.2**, by `cert_analyze.py
  calibrate` on the results of this stage, as in stage P. The constants
  of stage P, which S3 used, are not used here.
- **The seven nominal runs are made again**, although the nominal stage
  made them: the scripts of the campaigns read them in the folder of
  the stage, and the calibration needs the nominal leak scan. They are
  the same simulations. The report says whether their rows are those of
  the nominal stage, byte for byte. This is not a second attempt of the
  nominal stage: [`S_REPORT.md`](S_REPORT.md) stands as it is.

## The queue

One machine, this one, four runs at a time, in this order
(`python3 -I phase1/c_stage.py plan`):

1. the seven nominal runs;
2. then calibration and cells in turn, the units of the two queues of
   stage P taken alternately: calibration `5001` with its leak scan,
   cell `6065`; calibration `5002` with its leak scan, cell `6030`;
   `5003`, `6031`; `5004`, `6002`; `5005`, `6074`; `5006`, `6003`;
   `5007`, `6082`; `5008`, `6051`.

A calibration unit is the noiseless train and the ramp of its seed. A
cell unit is, in this order: ramp, read, leak scan, noiseless gain run,
noisy test run. **Any prefix of the queue is usable**: it holds whole
cells, of large and of small room in turn (large, small, small, large,
large, small, small, large), with the calibration made so far.

## One attempt, and how it resumes

The launcher of stage P (`../phase1/execute.py`), with its rules
([`../AMENDMENT_2.md`](../AMENDMENT_2.md)):

- **One attempt marker**, `phase1/RUN_ATTEMPT_C.json`, pushed before
  the first run. It names the commit and the sha256 of
  [`PREDICTION.md`](PREDICTION.md), of this file, of `phase1/c_stage.py`
  and of the two inputs. A launch stops if one of them has changed.
  **There is no attempt 2.**
- Before its first run the machine reproduces the nominal run of the
  schematic and checks that the noise preload builds. If it fails, it
  runs nothing.
- The name of each run is pushed as started before it begins. Results
  are pushed as each group of four ends.
- **A run that started is never run again.** After a restart of the
  container, a run that was pushed as started and has no result is
  recorded as lost. A run that was never pushed as started proceeds, by
  the same command, under the same marker. A run that ends in failure
  stays failed.
- A lost run and a failed run give nothing to the analysis. Nothing
  replaces them.

## Analysis of a truncated campaign, fixed now

The campaign is truncated if one of the 65 runs has no result. The
report then says so and lists those runs. The rules of
[`../AMENDMENT_2.md`](../AMENDMENT_2.md), and what C1 to C3 need more:

| | Rule |
|---|---|
| A cell | Evaluable if its five runs have a result. A port is evaluable if its cell is |
| The constants `d0`, `kappa`, `mu`, `h_mu` | From the calibration on layout 2.2, if at least 4 calibration units and 1 calibration leak scan have their results, and the nominal leak scan too. Otherwise the constants of `../../circuit/certification/CALIBRATION.md` are used for every port, and the report says so |
| C1 | On every evaluable port on which rule A1 can be read. Not evaluable if there is none |
| C2, no contradiction | On every evaluable port. One contradiction makes C2 fail, whatever the number of ports |
| C2, the number certified, with `n` evaluable ports | At least 2 if `n` is 14 or 16; at least 1 if `n` is 6 to 12; not evaluable below 6 |
| C3 | No prediction here. Had it made one, it would need the four ports of L12 |

A prediction that is not evaluable is reported as such. It counts
neither as holding nor as failing.

## How C1 to C3 are read

`phase1/c_stage.py`, committed with this file. The analysis is that of
stage P (`../phase1/p_analyze.py`, unchanged): the scripts of the
campaigns run in a mirror on the results of this stage
(`cert_analyze.py` calibrate, predict, certify; `uncond_analyze.py`;
`uncond_amend1.py`), and rule A1 with the functions of
`../../reusable-controller/physical/asymmetric_check.py`.

| | Read as |
|---|---|
| C1 | A port is refused for its rest state if rule A1 gives "rest charge" among its reasons: the rest charge before one of the first `m + 1` reads of the port in its noisy test run is outside 0.1 to 0.1001, `m` being its need. As in stage P, where the 16 ports were refused so |
| C2 | As L11 of stage P: a port is certified if its status 3 is "certified" or if rule A1 finds it eligible; it is contradicted if its count differs from its need |
| C3 | The shift of S3 is computed again from the committed results of the nominal stage, as `s_stage.py` does |

The report also gives, **as readings and not as verdicts of this
stage**:

- L1 to L13 of the first layout, read on layout 2.2 by the script of
  stage P, beside what the first layout gave;
- the table of the 16 ports (gap, need, count, status 3, rule A1 and
  its two rooms);
- **the 8 and 10 silent pulses at 125 °C.** In the nominal stage of
  layouts 2.1 and 2.2 the two ports of the nominal cell fire after 8
  and after 10 silent pulses at 125 °C, not after the same number. No
  prediction covers it; it is a reading outside any verdict, and it is
  written in the report as such.

The second analysis of stage P with the constants of the campaign on
the schematic (decision D6) is not made: it decided nothing.

The analysis was tried on the committed results of the first layout
before this stage (no simulation). It gives again what
[`../phase1/P_REPORT.md`](../phase1/P_REPORT.md) says: 16 of 16 ports
refused for their rest state, no port certified, 0 of the 4 ports of
L12; and for L1 to L13, 11 hold and L4 and L12 fail.

## Time budget, one machine

From the wall times of the same runs in stage P, four at a time in the
order of the queue: **17 groups, about 80 minutes of wall time,
2.5 core-hours**, the preflight of a few minutes not included.

No run is cut for time by the session: a run has the time limit of the
harness, 1 hour. If the container restarts, the stage resumes by the rule
above; an interruption is written in the report by the runs it lost.

The report is written once, after the last run, and pushed as it comes.
Then the work stops.
