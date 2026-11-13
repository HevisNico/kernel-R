# Repetition campaign: report

Written by `rep_analyze.py report` under [`PREDICTION.md`](PREDICTION.md) and [`AMENDMENT_1.md`](AMENDMENT_1.md). Step study: [`STEP.md`](STEP.md). Options: [`ACCEL.md`](ACCEL.md). One row per port and repetition: [`trials.csv`](trials.csv). One row per port: [`ports.csv`](ports.csv).

Repetitions analysed: 20 of 20 (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19); 1140 trials of 1140 planned. Step of the transient analysis: 200n.

## Summary

1. **Step.** 200 ns was kept by the rule written in advance. Between 200, 100 and 50 ns the change of `eps3` stays within the integration margin `MG` = 0.0001 ([`STEP.md`](STEP.md)); this is a sensitivity to the step, not a bound on the error of the solver.
2. **Count.** The count is the predicted `m` in 1140 of 1140 trials (57 ports, 20 repetitions each, fresh noise each time). One-sided 95% Clopper-Pearson upper bound on the probability of a wrong count, trials pooled: 0.262%. Pooling assumes interchangeable ports and independent trials.
3. **Per port.** The largest number of wrong counts for one port is 0 of 20; 57 ports have none. With no wrong count in 20 repetitions the bound for one port is 13.9%, and 29.7% simultaneously for the 57 ports.
4. **`eps3` on noisy runs.** With the two constants of each port frozen at their values without noise: median 0.00070, largest 0.00099; it is at most the `eps3` measured without noise in 929 of 1140 trials. Refitted on each run: median 0.00073, largest 0.00100.
5. **Certified repetitions.** 925 of 1140 trials satisfy rule A1 with every bound measured on the repetition itself, `eps3` included; the count is wrong in 0 of them. It stays a simulation; the gain of a read with a FIRE is checked by the current up to 0.75 unit only.

## Predictions

| | Prediction | Measured | Verdict |
|---|---|---|---|
| R1 | between 200, 100 and 50 ns `eps3` moves by at most 0.0001 | see [`STEP.md`](STEP.md) | holds |
| R2 | no run fails | 0 of 1040 runs without a usable result | holds |
| R3 | the count is the predicted `m` in at least 97% of the trials | 1140 of 1140 (100.00%) | holds |
| R4 | no port has its count wrong in more than 10% of its repetitions | largest number of wrong counts for one port: 0 of 20; ports above 10%: 0 | holds |
| R5 | the median `eps3` measured on the noisy runs is between 0.0005 and 0.003 | 0.00070 over 1140 trials | holds |
| R6 | no repetition certified on its own measures has a wrong count | 0 of 925 certified trials | holds |
| R7 | the noise of every run is different | 1040 different noises over 1040 runs | holds |

## Failures

- **F1, a repetition certified on its own measures with a wrong count:** none.
- **F2, a port with a wrong count in more than 10% of its repetitions:** none.
- **Runs without a usable result:** none.
- **Runs that share a noise:** none.

## `eps3` on noisy runs, and repeatability, per port

`37`: port certified by status 3 of the certification-unconditional campaign; `A1 only`: port that passes rule A1 only. Bounds are one-sided 95% Clopper-Pearson upper bounds on the probability of a wrong count.

| Cell | Port | m | Group | Trials | Count = m | Wrong | Upper bound | Simultaneous | `eps3` without noise | `eps3` noisy, median | largest | refitted, median | largest | At most the noiseless `eps3` | Certified | Contradicted |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `t6002` | 1 | 2 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00052 | 0.00048 | 0.00055 | 0.00053 | 0.00057 | 15 | 18 | 0 |
| `t6003` | 1 | 5 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00096 | 0.00093 | 0.00098 | 0.00095 | 0.00100 | 18 | 18 | 0 |
| `t6004` | 1 | 6 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00094 | 0.00092 | 0.00099 | 0.00094 | 0.00100 | 16 | 16 | 0 |
| `t6004` | 2 | 4 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00076 | 0.00072 | 0.00075 | 0.00074 | 0.00080 | 20 | 16 | 0 |
| `t6005` | 1 | 2 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00051 | 0.00048 | 0.00053 | 0.00050 | 0.00053 | 19 | 18 | 0 |
| `t6008` | 1 | 3 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00061 | 0.00060 | 0.00063 | 0.00062 | 0.00066 | 15 | 20 | 0 |
| `t6009` | 2 | 3 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00063 | 0.00061 | 0.00066 | 0.00064 | 0.00068 | 17 | 20 | 0 |
| `t6010` | 1 | 4 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00080 | 0.00080 | 0.00083 | 0.00082 | 0.00085 | 13 | 14 | 0 |
| `t6011` | 2 | 5 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00087 | 0.00083 | 0.00091 | 0.00087 | 0.00091 | 19 | 17 | 0 |
| `t6012` | 1 | 4 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00073 | 0.00071 | 0.00074 | 0.00074 | 0.00076 | 18 | 19 | 0 |
| `t6013` | 2 | 3 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00066 | 0.00063 | 0.00067 | 0.00065 | 0.00068 | 18 | 19 | 0 |
| `t6015` | 1 | 4 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00083 | 0.00080 | 0.00084 | 0.00082 | 0.00087 | 17 | 18 | 0 |
| `t6016` | 1 | 4 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00072 | 0.00071 | 0.00074 | 0.00073 | 0.00078 | 11 | 14 | 0 |
| `t6018` | 2 | 3 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00068 | 0.00064 | 0.00068 | 0.00067 | 0.00073 | 20 | 20 | 0 |
| `t6019` | 2 | 4 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00072 | 0.00070 | 0.00077 | 0.00073 | 0.00077 | 17 | 10 | 0 |
| `t6025` | 1 | 4 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00076 | 0.00074 | 0.00079 | 0.00076 | 0.00082 | 15 | 11 | 0 |
| `t6027` | 2 | 3 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00060 | 0.00056 | 0.00061 | 0.00059 | 0.00063 | 19 | 19 | 0 |
| `t6028` | 2 | 4 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00073 | 0.00068 | 0.00074 | 0.00072 | 0.00076 | 18 | 17 | 0 |
| `t6030` | 1 | 3 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00063 | 0.00060 | 0.00062 | 0.00062 | 0.00067 | 19 | 19 | 0 |
| `t6031` | 1 | 4 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00070 | 0.00067 | 0.00076 | 0.00070 | 0.00076 | 19 | 18 | 0 |
| `t6032` | 1 | 3 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00059 | 0.00057 | 0.00061 | 0.00059 | 0.00063 | 17 | 20 | 0 |
| `t6032` | 2 | 4 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00070 | 0.00067 | 0.00073 | 0.00069 | 0.00073 | 14 | 18 | 0 |
| `t6037` | 1 | 4 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00071 | 0.00068 | 0.00076 | 0.00070 | 0.00077 | 16 | 15 | 0 |
| `t6037` | 2 | 4 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00074 | 0.00072 | 0.00080 | 0.00075 | 0.00079 | 16 | 10 | 0 |
| `t6040` | 2 | 5 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00084 | 0.00082 | 0.00086 | 0.00084 | 0.00088 | 19 | 15 | 0 |
| `t6042` | 2 | 5 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00088 | 0.00086 | 0.00091 | 0.00089 | 0.00092 | 16 | 6 | 0 |
| `t6043` | 2 | 5 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00086 | 0.00082 | 0.00087 | 0.00085 | 0.00089 | 19 | 16 | 0 |
| `t6045` | 2 | 4 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00075 | 0.00073 | 0.00077 | 0.00076 | 0.00079 | 15 | 19 | 0 |
| `t6050` | 2 | 4 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00068 | 0.00066 | 0.00071 | 0.00068 | 0.00073 | 17 | 18 | 0 |
| `t6051` | 2 | 3 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00063 | 0.00060 | 0.00067 | 0.00064 | 0.00069 | 12 | 20 | 0 |
| `t6052` | 1 | 4 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00074 | 0.00073 | 0.00080 | 0.00075 | 0.00082 | 13 | 14 | 0 |
| `t6055` | 1 | 6 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00089 | 0.00086 | 0.00090 | 0.00089 | 0.00093 | 19 | 2 | 0 |
| `t6056` | 1 | 5 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00091 | 0.00090 | 0.00096 | 0.00092 | 0.00096 | 12 | 9 | 0 |
| `t6058` | 2 | 4 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00070 | 0.00068 | 0.00073 | 0.00071 | 0.00076 | 12 | 18 | 0 |
| `t6061` | 2 | 3 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00063 | 0.00061 | 0.00066 | 0.00064 | 0.00072 | 15 | 19 | 0 |
| `t6063` | 1 | 2 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00052 | 0.00048 | 0.00052 | 0.00051 | 0.00057 | 19 | 20 | 0 |
| `t6065` | 1 | 4 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00074 | 0.00072 | 0.00077 | 0.00074 | 0.00078 | 15 | 19 | 0 |
| `t6067` | 2 | 3 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00062 | 0.00061 | 0.00066 | 0.00062 | 0.00069 | 14 | 18 | 0 |
| `t6068` | 2 | 2 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00051 | 0.00048 | 0.00051 | 0.00051 | 0.00056 | 20 | 16 | 0 |
| `t6074` | 1 | 3 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00066 | 0.00061 | 0.00067 | 0.00065 | 0.00069 | 19 | 20 | 0 |
| `t6075` | 1 | 3 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00063 | 0.00061 | 0.00065 | 0.00063 | 0.00067 | 17 | 18 | 0 |
| `t6075` | 2 | 4 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00074 | 0.00070 | 0.00076 | 0.00072 | 0.00078 | 16 | 16 | 0 |
| `t6076` | 1 | 4 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00076 | 0.00074 | 0.00077 | 0.00077 | 0.00080 | 19 | 19 | 0 |
| `t6077` | 1 | 5 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00084 | 0.00082 | 0.00087 | 0.00084 | 0.00090 | 14 | 18 | 0 |
| `t6077` | 2 | 5 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00088 | 0.00086 | 0.00091 | 0.00088 | 0.00092 | 15 | 19 | 0 |
| `t6079` | 1 | 4 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00076 | 0.00074 | 0.00078 | 0.00077 | 0.00080 | 16 | 18 | 0 |
| `t6080` | 2 | 3 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00064 | 0.00063 | 0.00067 | 0.00064 | 0.00066 | 14 | 14 | 0 |
| `t6081` | 1 | 4 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00076 | 0.00073 | 0.00083 | 0.00075 | 0.00084 | 15 | 11 | 0 |
| `t6082` | 2 | 4 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00078 | 0.00074 | 0.00078 | 0.00076 | 0.00083 | 18 | 16 | 0 |
| `t6085` | 2 | 3 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00065 | 0.00063 | 0.00067 | 0.00065 | 0.00071 | 15 | 19 | 0 |
| `t6088` | 2 | 4 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00081 | 0.00080 | 0.00084 | 0.00081 | 0.00084 | 13 | 16 | 0 |
| `t6090` | 1 | 4 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00075 | 0.00075 | 0.00078 | 0.00078 | 0.00082 | 12 | 20 | 0 |
| `t6093` | 2 | 4 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00075 | 0.00073 | 0.00081 | 0.00075 | 0.00080 | 15 | 11 | 0 |
| `t6095` | 2 | 3 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00065 | 0.00062 | 0.00067 | 0.00064 | 0.00068 | 17 | 15 | 0 |
| `t6096` | 1 | 3 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00061 | 0.00059 | 0.00064 | 0.00062 | 0.00067 | 19 | 19 | 0 |
| `t6098` | 2 | 5 | 37 | 20 | 20 | 0 | 13.9% | 29.7% | 0.00082 | 0.00080 | 0.00087 | 0.00083 | 0.00086 | 15 | 19 | 0 |
| `t6099` | 1 | 5 | A1 only | 20 | 20 | 0 | 13.9% | 29.7% | 0.00085 | 0.00083 | 0.00091 | 0.00086 | 0.00090 | 17 | 4 | 0 |

| Group | Ports | Trials | Wrong counts | Upper bound, pooled |
|---|---|---|---|---|
| 37 | 37 | 740 | 0 | 0.404% |
| A1 only | 20 | 400 | 0 | 0.746% |

| Machine | Trials | Wrong counts |
|---|---|---|
| A | 570 | 0 |
| B | 570 | 0 |

## Trials with a wrong count

None.

## Traces

- Reduced traces: 1040 traces in 20 archives of the private repository `HevisNico/kernel-R-circuit`, folder `09-repetition-traces/`. Each archive was read back from GitHub and its SHA-256 compared before the local traces were removed; the SHA-256 of each archive and of each trace is in `results/repeat/repNN/ARCHIVE.json`.
- A reduced trace holds, for each read 0 to `m` of a port of rule A1, the solver points of its pulse and the signals that enter a measure: main charge, latch, noise of the threshold, steering, and the currents of the two mirrors with their noise.
- A noisy run is replayed by its noise number: the process id seen by the simulator is fixed, the binary is not modified (`fakepid.c`, [`PREFLIGHT.md`](PREFLIGHT.md)).
