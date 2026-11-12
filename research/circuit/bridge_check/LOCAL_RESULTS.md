# Window endpoints, local increments and latch events

Written by `local_analyze.py` under `GAIN_PROTOCOL.md` and `LOCAL_PROTOCOL.md`. No simulation is run here.
These are finite-trace diagnostics of five replays. They are not uniform bounds and not Lean certificates.

## Calibration by temperature

| Temperature | Global fit over 0.35 to 0.42 V: beta per V | largest error | Observed range (V) | Local beta per V | 1/beta (mV) | epsilon per V | Secants (min, max) per V | All negative | Local fit largest error |
|---|---|---|---|---|---|---|---|---|---|
| -40 °C | 38.340 | 0.1119 | 0.3865 to 0.3900 (8 points) | 38.609 | 25.90 | 2.757 | -41.366, -38.492 | yes | 0.04481 |
| 27 °C | 31.198 | 0.0786 | 0.3805 to 0.3985 (37 points) | 31.377 | 31.87 | 1.937 | -33.315, -31.038 | yes | 0.04115 |
| 125 °C | 24.161 | 0.0600 | 0.3800 to 0.3900 (21 points) | 24.160 | 41.39 | 1.264 | -25.424, -24.063 | yes | 0.03663 |

The error of a step of the stored voltage is at most `epsilon * |delta V|` for the piecewise-linear interpolation of each DC curve. It is not a bound on the transistor between grid points, nor on a pulse, nor on a device with mismatch.

At 27 °C the nominal dose is `beta * (Cs/Cf) * 0.1` = 0.04184 with the local slope, 0.04160 with the global one. For a step of one dose, 1.35 mV, the local error bound is 0.00262 in log-gain; the endpoint error of the global law is 0.1572.

## Write windows

A window goes from the entry latch to the exit latch of the pulsed port. Log-gain values use the local slope at 27 °C. The calibration is that of nominal devices: for the mismatch cell it is a proxy.

| Run | Silent windows | Sensor dose | Sensor tolerance (largest) | Residual, in log-gain (largest) | Summing-node move (largest) | Step at the window (range) | Local error bound of a step (largest) | Read-to-read increment (range) | Not explained by the window (largest) | Increments positive |
|---|---|---|---|---|---|---|---|---|---|---|
| `nominal_200ns_retry1` | 8 | 0.04191 to 0.04191 | 7.47e-05 | 1.32e-03 | 4.60e-04 | 0.04277 to 0.04278 | 2.64e-03 | 0.04225 to 0.04225 | 9.83e-04 | 8 of 8 |
| `nominal_100ns_retry1` | 8 | 0.04191 to 0.04191 | 7.48e-05 | 1.32e-03 | 4.59e-04 | 0.04277 to 0.04278 | 2.64e-03 | 0.04225 to 0.04225 | 9.83e-04 | 8 of 8 |
| `mm2064_quiet_retry1` | 9 | 0.04181 to 0.04193 | 9.37e-05 | 1.38e-03 | 4.35e-04 | 0.04270 to 0.04288 | 2.65e-03 | 0.04210 to 0.04232 | 1.01e-03 | 9 of 9 |
| `mm2064_noise_1_retry1` | 9 | 0.04137 to 0.04224 | 4.69e-04 | 1.38e-03 | 1.17e-02 | 0.03304 to 0.05512 | 3.40e-03 | 0.01981 to 0.06596 | 2.33e-02 | 9 of 9 |
| `mm2064_noise_2_retry1` | 9 | 0.04137 to 0.04229 | 4.62e-04 | 1.40e-03 | 2.45e-02 | 0.01814 to 0.05562 | 3.43e-03 | 0.03654 to 0.05971 | 1.63e-02 | 9 of 9 |

On a window with a FIRE the sensor current goes to the dump, so the quantity to bound is the change of the capacitor itself.

| Run | Firing windows | Steering switch turned on | Capacitor change, in log-gain (largest) | Step at the window (largest) | Read-to-read increment (largest) |
|---|---|---|---|---|---|
| `nominal_200ns_retry1` | 14 | 0 | 3.16e-07 | 9.82e-05 | 7.80e-05 |
| `nominal_100ns_retry1` | 14 | 0 | 3.16e-07 | 9.84e-05 | 7.80e-05 |
| `mm2064_quiet_retry1` | 13 | 0 | 3.02e-07 | 9.51e-05 | 7.81e-05 |
| `mm2064_noise_1_retry1` | 13 | 0 | 1.75e-05 | 2.28e-02 | 2.46e-02 |
| `mm2064_noise_2_retry1` | 13 | 0 | 1.68e-05 | 2.18e-02 | 1.73e-02 |

With the global affine law, the sign of a silent step is robust to twice its largest error on 0 of 8 windows of `nominal_200ns_retry1`, 0 of 8 windows of `nominal_100ns_retry1`, 0 of 9 windows of `mm2064_quiet_retry1`, 0 of 9 windows of `mm2064_noise_1_retry1`, 0 of 9 windows of `mm2064_noise_2_retry1`.

## FIRE and comparator events

FIRE is the rising crossing of the protection latch at 0.9 V. The raw comparator is a different signal.

| Run | Periods with FIRE | Latch rises per period | Latch high for (µs) | Comparator transitions in a period with FIRE | in a silent period | Comparator segments shorter than 200 ns | longest of them (ns) | Comparator transitions around the latch rise (ns from it) | around the latch fall (ns from it) | inside an ERROR window | Nearest to an ERROR window (µs) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `nominal_200ns_retry1` | 13 | [0, 1] | 93.6 to 93.8 | [6] | 0 | 52 | 2.64 | -0.12 to +2.73 | -0.35 to +2.35 | 0 | 17.31 |
| `nominal_100ns_retry1` | 13 | [0, 1] | 93.6 to 93.8 | [6] | 0 | 52 | 2.64 | -0.12 to +2.73 | -0.35 to +2.35 | 0 | 17.30 |
| `mm2064_quiet_retry1` | 12 | [0, 1] | 98.0 to 98.2 | [6] | 0 | 48 | 2.65 | -0.12 to +2.73 | -0.33 to +2.36 | 0 | 16.63 |
| `mm2064_noise_1_retry1` | 12 | [0, 1] | 97.2 to 98.3 | [6] | 0 | 48 | 2.65 | -0.11 to +2.73 | -0.35 to +2.36 | 0 | 16.39 |
| `mm2064_noise_2_retry1` | 12 | [0, 1] | 97.3 to 98.5 | [6] | 0 | 48 | 2.66 | -0.12 to +2.73 | -0.33 to +2.36 | 0 | 16.25 |

- The protection latch rises at most once per period in these replays, and falls once after each rise.
- The raw comparator has several transitions in every period with a FIRE. The statement that there is no extra crossing holds for the latch, not for the comparator.
- Every comparator transition of these replays lies within the nanoseconds given above of a latch transition: three around the FIRE and three around the release. The latch has one rise and one fall in such a period. No comparator transition falls inside an ERROR window, and the nearest is more than 16 µs away from one.
- Every transition, with its date, its dwell lengths and its distance to the latch transitions and to the ERROR windows, is in `latch_events.csv`.
- The delayed enable nodes of the latch are not saved, so the comparison with its 200 ns lockout is descriptive.
