# Coincidence benchmark results

The first sweep used runner `b28e2cbb383819dcc19e78d951a9daf0a42b5025` and registered protocol
`1f04221262694383b1505a8d064f62903a85a34a`. The pinned kernel was `11f476c3eb299263b980d5b69fb4592e8c0c093b`.
Each box used 621 paired points, including 512 random draws,
and all registered label, port, offset and jitter combinations.
The results are numerical and describe the tested points and timer settings.

## Registered predictions

At 100 µs per model unit and ±10% current error, the cap candidates
reached both caps at every tested point in their respective fabrication boxes.
The wide-box candidate passed at nominal FIRE and at ±0.3% FIRE, and
failed at ±1% FIRE. Here is the minimum coincidence or rejection slack
with nominal ERROR thresholds. Positive slack passes the timing contract.

| FIRE error | R | Nominal timer | Wide cap | Best tested timer | Long discharge |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0% | +4.999235 µs | -3.997659 µs | +0.166627 µs | +0.166627 µs | +4.999497 µs |
| 0.3% | +4.486972 µs | -4.010927 µs | +0.004346 µs | +0.004346 µs | +4.682088 µs |
| 1% | +3.291433 µs | -4.624617 µs | -0.374641 µs | -0.374641 µs | +3.941416 µs |
| 2% | +1.581924 µs | -5.576654 µs | -0.916881 µs | -0.916881 µs | +2.883003 µs |
| 3% | -0.131014 µs | -7.037815 µs | -1.460136 µs | -1.460136 µs | +1.823921 µs |
| 5% | -3.574217 µs | -10.116328 µs | -2.549855 µs | -2.549855 µs | -0.297590 µs |

## Coverage of the tested grid

Each row counts passing ERROR × FIRE boxes out of 36.
Timer results are at ±10% current error. R and the discharge
ablation use the common fabrication and threshold parameters.

| Scale (µs/unit) | Fabrication radius | R | Nominal timer | Capped candidate | Best tested timer | Long discharge | R passes and all tested timers fail |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 50 | 0% | 33 | 18 | 36 | 36 | 36 | 0 |
| 50 | 0.3% | 33 | 18 | 36 | 36 | 36 | 0 |
| 50 | 10% | 33 | 18 | 36 | 36 | 36 | 0 |
| 100 | 0% | 17 | 0 | 36 | 36 | 28 | 0 |
| 100 | 0.3% | 17 | 0 | 36 | 36 | 28 | 0 |
| 100 | 10% | 17 | 0 | 12 | 12 | 28 | 7 |
| 200 | 0% | 8 | 0 | 30 | 30 | 17 | 0 |
| 200 | 0.3% | 8 | 0 | 30 | 30 | 17 | 0 |
| 200 | 10% | 8 | 0 | 0 | 0 | 17 | 8 |

At nominal ERROR thresholds, the long-discharge ablation passed the
wide-box cases at 1% and 2% FIRE where R passed and all constant-current
candidates failed. Its write was effectively a full discharge. Across all
three scales and fabrication radii, the long discharge passed every tested
box in which R passed.

The scored runs had one report from each trained read and silence on
untrained reads. The differences in the table concern timing. The best
timer column selects one common setting per declared box from the
registered runner grid. A failure of that grid leaves the unrestricted
timer comparison open.

The first-crossing times and gains agreed within 5e-9 in their respective units
on 24 spot checks using an independent DOP853 integration, including
an ERROR entry before pulse expiry. At the widest error setting,
quadrature orders 16 and 32 gave identical retained training charge
in the reported numerical precision.

## Reproduce

Use the command and pinned versions in the [runner guide](README.md).
The first-run outputs had these SHA-256 hashes.

- `points.npy` · `c5add045b33fdc19204c39263ffc1ce7a86449fbf0872a085febc9b8d2fa9a8f`
- `sweep.csv` · `777e9c9b78efec507870c7b1732b14f3afc7c1e2094ae544dacacfcf67fe274f`
