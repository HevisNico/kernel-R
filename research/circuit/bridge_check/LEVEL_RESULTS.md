# The threshold budget in two parts

Written by `level_analyze.py` under `LEVEL_PROTOCOL.md`. Levels are in the declared coordinate `q`.

Cell `mc_2064`. Reference level of the historical table: `level0 = 0.1 + 0.45059 / 0.5` = 1.00118.

| Part | Value | From |
|---|---|---|
| `ell_static` | 0.00028 | 11 single-port periods with a FIRE in the replay without noise; their level goes from 1.00125 to 1.00146 |
| `ell_dynamic` | 0.00241 | 22 paired periods of the two noisy replays: largest \|delta\| 0.00219, standard deviation 0.00080, mean +0.00046. A statistic, not a certified bound |
| `ell` | 0.00269 | their sum |

Smallest level seen: 1.00042. `19/20 <= level` and `19/20 <= level0`: yes on these values.

Periods with a FIRE in only one of a noisy replay and the quiet one, left out of `delta`: none.

## room

`d0`, `a`, `m` and `b` are those of the historical table. Only `ell` changes.

| Port | Observed silent pulses | m | room with `ell = 0` (historical) | room with `ell_static` | room with `ell_static + ell_dynamic` (statistical) |
|---|---|---|---|---|---|
| `mc_2064`, port 1 | 3 | 4 | +0.000233 | -0.000100 | -0.002933 |
| `mc_2064`, port 2 | 5 | 5 | -0.012314 | -0.012647 | -0.015480 |

The first value reproduces the historical table. The second uses a measure made on the cell. The third adds a statistic of two replays and is not certified for the original trajectory.
