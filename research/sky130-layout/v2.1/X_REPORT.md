# Layout 2.1: X1 to X7

Written by `layout/x_check.py` under [`PREDICTION.md`](PREDICTION.md). **An extraction, not a simulation.** The capacitances are those Magic extracts by rules, primary list.

**5 hold, 2 fail, of 7.**

| | Prediction | Layout 2.1 | Second layout | Verdict |
|---|---|---|---|---|
| X1 | Between `vq` and each loud net at most 0.03 fF, and at most 0.10 fF in all; device floor subtracted for `adm` | largest 0.0426 fF (`vrefmn`); in all 0.0435 fF over 102 loud nets | largest 0.049 fF (`vrefmn`); in all 0.052 fF | fails |
| X2 | Between a summing node and `vs` of its port at most 0.10 fF; and each other loud net at most 0.03 fF; device floor subtracted for `si` | port 1: `vs` 0.0000 fF, largest other 0.0118 fF (`x1.si`); port 2: `vs` 0.0000 fF, largest other 0.0118 fF (`x2.si`) | port 1: `vs` 0.000 fF, largest other 0.000 fF (`cmpm`); port 2: `vs` 0.000 fF, largest other 0.000 fF (`cmpm`) | holds |
| X3 | The capacitances with one end on `vq`, summed: at most 45 fF | 52.33 fF | 39.73 fF | fails |
| X4 | For every net of a port, its capacitance to `vq` in port 1 and in port 2 differ by at most 0.1 fF | largest difference 0.0131 fF (`sum`), over 4 nets | largest difference 0.00 fF (`admb`) | holds |
| X5 | Magic DRC 0 and LVS match on each block and on the cell; no wire under a capacitor; at most 0.085 mm² | 9 of 9 blocks clean; flattened cell: 0 DRC errors; `capm.10` and `capm.2b`: 0 reports; 375.2 µm × 215.0 µm = 0.0807 mm² | 9 of 9; 0; 0; 0.0836 mm² | holds |
| X6 | In each port, between `x`, `vgd` or `vs` and `si` or `sd`: at most 0.05 fF each; device floor subtracted for `x`–`sd` and `x`–`si` | largest 0.0332 fF (port 1, `x`–`si`) | largest 1.104 fF (port 1, `vgd`–`si`) | holds |
| X7 | In each port, the capacitances with one end on `vs`, summed: at most 10 fF | port 1: 6.99 fF; port 2: 6.99 fF | port 1: 11.96 fF; port 2: 11.94 fF | holds |

Device floor, the switch of 1 µm by 0.15 µm drawn alone: gate to drain exit 0.0355 fF, gate to source exit 0.0355 fF.

### X1: the largest capacitances between `vq` and a loud net

| Loud net | Layout 2.1 | Second layout |
|---|---|---|
| `vrefmn` | 0.0426 fF | 0.0492 fF |
| `x1.adm` | 0.0009 fF | 0.0001 fF |
| `cmpm` | 0.0000 fF | 0.0000 fF |
| `cmpmb` | 0.0000 fF | 0.0000 fF |
| `p` | 0.0000 fF | 0.0000 fF |
| `pb` | 0.0000 fF | 0.0000 fF |
| `pbdel` | 0.0000 fF | 0.0000 fF |
| `pd1` | 0.0000 fF | 0.0000 fF |

### X2: the largest capacitances between a summing node and a loud net

| Port | Loud net | Layout 2.1 | Second layout |
|---|---|---|---|
| 1 | `x1.si` | 0.0118 fF | 0.0000 fF |
| 1 | `cmpm` | 0.0000 fF | 0.0000 fF |
| 1 | `cmpmb` | 0.0000 fF | 0.0000 fF |
| 1 | `p` | 0.0000 fF | 0.0000 fF |
| 2 | `x2.si` | 0.0118 fF | 0.0000 fF |
| 2 | `cmpm` | 0.0000 fF | 0.0000 fF |
| 2 | `cmpmb` | 0.0000 fF | 0.0000 fF |
| 2 | `p` | 0.0000 fF | 0.0000 fF |

### X3: where the capacitance of `vq` goes

| To | Layout 2.1 | Second layout |
|---|---|---|
| `0` | 42.09 fF | 28.95 fF |
| `vr0` | 3.07 fF | 2.48 fF |
| `vdd` | 2.81 fF | 3.20 fF |
| `xcmpm.tail` | 1.96 fF | 1.98 fF |
| `xcmpm.o1m` | 1.72 fF | 1.64 fF |
| `vpre` | 0.19 fF | 0.04 fF |
| `x2.dq` | 0.18 fF | 0.19 fF |
| `x1.dq` | 0.18 fF | 0.19 fF |

### X6: the sensor nodes and the two steering controls

| Port | Pair | Layout 2.1, floor subtracted | as extracted | Second layout, floor subtracted | as extracted |
|---|---|---|---|---|---|
| 1 | `vgd`–`sd` | 0.0028 fF | 0.0028 fF | 0.0062 fF | 0.0062 fF |
| 1 | `vgd`–`si` | 0.0000 fF | 0.0000 fF | 1.1038 fF | 1.1038 fF |
| 1 | `vs`–`sd` | 0.0000 fF | 0.0000 fF | 0.2470 fF | 0.2470 fF |
| 1 | `vs`–`si` | 0.0000 fF | 0.0000 fF | 0.2022 fF | 0.2022 fF |
| 1 | `x`–`sd` | 0.0001 fF | 0.0355 fF | 1.0765 fF | 1.1120 fF |
| 1 | `x`–`si` | 0.0332 fF | 0.0687 fF | 0.9483 fF | 0.9838 fF |
| 2 | `vgd`–`sd` | 0.0028 fF | 0.0028 fF | 0.0063 fF | 0.0063 fF |
| 2 | `vgd`–`si` | 0.0000 fF | 0.0000 fF | 1.1038 fF | 1.1038 fF |
| 2 | `vs`–`sd` | 0.0000 fF | 0.0000 fF | 0.2478 fF | 0.2478 fF |
| 2 | `vs`–`si` | 0.0000 fF | 0.0000 fF | 0.2022 fF | 0.2022 fF |
| 2 | `x`–`sd` | 0.0001 fF | 0.0355 fF | 1.0765 fF | 1.1120 fF |
| 2 | `x`–`si` | 0.0332 fF | 0.0687 fF | 0.9483 fF | 0.9838 fF |

### X7: where the capacitance of `vs` goes, port 1

| To | Layout 2.1 | Second layout |
|---|---|---|
| `0` | 3.19 fF | 5.39 fF |
| `vmem1` | 1.60 fF | 1.68 fF |
| `vdd` | 0.95 fF | 2.28 fF |
| `x1.xcmps.tail` | 0.25 fF | 0.25 fF |
| `x1.xcmps.o1` | 0.24 fF | 0.25 fF |
| `vpre` | 0.19 fF | 0.71 fF |
| `x1.xcmps.o2` | 0.15 fF | 0.17 fF |
| `vcm` | 0.13 fF | 0.10 fF |
| `x1.ibs` | 0.13 fF | 0.22 fF |
| `x1.preb` | 0.10 fF | 0.16 fF |

## Not part of the verdicts

KLayout deck, reports by rule: `licon.1` 184, `licon.12` 3, `licon.7` 46, `m3.3ab` 10, `m4.5ab` 281.
Antenna check of Magic: 1 Antenna violation detected at plane metal4;       1 Effective antenna ratio 913.661 > limit 400.
