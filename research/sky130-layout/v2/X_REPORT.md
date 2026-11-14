# Second layout: X1 to X5

Written by `layout/x_check.py` under [`PREDICTION.md`](PREDICTION.md). **An extraction, not a simulation.** The capacitances are those Magic extracts by rules, primary list.

**4 hold, 1 fail, of 5.**

| | Prediction | Second layout | First layout | Verdict |
|---|---|---|---|---|
| X1 | Between `vq` and each loud net at most 0.03 fF, and at most 0.10 fF in all; device floor subtracted for `adm` | largest 0.0492 fF (`vrefmn`); in all 0.0519 fF over 102 loud nets | largest 1.674 fF (`x1.ad`); in all 3.563 fF | fails |
| X2 | Between a summing node and `vs` of its port at most 0.10 fF; and each other loud net at most 0.03 fF; device floor subtracted for `si` | port 1: `vs` 0.0000 fF, largest other 0.0000 fF (`cmpm`); port 2: `vs` 0.0000 fF, largest other 0.0000 fF (`cmpm`) | port 1: `vs` 0.918 fF, largest other 0.191 fF (`x1.si`); port 2: `vs` 0.920 fF, largest other 0.191 fF (`x2.si`) | holds |
| X3 | The capacitances with one end on `vq`, summed: at most 45 fF | 39.73 fF | 75.55 fF | holds |
| X4 | For every net of a port, its capacitance to `vq` in port 1 and in port 2 differ by at most 0.1 fF | largest difference 0.0000 fF (`adm`), over 3 nets | largest difference 8.28 fF (`dq`) | holds |
| X5 | Magic DRC 0 and LVS match on each block and on the cell; no wire under a capacitor; at most 0.085 mm² | 9 of 9 blocks clean; flattened cell: 0 DRC errors; `capm.10` and `capm.2b`: 0 reports; 387.5 µm × 215.7 µm = 0.0836 mm² | 9 of 9; 0; 0; 0.0742 mm² | holds |

Device floor, the switch of 1 µm by 0.15 µm drawn alone: gate to drain exit 0.0355 fF, gate to source exit 0.0355 fF.

### X1: the largest capacitances between `vq` and a loud net

| Loud net | Second layout | First layout |
|---|---|---|
| `vrefmn` | 0.0492 fF | 0.6908 fF |
| `xcmpm.o1` | 0.0013 fF | 0.0393 fF |
| `xcmpm.o2` | 0.0013 fF | 0.0013 fF |
| `x1.adm` | 0.0001 fF | 0.0613 fF |
| `x2.adm` | 0.0001 fF | 0.0418 fF |
| `cmpm` | 0.0000 fF | 0.0000 fF |
| `cmpmb` | 0.0000 fF | 0.0000 fF |
| `p` | 0.0000 fF | 0.0000 fF |

### X2: the largest capacitances between a summing node and a loud net

| Port | Loud net | Second layout | First layout |
|---|---|---|---|
| 1 | `cmpm` | 0.0000 fF | 0.0000 fF |
| 1 | `cmpmb` | 0.0000 fF | 0.0000 fF |
| 1 | `p` | 0.0000 fF | 0.0000 fF |
| 1 | `pb` | 0.0000 fF | 0.0000 fF |
| 2 | `cmpm` | 0.0000 fF | 0.0000 fF |
| 2 | `cmpmb` | 0.0000 fF | 0.0000 fF |
| 2 | `p` | 0.0000 fF | 0.0000 fF |
| 2 | `pb` | 0.0000 fF | 0.0000 fF |

### X3: where the capacitance of `vq` goes

| To | Second layout | First layout |
|---|---|---|
| `0` | 28.95 fF | 31.31 fF |
| `vdd` | 3.20 fF | 3.72 fF |
| `vr0` | 2.48 fF | 3.51 fF |
| `xcmpm.tail` | 1.98 fF | 1.94 fF |
| `xcmpm.o1m` | 1.64 fF | 1.64 fF |
| `ibm` | 0.95 fF | 1.39 fF |
| `x1.dq` | 0.19 fF | 0.81 fF |
| `x2.dq` | 0.19 fF | 9.09 fF |

## Not part of X5

KLayout deck, reports by rule: `licon.1` 184, `licon.12` 3, `licon.7` 46, `m3.3ab` 9, `m4.5ab` 280.
Antenna check of Magic: 2 Antenna violation detected at plane metal1;       1 Antenna violation detected at plane metal4;       2 Effective antenna ratio 408.037 > limit 400;       1 Effective antenna ratio 913.661 > limit 400.
