# Amendment 1: the current of the mirror after a FIRE, and a third status

Pushed before the first run of a test cell. When it is written, the two
preflight runs on the nominal cell exist and nothing else. `PREDICTION.md`
is not edited. Its statuses 1 and 2 are computed and reported as
registered. This amendment adds a status 3 beside them, and both results
are shown.

## What the preflight showed on the nominal cell

`PREFLIGHT.md` lists, read by read, the gain `Z` of the certification
campaign and the gain `GI` measured on the current of the mirror over
the whole pulse.

- **Silent reads.** `Z - GI` goes from -0.02739 to -0.02670 over the
  four silent reads of a port: after one constant, the two gains agree
  within 0.00035.
- **Reads with a FIRE.** `Z - GI` is -0.03050 in the training, 0.00345
  away from the constant of the silent reads. In the leak scan it goes
  from -0.02704 for a FIRE at 0.994 unit to -0.03237 for a FIRE at
  0.837 unit: the earlier the FIRE, the larger the distance.

The cause is in the measure, not in `Z`. `PREDICTION.md` says that after
a FIRE the current of the mirror "is steered away from the main
capacitor but still flows". It does flow, but it is not the same
current: its drain goes from the main capacitor, near 0.8 V, to the rest
voltage, 1.25 V, and the current rises. In the leak scan, 0.99 unit
after the start of the pulse, the current is 7.470e-8 A in read 31
(FIRE at 0.9945, not yet cut) and 8.527e-8 A in read 30, whose gain is
0.0018 higher and whose FIRE is at 0.9834. So `GI` over the whole pulse
is not the charge that an uncut read with a FIRE would have delivered.
The registered `eps_peak` would be 0.00355 on the two nominal ports and
`eps_scan` 0.00551 on the nominal cell, almost all of it from this.

Before the FIRE the current is not disturbed. Measured from the start of
the pulse to 0.75 unit, the date of the early gain `Y`, the charge
follows `Y` through the reads with a FIRE without a step: `Y - GE` goes
from -0.03158 to -0.03090 over the silent reads and is -0.03061 in the
reads with a FIRE of the training.

## The rule added

```text
WE = (1 / (Cq * 0.5 V)) * integral from the start ts of the pulse to ts + 0.75 unit
                          of  Im(t) * exp(-(ts + 0.75 unit - t) / (2 units))  dt
GE = log(WE)
DE = mean of Y - GE over the silent reads of the port in the run
eps3 = the larger of
         the largest |G - GI - D|   over the silent reads of the port in the run        (as registered)
         the largest |Y - GE - DE|  over its reads that have a gain: silent, or FIRE at 0.76 or later
       plus mg
```

`Y` is the early gain of the certification campaign, for a silent read
as for a read with a FIRE. `mg = 0.0001`, as registered. A read with a
FIRE earlier than 0.76 is left out and counted, as registered.
`eps3(port)` comes from the training without noise of the cell,
`eps3_scan(cell)` from its leak scan. If a port has no silent read in
its run, or a value is missing or not positive, `eps3` is not evaluable.

So a silent read is checked as registered, over the whole pulse. A read
with a FIRE is checked on its early gain `Y`, up to 0.75 unit. Its gain
is `Y + kappa`: the step from 0.75 unit to the end of the pulse is not
measured by any current, because the FIRE changes the path of the
current. That step stays covered by `kappa` and `eps_kappa` of the
certification campaign, which were measured on silent reads.

**Status 3** is status 2 with `eps3` in place of `eps_peak` and
`eps3_scan` in place of `eps_scan`:

```text
a3  = a + eps3(port)
B3  = B + 2*eps3(port)
Pf3 = 0.1 + (c - 0.1)*exp(-1/2) + exp(Y + kappa + eps3_scan(cell))
h3  = max(|Ps - level0|, |Pf3 - level0|)
ell3  = h3 + noise + mq
room3 = d0/2 - a3 - B3 - (20/17)*ell3 - 1/8000
```

with the rules of status 2 for not evaluable, outside the certified
domain, certified with the count confirmed and certified with the count
contradicted. Failure F1 of `PREDICTION.md` also covers status 3.

Status 2 stays what `PREDICTION.md` calls the new status of a port, and
`REPORT.md` is written by `uncond_analyze.py` as pushed. Status 3 is
written by `uncond_amend1.py` in `REPORT_AMENDMENT_1.md`, which shows
the status of the certification campaign and statuses 1, 2 and 3 side by
side. Status 3 is the status that this campaign puts forward for
condition 2; status 2 shows what the registered measure gives.

## Extraction

`uncond_run.py` is not modified. `uncond_early.py` reads the compact
trace of a run, checks its SHA-256 against the metadata of the run, and
writes `results/STAGE/NAME.early.csv`. It is run on each slice before
the slice is pushed. `uncond_amend1.py report` is run once, after
`uncond_analyze.py report`.

## Predictions added

Written after the preflight on the nominal cell was seen, where `eps3`
is 0.00075 on the two ports. U5 and U6 stay as registered.

| | Prediction |
|---|---|
| U8 | The median `eps3` of the 200 ports is between 0.0004 and 0.002 |
| U9 | Status 3 certifies 35 to 58 ports |
| U10 | No port certified by status 3 has its count contradicted |

## What status 3 still rests on

What `PREDICTION.md` lists, and one more line: the gain of a read with a
FIRE is checked by the current of the mirror up to 0.75 unit only; from
there to the end of the pulse it rests on `kappa` and `eps_kappa`.
