# Certification with the level of each cell and an independent measure of the gain: rules, criteria and predictions

Pushed to the public repository before the first run of this campaign.
The time at which GitHub receives this push is the date of these rules.
This file is not edited afterwards. A deviation is declared in a new
file, pushed before the run or the computation that it concerns.

## What is known when this is written

Everything of the certification campaign in `../certification/`: its
rules, its 350 runs, its constants, its predicted needs and its report.
59 ports of 200 are certified there under two declared conditions
(`../certification/AMENDMENT_3.md`):

1. the offset `mu` between the firing level and the static level, and
   its bound `h_mu`, are measured on six cells and applied to the 100
   test cells;
2. the gain of a read is inferred from the peak of the main charge
   through the scalar model.

No run of this campaign exists. One simulator run was made before this
push, on a deck of one transistor that is not the cell: it checked that
ngspice 42 can save the drain current of a transistor inside a
subcircuit under the name used below. It says nothing about the cell.

Nothing of `../certification/` is modified. Its results, its statuses
and its verdicts E1 to E8 stay as they are.

## Purpose

Measure both things on the test cells themselves, and give each of the
200 ports a new status with its own bounds, next to its status of the
certification campaign.

## Simulator, sources and extraction

As in `../certification/manifest.json`: ngspice 42 (Ubuntu package
42+ds-3build1, same SHA-256), the SKY130 models at the same commit, the
same netlist, the same solver options, a largest step of 200 ns, 27 °C.
Every run of this campaign is without noise.

`uncond_run.py` calls the function `main` of `../certification/cert_run.py`,
which is not modified (its SHA-256 is in `manifest.json` and is checked
at each run). Two things are set before the call: the folder of the
results, and two more saved signals. The deck, the rows and the compact
trace of a run are therefore made by the code of the certification
campaign.

The two more signals are the drain currents of the output transistor of
the gain mirror of each port, `xmout`:
`@m.x1.xmout.msky130_fd_pr__nfet_01v8[id]` and the same for `x2`. Saving
a signal adds no element to the circuit.

The compact traces go to the private repository, their SHA-256 to the
public metadata of each run, as in the certification campaign.

## Runs

`manifest.json` holds the complete ordered list. Every run is made once.
A run that fails stays failed and is reported. `uncond_launch.py` ends
with a status that is not zero when a run fails.

| Stage | Runs | What |
|---|---|---|
| 0. Preflight | 2 | Nominal cell: the training and the leak scan of the preflight of the certification campaign, with the two more signals |
| 1. Leak scans | 100 | Mismatch seeds 6001 to 6100, section `tt_mm`: 40 pulses on port 1 under a leak of 0.1 TΩ, the protocol of the five leak scans of the calibration |
| 2. Trainings without noise | 100 | The same seeds: the stimulus of the test runs (10 pulses on port 1, 10 on port 2, one on both), without noise |

**Preflight check.** The rows of the two preflight runs must be the rows
of `../certification/results/preflight/nom_train.csv` and
`nom_leak.csv`, byte for byte (same SHA-256). This shows that the two
more signals and the call through `uncond_run.py` change nothing. If the
rows differ, the cause is looked for and an amendment is pushed before
any other run. `uncond_analyze.py preflight` writes this check in
`PREFLIGHT.md`. It reads no run of a test cell.

Order: this file and the scripts are pushed; then the preflight and its
check; then stage 1 and stage 2 in slices, each slice pushed when it
ends. `uncond_analyze.py report` is run once, after the last slice is
pushed, and its report is pushed as written.

## Quantities taken from the certification campaign, unchanged

`kappa`, `d0`, `mu`, `h_mu` (`calibration.json`); for each cell its
static level `Ls` and `level0 = Ls + mu`, for each port its start gain
`G0s` and its predicted need `m` (`predictions.csv`); for each port its
count, `a`, `B`, the noise of the threshold in its reads, and the
reasons of its status that do not depend on `ell` (`ports.csv`). The
margins `mz = 0.0002` and `mq = 0.0002`. The definitions of the rest
state, of a FIRE, of the gains `G`, `Y` and `Z` of a read, and of the
peak `Pf` that a gain gives.

`level0` is not moved to the level measured on the cell: `m` and `a`
were pushed before the test runs and stay. The distance between the
measured level and `level0` goes into `ell`.

## Condition 1: the level of each cell

In the leak scan of a cell, as in the calibration: take the first silent
read after the first FIRE, with peak `Ps`, and the read before it, which
has a FIRE, with the peak `Pf = 0.1 + (c - 0.1)*exp(-1/2) + exp(Y + kappa)`
that its gain gives. The firing level of the cell lies between `Ps` and
`Pf`.

```text
mu_cell = (Ps + Pf)/2 - Ls
hw_cell = (Pf - Ps)/2
h1      = |mu_cell - mu| + hw_cell          = max(|Ps - level0|, |Pf - level0|)
```

`h1` is the formula of `h_mu` for one cell: the distance of its midpoint
to `mu`, plus its half-width. It replaces `h_mu` for the two ports of
the cell.

A cell is **not evaluable** if its scan failed, has no silent read after
its first FIRE, if the read before that silent read has no gain (FIRE
earlier than 0.76), or if `Pf < Ps` (the bracket is empty).

**Envelope of the six cells.** The certification campaign assumed that
the firing level of every test cell is within `h_mu` of `Ls + mu`.

- The `mu` of a cell is **inside the envelope** when
  `|mu_cell - mu| <= h_mu`, that is `mu_cell` in
  `[-0.00112, +0.00191]` (the values of `calibration.json`, rounded here).
- The bracket of a cell is **inside the envelope** when `h1 <= h_mu`:
  then the bound used by the certification campaign did cover the level
  measured on that cell.

Both counts are reported.

## Condition 2: a gain measured on the current of the mirror

The scalar model says that the main charge is a capacitor `Cq` = 5 pF
that leaks toward rest with a time constant of 2 units and receives the
output current of the gain mirror during the pulse. If so, the part of
the peak that a read adds is the charge that the mirror delivers,
weighted by the leak:

```text
W  = (1 / (Cq * 0.5 V)) * integral over the pulse, from its start ts to ts + 1 unit,
                          of  Im(t) * exp(-(ts + 1 unit - t) / (2 units))  dt
GI = log(W)
```

`Im` is the drain current of `xmout` of the port. The integral is the
trapezoid sum over the solver points, the two ends interpolated. `GI`
uses no voltage of the main capacitor. After a FIRE the current of the
mirror is steered away from the main capacitor but still flows, so `GI`
exists for a read with a FIRE as for a silent read. This is what the
gain inferred from the peak cannot give: the uncut peak of a read with a
FIRE does not exist.

`GI` is compared with the gain `Z` of the certification campaign (`G`
from the peak of a silent read, `Y + kappa` for a read with a FIRE),
read by read, on the single-port reads of a run without noise:

```text
D        = mean of G - GI over the silent reads of the port in the run
eps_peak = largest |Z - GI - D| over all the reads of the port in the run that have a gain, plus mg
```

`mg = 0.0001` is a margin for the resolution of the integral. One
constant `D` per port and per run is allowed, because a gain is defined
up to a constant factor. Nothing else is fitted: a slope different from
1 between the two gains goes into `eps_peak`. A read with a FIRE earlier
than 0.76 has no gain `Z` and is left out; their number is reported.

- `eps_peak(port)`: from the 10 reads of the port in the training
  without noise of its cell.
- `eps_scan(cell)`: from the 40 reads of port 1 in the leak scan of the
  cell.

If a port has no silent read in its run, or a value is missing or not
positive, `eps_peak` is not evaluable.

**Same cell.** The gain `G` of the first read of port 1 in the training
without noise must be within `mz` of the `G0s` of that port in the
certification campaign. A cell that fails this check is not evaluable
for condition 2. The same difference for port 2, whose first read comes
after ten reads of port 1, is reported.

`eps_peak` is added whatever its size. There is no threshold under which
the measure would be called unreliable and set aside.

### Where the gain enters the budget

```text
a2  = a + eps_peak(port)                      one gain, Z(0)
B2  = B + 2*eps_peak(port)                    a difference of two gains
Pf2 = 0.1 + (c - 0.1)*exp(-1/2) + exp(Y + kappa + eps_scan(cell))
h2  = max(|Ps - level0|, |Pf2 - level0|)      the gain that gives the upper end of the bracket
```

## Two new statuses of a port

```text
ell1  = h1 + noise + mq
room1 = d0/2 - a  - B  - (20/17)*ell1 - 1/8000        level of the cell; gain as in the certification campaign
ell2  = h2 + noise + mq
room2 = d0/2 - a2 - B2 - (20/17)*ell2 - 1/8000        level of the cell and independent gain
```

`noise` is the largest noise of the threshold in the reads 0 to `r` of
the port in its test run, as in the certification campaign.

For each of the two, with its own `ell` and `room`:

| Status | Rule |
|---|---|
| Not evaluable | The port was not evaluable in the certification campaign; or its cell is not evaluable for condition 1; or, for status 2 only, `eps_peak(port)` or `eps_scan(cell)` is not evaluable or the cell fails the same-cell check |
| Outside the certified domain | Evaluable, and one of: a reason of the certification campaign that does not depend on `ell` (rest state outside the band, latch rising twice, steering rule broken); `level0 - ell < 19/20`; `room <= 0`. The reason is given |
| Certified, count confirmed | None of the above, and the count of the test run is the predicted `m` |
| Certified, count contradicted | None of the above, and the count is not the predicted one |

Status 2 is the new status of the port. Status 1 is shown beside it, to
separate the effect of the level from the effect of the gain.
`room2 <= room1` by construction, so a port certified by status 2 is
certified by status 1.

## What is a failure

- **F1.** A port certified by status 1 or by status 2 whose count is
  contradicted.
- **F2.** A cell whose `mu_cell` is outside the envelope of the six
  cells.

A failure is reported as such and investigated. Nothing is adjusted to
remove it. No rule, constant or margin is changed after a result of
stage 1 or 2 is seen. If a rule proves wrong, a new rule is written and
pushed before it is used, and both results are shown.

## What the new status still rests on

Stated here so that the report cannot claim more.

- It is a simulation, with the accuracy of the solver. No chip was built.
- The level of a cell is bracketed once, between two successive reads of
  port 1 in one scan. It is used for the two ports of the cell: they
  share the main capacitor and the comparator.
- `eps_peak` is measured without noise, on the same port and the same
  staircase of gains, and applied to the reads of the noisy test run.
- `kappa`, `d0`, `eps_kappa` and the centre `mu` of the certification
  campaign.
- The count of a port comes from one noisy run, which is not reproduced
  by its seed.

## Predictions

| | Prediction |
|---|---|
| U1 | No run fails, and the 100 leak scans have a silent read after their first FIRE |
| U2 | The `mu` of every one of the 100 cells is inside the envelope of the six cells (no failure F2) |
| U3 | The bracket is inside the envelope for 65 to 95 of the 100 cells |
| U4 | Status 1 certifies 52 to 68 ports |
| U5 | The median `eps_peak` of the 200 ports is between 0.0003 and 0.004 |
| U6 | Status 2 certifies 15 to 58 ports |
| U7 | No certified port has its count contradicted, by status 1 or by status 2 (no failure F1) |

## What this campaign does not do

- It does not change the status of any port of the original campaign or
  of the certification campaign. `mc_2064`, port 1, keeps its historical
  status.
- It does not run a noisy run, and it does not replace a test run.
- It does not build the detection of a pulse, and it does not test the
  read windows of the ideal model.
