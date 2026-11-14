# Layout of one R cell: predictions of phase 1

Written on 2026-11-13, after the owner approved phase 0 and accepted
decisions D1 to D7 of [`PHASE1_PLAN.md`](PHASE1_PLAN.md) as proposed.

**When this file is committed:**

- no layout exists of the cell or of any of its blocks, other than the
  inverter of phase 0;
- no extraction of the cell or of a block has been made or seen;
- no run of the two stages below has been made, with or without
  areas, at any temperature.

**No run of these stages starts before the owner says so.** This file is
not edited afterwards. A deviation is declared in an amendment committed
before the run it concerns.

These are simulations. No chip is built. A prediction here is a
prediction about a simulation.

## What is known

- Phase 0: the loop on one inverter, the footprints of the parts drawn
  alone, and three probes on single devices
  ([`TOOLCHAIN.md`](TOOLCHAIN.md), [`FLOORPLAN.md`](FLOORPLAN.md),
  [`RISKS.md`](RISKS.md)).
- The committed results of the circuit study and of its certification
  campaigns. The reference values quoted below are read from them.
- The arithmetic of [`RISKS.md`](RISKS.md): about 13 pA of junction
  current on the summing node at 125 °C, from one device; 1% more
  capacitance on the main capacitor node is 0.010 in log-gain.

The predictions are not blind to these. They are blind to any
simulation of the cell with areas or parasitics.

## Two stages

| Stage | Netlist | Needs a layout? | Question |
|---|---|---|---|
| **J**, junction areas | The schematic, with source and drain areas on every transistor. No wire | No | What do the junction areas alone do to the full cell, at 27 °C and at 125 °C? |
| **P**, post-layout | The schematic, with the areas and the wire capacitances extracted from the layout of the cell | Yes | Does the certified behaviour survive the parasitics? |

Stage J answers the owner's request to quantify the junction-area effect
on the full cell at 27 °C and at the hottest corner the campaigns used.
That corner is the typical corner at 125 °C, run `pvt_tt_125` of the
circuit campaign.

Both stages use the same construction of the netlist, which keeps the
mismatch sample of a seed ([`RISKS.md`](RISKS.md), finding F2):

- every device line of `../circuit/cell.spice` and
  `../circuit/blocks.spice`, in its order, with its name, width and
  length unchanged;
- on each transistor line, `ad`, `as`, `pd`, `ps`;
- in stage P only, the extracted capacitances between the nets of the
  schematic, after the devices;
- capacitors and resistors of the cell keep their ideal values
  (decision D3).

Same simulator, device models, solver options and largest step as the
campaigns: ngspice 42, `sky130_fd_pr` at `1232782c…`, the options of
`cell.spice`, 200 ns.

**Before any run of a stage**, three things are committed: the script
that builds the netlist, a manifest with the sha256 of every input and
the ordered list of runs, and the result of the identity test: with all
areas and capacitances at zero, the constructed netlist gives rows
identical byte for byte to the schematic, on the nominal cell and on
seed 6002 without noise. If the identity test fails, no stage starts and
the plan is rewritten.

## Stage J: junction areas on the full cell

**Areas.** For each transistor, the `ad`, `as`, `pd`, `ps` that Magic
extracts from that device drawn alone by the device generator of the
PDK, with the finger choice of
[`footprints/footprints.tcl`](footprints/footprints.tcl). The table of
areas is committed with its hash before the first run. These are not the
areas of a layout of the cell: shared diffusions would be smaller.

**Runs.** Nominal cell, typical corner, no noise, no mismatch.

| Run | Kind | Temperature | Areas | Imposed leak | Reference |
|---|---|---|---|---|---|
| J1 | cell run, 22 periods | 27 °C | yes | none | `../circuit/results/nom.csv` |
| J2 | cell run, 22 periods | 125 °C | yes | none | `../circuit/results/pvt_tt_125.csv` |
| J3 | refresh, 60 pulses | 27 °C | yes | none | first 60 pulses of `refresh_none.csv` |
| J4 | refresh, 100 pulses | 27 °C | yes | 0.1 TΩ | first 100 pulses of `refresh_lk11.csv` |
| J5 | refresh, 60 pulses | 125 °C | yes | none | run J6 |
| J6 | refresh, 60 pulses | 125 °C | **no** | none | control: the schematic, which the campaigns did not run at 125 °C |

**Measures.** Those of `../circuit/run.py`, with its definitions
(`../circuit/DESIGN.md`, "Measures"): FIRE, latency, stored voltage,
step. A step is positive toward a higher gain. The drift of a port at
rest is the mean step of port 2 over the ten periods in which port 1 is
pulsed.

**Predictions.**

| | Prediction | Reference value |
|---|---|---|
| JA | J1: each port is silent for 4 pulses, then fires on the 6 that follow. The joint pulse fires | 4 and 4 |
| JB | J1: every silent step is between 1.346 and 1.356 mV | 1.346 to 1.347 mV |
| JC | J1: every step of a firing pulse, and every step of a port at rest, is at most 0.002 mV in size | at most 0.001 mV |
| JD | J1: FIRE latency of a single port between 0.905 and 0.925; of the joint pulse between 0.265 and 0.272 | 0.9115 to 0.912; 0.2675 |
| JE | J3: no silent pulse after the stop | none in 150 pulses |
| JF | J4: after the stop, a silent pulse once every 22 to 24 periods, never twice in a row | every 23 periods in its first 100 pulses |
| JG | J2: a port at rest drifts toward a lower gain by 0.12 to 0.28 mV per period | 0.001 mV at most |
| JH | J2: port 1 is silent for 8 or 9 pulses before its first FIRE | 7 |
| JI | J2: port 2 is silent for 9 or 10 pulses. Ten means that it does not fire in its series | 7 |
| JJ | J2: the joint pulse fires | fires at 0.2705 |
| JK | J5: after its stop the port falls silent again once every 5 to 11 periods, never twice in a row | not run in the campaigns |
| JL | J6: no silent pulse after the stop | not run in the campaigns |
| JM | The guard of `../circuit/analyze.py` reports nothing on any of the six runs | nothing |

Reasoning, so that a failure can be read:

- JA to JF say that at 27 °C the areas change almost nothing: a
  junction capacitance of about 1 fF on the 400 fF sensor node, and a
  junction current below the default the campaigns carried.
- JG to JK carry the arithmetic of phase 0 to the cell: 13 pA on a
  30 pF capacitor is 0.19 mV per period, 0.14 dose. A port then needs
  more pulses to reach its first FIRE, loses its gain while the other
  port is trained, and refreshes by itself about every 7 periods.
- If JG to JK fail and JA to JF hold, the arithmetic on one device does
  not carry to the cell, and [`RISKS.md`](RISKS.md) overstated F1.
- If JA to JF fail, the areas matter at 27 °C, and the question reaches
  the schematic campaigns themselves.

## Stage P: post-layout

**Layout and extraction.** As in steps 1 and 2 of
[`PHASE1_PLAN.md`](PHASE1_PLAN.md), with decisions D1 to D5: the 232
transistors, 12 capacitors and 8 resistors inside; unit plates for the
feedback and sensor capacitors; transistors beside the capacitors;
capacitance-only extraction with areas for the predictions.

**Cells.** The 8 cells fixed in [`PHASE1_PLAN.md`](PHASE1_PLAN.md) by
the column `room3` of
`../circuit/certification-unconditional/ports_amendment1.csv`: `t6065`,
`t6002`, `t6074`, `t6051` (largest room at status 3) and `t6082`,
`t6003`, `t6031`, `t6030` (smallest). Both ports of each: 16 ports, of
which 8 are certified at status 3 in the campaign.

**Runs.** Those of step 3 of [`PHASE1_PLAN.md`](PHASE1_PLAN.md):

- nominal: cell run, ramp, read, leak scan, refresh of 100 pulses under
  0.1 TΩ, at 27 °C; cell run and refresh of 60 pulses with no imposed
  leak at 125 °C;
- calibration on 8 cells (seeds 5001 to 5008): noiseless train and ramp
  of each, leak scan of the first two;
- for each of the 8 cells: ramp, read, leak scan, noiseless gain run,
  one noisy test run;
- one nominal cell run with resistance extracted, stopped and reported
  as failed after 30 minutes, reported apart;
- the supply current of the nominal cell run, reported and not
  predicted.

Noise is made reproducible by a noise identifier per run, with the
preload of `../circuit/repetition/fakepid.c`.

**Rules.** The quantities `Ls`, `G0s`, gap, `m`, `a`, `B`, `ell`,
`eps3` and the rooms are those of
`../circuit/certification/PREDICTION.md` and of amendment 1 of
`../circuit/certification-unconditional/`. The directional rule is A1 of
`../reusable-controller/physical/ASYMMETRIC_PROTOCOL.md`. They are
applied unchanged. The constants `d0`, `kappa`, `mu`, `h_mu` are those
of the calibration of this stage (decision D6). A second analysis with
the constants of `../circuit/certification/CALIBRATION.md` is reported
and decides no prediction.

"Schematic" below means the committed value of the same cell and port.
"Post-layout need" is the need predicted from the ramp and the read of
the post-layout cell.

**Predictions.** The candidates L1 to L13 of
[`PHASE1_PLAN.md`](PHASE1_PLAN.md), unchanged.

| | Prediction | Schematic |
|---|---|---|
| L1 | The nominal cell stops by itself: on each port, silent pulses, then a FIRE on every later pulse of its series, no relapse | holds |
| L2 | The nominal count of silent pulses is 3, 4 or 5 on each port, the same on both | 4 and 4 |
| L3 | A silent pulse of the nominal cell writes between 1.33 and 1.42 mV | 1.346 to 1.347 mV |
| L4 | A firing pulse of the nominal cell moves the stored voltage by at most 0.005 mV | at most 0.001 mV |
| L5 | The guard reports nothing on any run | nothing |
| L6 | Under 0.1 TΩ the nominal cell falls silent once every 20 to 25 periods, never twice in a row | every 22 or 23 |
| L7 | The static FIRE level `Ls` of the nominal cell and of each of the 8 cells moves by less than 0.002 level unit | per cell |
| L8 | The gap of the nominal cell moves by between −0.005 and +0.030 in log-gain. The gap of each of the 16 ports moves by the nominal shift within ±0.004 | per port |
| L9 | The need of each of the 16 ports changes by 0 or +1 | per port |
| L10 | The observed count equals the post-layout need on at least 13 of the 16 ports | 189 of 200 in the campaign |
| L11 | No port certified post-layout, at status 3 or by rule A1, has a count different from its post-layout need | 0 contradicted |
| L12 | Of the 4 status-3 ports with the largest room (`t6065` port 1, `t6002` port 1, `t6074` port 1, `t6051` port 2), at least 3 are certified again at status 3. No prediction for the 4 with the smallest room | all 8 certified |
| L13 | At 125 °C with no imposed leak, the nominal cell stops and then falls silent again once every 4 to 15 periods | no silent pulse after the stop |

In reduced or minimal scope (below), "16 ports" becomes 8 or 4, "at
least 13" in L10 becomes at least 6 of 8 or 3 of 4, and L12 is judged on
the cells that remain: at least 1 of `t6065` port 1 and `t6002` port 1
in reduced scope, `t6065` port 1 in minimal scope.

**What counts against the layout bet:** L1, L5 or L11 failing. A cell
that no longer stops, a guard event, or a certified port with a wrong
count.

**What is a shift and not a failure:** L2, L3, L8, L9 or L12 outside
their range while L11 holds. The layout is the same for every cell, so
its parasitics should shift every cell by the same amount; a port
certified on the schematic may then sit at the edge of its dose
interval, and the rule should refuse it.

## Reduced statistical power

Phase 1 uses 8 cells where the campaigns used 20 and 100. This is
stated here so that no result of phase 1 is read as more than it is.

**Calibration on 8 cells instead of 20** (decision D6).

- `d0` and `kappa` are means over the silent reads of the cohort. With
  8 cells of 20 there are about 2.5 times fewer reads. If the reads were
  independent, the standard error of each mean would be about 1.6 times
  that of the campaign. Reads of one cell are not independent, so 1.6 is
  a floor.
- `h_mu` is a worst case over leak scans: 3 scans here (the nominal
  cell and 2 cells), 6 in the campaign. A worst case over fewer cells is
  smaller. The campaign already said that its `h_mu` was "the worst case
  on six cells, not a bound established for each test cell"; here it is
  the worst case on three.
- A constant that is off moves the rooms of every port together. This
  is why the frozen constants of the campaign are reported as a second
  analysis.

**16 ports instead of 200, and one noisy run per cell.**

- L11 can fail on one port, and one failure is enough to count against
  the bet. **It cannot establish a rate.** With no contradiction among
  `n` certified ports, the 95% upper bound on the rate of contradiction
  is `1 − 0.05^(1/n)`: 53% for 4 ports, 31% for 8, 17% for 16. The
  repetition campaign reached 0.26% with 1 140 trials.
- L10 and L12 are counts on 16 and on 4 ports. A difference of one port
  changes their verdict.
- The 8 cells are not a sample: they were chosen by their room. Nothing
  measured on them is a rate over cells.
- Stage J and the nominal runs of stage P are single runs without
  noise. They are reproducible and carry no interval.

Phase 1 can show that the certified behaviour fails after layout. If it
does not fail, phase 1 shows that it held on these cells, with this
layout and this extraction, and no more.

## Scope and compute time

Seconds per run are the medians recorded in the committed campaigns.
`f` is the slowdown of the stage-P netlist against the schematic. It is
measured before stage P by the 2-period ramp, which prints its wall time
and nothing else; its output is not read.

| Measured `f` | Scope of stage P | Wall time at the upper `f`, four cores, stage J and preflight included |
|---|---|---|
| at most 6 | Full: 8 cells, calibration on 8 | 3.9 h |
| above 6, at most 10 | Reduced: `t6065`, `t6002`, `t6031`, `t6030`; calibration on 4 cells and 1 leak scan | 3.7 h |
| above 10, at most 18 | Minimal: `t6065`, `t6030`; constants of the campaign, no calibration | 3.7 h |
| above 18 | No stage P. The extraction is reconsidered and the plan rewritten |

Stage J alone is 328 simulated periods, about 1 900 s of one core at the
recorded speed.

The campaign stays under 4 hours. The drawing of the layout is not in
this budget.

## Reporting

- The runs go in slices, each pushed as it ends. A failed run stays
  failed. An interruption is written down.
- The report is written once, by the analysis, after the last run of a
  stage. Stage J may be reported before stage P starts.
- A failed prediction stays in the report with its verdict.
- Every figure is called a simulation, and nominal where it is.
