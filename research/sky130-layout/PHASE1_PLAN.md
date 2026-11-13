# Proposed plan for phase 1

Phase 0, item 5. **A proposal for the owner. Nothing in it is
registered, and nothing in it has been run.** The predictions below are
candidates: they become predictions only when the owner fixes them in a
`PREDICTION.md` committed before the first post-layout run of the cell.

## The question

One R cell is laid out in SKY130 as it was simulated. Its parasitics are
extracted and added to the simulated cell. **Does the certified
behaviour survive them?**

Three answers are possible and each is a result: it survives; it
survives with a shift that the certification measures and absorbs; it
does not.

## What is known when this is written

Written on 2026-11-13, at the end of phase 0. Known:

- the loop on one inverter, and its extracted netlists
  ([`TOOLCHAIN.md`](TOOLCHAIN.md));
- the footprints of the parts, each drawn alone
  ([`FLOORPLAN.md`](FLOORPLAN.md));
- three probes on single devices ([`RISKS.md`](RISKS.md), F1 and F2);
- the committed results of the circuit study and of its three
  certification campaigns.

**Not known: any extraction of the cell or of one of its blocks, and any
post-layout simulation of the cell.** No layout of the cell exists.

## Decisions for the owner

| | Decision | Proposal |
|---|---|---|
| D1 | Boundary of the layout | Inside: the 232 transistors, the 12 capacitors and the 8 resistors of [`INVENTORY.md`](INVENTORY.md). Outside, as pins: supply, references, bias sinks, discharge references, clocks, pulse currents, the preset, and the inputs where the bench injects noise and the imposed leak |
| D2 | Feedback and sensor capacitors | Unit plates of 0.4 pF, 75 and 1, with dummies. About 64 000 µm² for the cell. The large-plate option is 54 000 µm² and leaves the ratio uncontrolled |
| D3 | Capacitors in the simulated netlist | Ideal values, plus the extracted parasitics. The mismatch sample of each cell is then kept. Capacitor mismatch stays unmodelled, as in the campaigns |
| D4 | Transistors under the capacitors | No. Beside them |
| D5 | Extraction used for the predictions | Capacitance only, with source and drain areas. One nominal run with resistance too, reported apart |
| D6 | Calibration constants of the certification | Recalibrated on the post-layout cell by the registered procedure, on 8 cells instead of 20. The frozen constants of the campaign as a second, declared analysis |
| D7 | Ports | 8 cells fixed now from committed data, see below |

## Step 1. The layout

Bottom-up, in Magic, scripted as the inverter of phase 0 was. Each block
is DRC clean and LVS clean before it is used in the next.

| Order | Block | Matching-sensitive content |
|---|---|---|
| 1 | Logic row: inverter, NAND gates, latch | none |
| 2 | Comparator, in its two sizes | input pair, load mirror, bias mirror |
| 3 | Op-amp, with `rz` and `cc` | input pair, load mirror, bias mirror 1 : 1 : 4 |
| 4 | Gain mirror | the pair 40 / 2.5 |
| 5 | Sensor: `cs`, precharge, discharge mirror, steering | the summing-node side |
| 6 | Capacitor array `cf` + `cs` | 76 unit plates and dummies |
| 7 | Port: blocks 1 to 6 | the summing node, the sensor node |
| 8 | Shared: `cq`, `rleak`, FIRE comparator, protection latch | the node `vq` |
| 9 | Cell: two ports, mirrored, and the shared block | |

Acceptance of the layout, all required:

- Magic DRC, style `drc(full)`: 0 errors.
- KLayout DRC of the GDS, deck of the PDK with front-end, back-end and
  grid rules on: 0 violations. Any waived rule is listed with its
  reason.
- netgen LVS against a netlist of the cell: "Circuits match uniquely"
  **and** no property error.
- The LVS netlist is produced by a script from `cell.spice` and
  `blocks.spice`: the elements of role "cell" of `inventory.py`, nothing
  typed by hand. The script fails if the device list differs from the
  inventory.
- Antenna check of Magic run and reported. Metal density and fill are
  not required of a single cell; said so in the report.

No estimate of the drawing time is given: phase 0 drew two transistors
and four wires, which does not measure it.

## Step 2. From the layout to a netlist that is still the same cell

By finding F2 of [`RISKS.md`](RISKS.md), the extracted netlist cannot be
simulated as it comes. A script, `annotate.py`, builds the **annotated
netlist**:

- every line of `cell.spice` and `blocks.spice`, in its order,
  unchanged but for the next item;
- on each transistor, the `ad`, `as`, `pd`, `ps` that Magic extracted
  for it, summed over its fingers;
- after the devices, the extracted capacitances between the nets of the
  schematic, named by the LVS correspondence.

Node names, instance names and the four noise-source lines stay those
the campaign runners rely on. The runner and the manifest are new files
of this folder: the campaign runners check the hash of `cell.spice` and
are not edited.

**Preflight, before preregistration.** Four checks, none of which shows
a post-layout result:

| | Check | Passes if |
|---|---|---|
| A | The schematic nominal run with this installation | Identical to `../circuit/results/nom.csv`. Done in phase 0 |
| B | The annotated netlist with every parasitic at zero and no area | Rows identical byte for byte to the schematic, on the nominal cell and on seed 6002 without noise |
| C | The new runner and analysis on the schematic, for the cells of step 3, noiseless stages | Rows identical to the committed ones of `../circuit/certification/` and `../circuit/certification-unconditional/` |
| D | Cost: the 2-period ramp on the full annotated netlist | Prints its wall time **and nothing else**. Its output is not read, not saved |

If B fails, the port-by-port question cannot be asked and the plan is
rewritten before any prediction is fixed.

Noise is made reproducible as in the repetition campaign: a noise
identifier per run through the preload of
`../circuit/repetition/fakepid.c`, read and not edited.

## Step 3. The post-layout checks

All runs are simulations of the annotated netlist, typical corner, 27 °C
unless said, same solver options and largest step as the campaigns.

| Check | Runs | What is read |
|---|---|---|
| **Self-stop and silent-pulse count**, nominal | Cell run: 10 pulses per port and a joint pulse, no noise | Silent pulses before the first FIRE of each port (schematic: 4 and 4), step of each silent pulse (schematic: 1.346 to 1.347 mV), step of a firing pulse, relapses, joint read, the guard |
| **Leak refresh**, nominal | Refresh run of 100 pulses under 0.1 TΩ, no noise | Periods between two silent pulses (schematic: 22 or 23), band of the stored voltage |
| **Junction leak**, nominal, 125 °C | Cell run, and a refresh run of 60 pulses with no imposed leak | Whether the cell stops, and whether it refreshes by itself. Tests F1 |
| **Static FIRE level and first gain**, nominal and 8 cells | Ramp and read of each cell, no noise | `Ls`, `G0s`, the gap and the predicted need `m` of each port, against the committed values of the same cell |
| **Need margins on 16 ports** | For each of 8 cells: leak scan, noiseless gain run, one noisy test run | `a`, `B`, `ell`, the room of each port by the registered rules (status 3 of amendment 1, and directional rule A1), the count against `m` |
| **Calibration** | 8 cells of the calibration cohort (seeds 5001 to 5008): noiseless train and ramp; 2 leak runs | `d0`, `kappa`, `mu`, `h_mu` of the post-layout cell |
| **Resistance**, nominal | One cell run on the netlist with resistance extracted | The same readings as the first row, reported apart. Stopped and reported as failed after 30 minutes |
| **Supply current**, nominal | Read on the nominal cell run, at no cost | Standing current and charge drawn per pulse. **Reported, not predicted**: the first energy figure of the cell, for a nominal simulation |

**The 8 cells** are fixed by a rule on committed data, the column
`room3` of
`../circuit/certification-unconditional/ports_amendment1.csv`: the four
cells that hold the status-3 ports with the largest room, and the four
that hold those with the smallest.

| Cell (mismatch seed) | Status-3 port | `room3` | Need `m` |
|---|---|---|---|
| `t6065` (6065) | 1 | 0.00921 | 4 |
| `t6002` (6002) | 1 | 0.00841 | 2 |
| `t6074` (6074) | 1 | 0.00727 | 3 |
| `t6051` (6051) | 2 | 0.00640 | 3 |
| `t6082` (6082) | 2 | 0.00049 | 4 |
| `t6003` (6003) | 1 | 0.00043 | 5 |
| `t6031` (6031) | 1 | 0.00036 | 4 |
| `t6030` (6030) | 1 | 0.00030 | 3 |

Both ports of each cell are measured: 16 ports, of which these 8 are
certified at status 3 in the campaign.

## Step 4. Candidate predictions

Candidates, written before any extraction of the cell is seen. The
numbers are the author's reasoning from [`RISKS.md`](RISKS.md), not
measurements. The owner fixes, changes or drops each one before
preregistration.

One piece of reasoning runs through them. **The layout is the same for
every cell.** Its parasitics shift every cell by the same amount; the
cells differ by their mismatch only. So the shift measured on the
nominal cell should be the shift of every cell, and a port whose margin
is thinner than the shift should change its need.

| | Candidate prediction | Schematic value | Reasoning |
|---|---|---|---|
| L1 | The nominal cell stops by itself: on each port, silent pulses, then a FIRE on every later pulse of its series, no relapse | holds | The mechanism does not depend on a capacitance value |
| L2 | The nominal count of silent pulses is 3, 4 or 5 on each port, the same on both | 4 and 4 | The start gap is 3.6 doses. A shift of 0.4 dose makes it 5 |
| L3 | A silent pulse writes between 1.33 and 1.42 mV | 1.346 to 1.347 mV | Parasitic on the sensor node adds to 400 fF: 0 to 20 fF |
| L4 | A firing pulse moves the stored voltage by at most 0.005 mV | at most 0.001 mV | Coupling to the summing node gives its charge back within the period |
| L5 | The guard reports nothing on any run | nothing | |
| L6 | Under 0.1 TΩ the nominal cell falls silent once every 20 to 25 periods, never twice in a row | every 22 or 23 | The junction leak at 27 °C is far below 4 pA |
| L7 | **Threshold.** The static FIRE level `Ls` of each cell moves by less than 0.002 level unit, 1 mV on the main capacitor | per cell, committed | A parasitic changes a delay, not a comparator threshold |
| L8 | **Common shift.** The gap of the nominal cell moves by between −0.005 and +0.030 in log-gain. The gap of each of the 16 ports moves by the nominal shift within ±0.004 | per port, committed | Parasitic on `vq` raises the gain needed to fire, by 1% per 50 fF |
| L9 | The predicted need of each of the 16 ports changes by 0 or +1 | per port, committed | Follows from L8: a shift below one dose, upward |
| L10 | **Count.** The observed count equals the post-layout predicted need on at least 13 of the 16 ports | 189 of 200 in the campaign | Same rate as the campaign |
| L11 | **Soundness.** No port certified post-layout, by status 3 or by rule A1, has a count different from its post-layout predicted need | 0 contradicted in 59, 37 and 57 | The rule certifies from margins measured on the run itself |
| L12 | **Survival.** Of the 4 status-3 ports with the largest room, at least 3 are certified again at status 3. No prediction for the 4 with the smallest room: their room, 0.0003 to 0.0005, is below the shift expected in L8 | all 8 certified at status 3 | A large room survives a common shift only if the port stays near the centre of its dose interval. This is the weakest candidate |
| L13 | At 125 °C with no imposed leak, the nominal cell stops and then refreshes by itself: a silent pulse every 4 to 15 periods | no silent pulse after the stop in the campaign run | F1: about 13 pA on the summing node, 14% of a dose per period, by arithmetic on one device |

**What would count against the layout bet:** L1, L5 or L11 failing. A
cell that no longer stops, a guard event, or a certified port with a
wrong count.

**What would be a shift and not a failure:** L2, L3, L8, L9 or L12
outside their range while L11 holds. The cell behaves as a cell of
another need, and the certification says so.

"Certified ports stay certified" is deliberately not a candidate as it
stands. With a common shift of a fraction of a dose, a port certified on
the schematic may sit near the edge of its dose interval after layout.
The rule should then refuse it, and that refusal would be the rule
working. L11 and L12 separate the two cases.

## Step 5. Compute time

Seconds per run are the medians recorded in the metadata of the
committed campaigns, four runs at a time: ramp 22 s, read 27 s, leak
scan 236 s, noiseless train 125 s, noisy train 190 s, calibration train
142 s. This machine ran the nominal noiseless train in 91 s and 95 s.

**The unknown is the slowdown `f` of the annotated netlist.** Phase 0
does not measure it: there is no cell netlist to time. Capacitance-only
annotation adds capacitors and no node, so `f` is expected between 1 and
3. That is an assumption. Preflight D measures `f` before anything is
registered.

| Part | Schematic seconds | Scales with `f`? |
|---|---|---|
| Preflight A, B | 500 | no |
| Preflight C: 4 noiseless stages on 8 cells | 3 280 | no |
| Preflight D | 22 | yes |
| Nominal block: train, ramp, read, leak scan, refresh of 100 pulses, train and refresh of 60 pulses at 125 °C | 1 456 | yes |
| Calibration: 8 trains, 8 ramps, 2 leak runs | 1 842 | yes |
| 8 cells × (ramp, read, leak scan, gain train, noisy test train) | 4 800 | yes |
| Nominal run with resistance | at most 1 800 s on one core | capped |

Wall time on four cores, in hours, everything included:

| Scope | `f` = 1 | 2 | 3 | 4 | 6 | 10 | 16 | 20 |
|---|---|---|---|---|---|---|---|---|
| **Full**: 8 cells, calibration on 8 | 0.95 | 1.5 | 2.1 | 2.6 | **3.8** | 6.0 | | |
| **Reduced**: 4 cells (`t6065`, `t6002`, `t6031`, `t6030`), calibration on 4 | 0.6 | 0.9 | 1.3 | 1.6 | 2.3 | **3.6** | 5.6 | |
| **Minimal**: 2 cells (`t6065`, `t6030`), frozen constants, no calibration | 0.4 | 0.6 | 0.8 | 1.0 | 1.3 | 2.1 | 3.2 | **3.9** |

**Scope rule, fixed before preregistration from preflight D alone:**

| Measured `f` | Scope |
|---|---|
| at most 6 | Full |
| above 6, at most 10 | Reduced |
| above 10, at most 20 | Minimal. L8, L10 and L12 are then judged on 4 ports and say little |
| above 20 | No campaign. The extraction is reconsidered and the plan rewritten |

The campaign stays under 4 hours in every row. The drawing of the layout
is not in this budget.

## Step 6. Order of the commits

Following the practice of the certification campaigns:

1. The layout scripts, with DRC and LVS results and hashes. Review.
2. `annotate.py`, the new runner and analysis, the manifest with the
   hashes of every input, and the results of preflight A to D.
3. `PREDICTION.md`, with the scope given by preflight D, the predictions
   the owner fixed, and what would count against them. **Committed and
   pushed before the first post-layout run of the cell.**
4. The runs, in slices, each pushed as it ends. A failed run stays
   failed. An interruption is written down.
5. The report, written once by the analysis, after the last run. A
   failed prediction stays in it with its verdict.

Any deviation is declared in an amendment before the run it concerns.

## What phase 1 will not say

- Nothing about silicon. Every result is a simulation with extracted
  parasitics, and the extraction is rule-based.
- Nothing about matching in the layout ([`RISKS.md`](RISKS.md),
  section 1).
- Nothing about the pulse detector, the references, the bias generator
  or the preset: they stay ideal, outside the boundary.
- Nothing about substrate coupling or supply bounce.
- Nothing about capacitor mismatch, under decision D3.
- Nothing about density beyond the area of this one cell.
- One layout. Another floorplan gives other parasitics.
