# Network of R cells: predictions

Written and pushed alone, before any implementation of the campaign: no
runner, no manifest, no analysis exists when this file is committed. Nothing
in it may be changed afterwards; a wrong rule is corrected by an amendment
file pushed before the run or the computation it concerns.

Everything here is a transistor-level simulation (ngspice 42, SKY130
models) of two R cells of [`../circuit/cell.spice`](../circuit/cell.spice),
with the junction areas of stage J of the layout study, joined by an ideal
router outside the simulator. There is no layout of a network, no wire
between the cells and no silicon.

## What is tested

A two-cell network learns: each of its four ports takes doses until it
fires, and then stops. The network theorem, instantiated for this cell
([`../network-circuit/phase1/MODEL.md`](../network-circuit/phase1/MODEL.md)),
says what state the network ends in when every read has room for its error:
`circuit_dated_predicted` of
[`DatedOrder.lean`](../network-circuit/phase1/DatedOrder.lean). The model
takes four numbers per port, measured on each cell alone.

This campaign asks whether, on cells with mismatch that no one has looked
at, **the learned state of the network is the one computed beforehand from
those per-cell measures**.

The primary claim is deterministic: network runs without noise, one
discrepancy refutes it. Runs with noise are made and reported; nothing is
claimed about them.

## Decisions of the owner that this file applies

1. The primary claim is deterministic: six new instances; the constants of
   each cell are measured; the learned state is predicted from them; one
   network run without noise per instance; the claim covers the instances
   with full room under the noise-free budget; one discrepancy refutes it.
2. Noisy runs are run and reported, with `K = 3` and the corrected budget
   of [`NOISE.md`](../network-circuit/phase1/NOISE.md). The per-port
   predictions under noise are a declared comparison, not a claim.
3. The noise model is unchanged. It overstates the low-frequency noise of
   the integrator amplifier ([`../circuit/DESIGN.md`](../circuit/DESIGN.md),
   "Noise"; measured in `NOISE.md`). **A claim under noise is deferred to a
   separate study with an independent noise model.**
4. The 8-unit calendar is kept as a negative control, on one instance with
   full room; its prediction is that the predictor that ignores the help of
   a recent pulse fails on at least one port.
5. No development instance is reused. If no instance has full room the
   primary claim is "not established", with no extra draw.
6. Two machines, at most 4 h of compute in all.
7. The argument about instances with a read without room
   (`MODEL.md`, section 6) is kept out of every claim.

## What was run before this file

- Phase 0: one nominal cell alone (no mismatch), and the nominal network
  without noise on two calendars with pulses 8 units apart
  ([`../network-circuit/README.md`](../network-circuit/README.md)).
- Phase 1: three development instances (mismatch seeds 7101, 7102, 7103),
  each port alone, never a network.
- Four noisy network runs of the 18-unit calendar on the nominal cell
  (`NOISE.md`, section 6).

No network was ever run on a cell with mismatch. No network run without
noise was made on the 18-unit calendar. Nothing was simulated with the
seeds below.

## Definitions

**Time unit.** 20 us, the length of a pulse.

**Instance.** One deck with two cells, `a` and `b`: `net.deck` of
`../network-circuit/net.py` with the model section `tt_mm`, 27 C, the
junction areas of stage J, and the simulator command `setseed` with the seed
of the instance before the deck is read, which fixes its mismatch sample.
Six instances: seeds **7201, 7202, 7203** (measured on machine `a`) and
**7204, 7205, 7206** (machine `b`).

**Ports.** `a1`: port 1 of cell `a`, the sources of A. `a2`: port 2 of cell
`a`, the return wire. `b1`: port 1 of cell `b`, the forward wire. `b2`: port
2 of cell `b`, the sources of B.

**Stored voltage `u`** of a port: stored node minus summing node, in mV. A
more negative `u` is a higher gain.

**Word** of a port in a run: one letter per pulse delivered to the port, in
the order of the dates. `s`: no FIRE of the cell from the start of the pulse
to one unit and 2 us later, and exactly one write on that port during the
cycle of the pulse. `F`: one FIRE in that window and no write. Any other
pulse (refused by the router, not delivered, arriving while the cell is
protected, a FIRE with a write, neither a FIRE nor a write) gets its own
letter and is neither `s` nor `F`. FIRE: the protection latch of the cell
rises through 0.9 V. Write: the write signal of the port rises through
0.9 V.

**Learned state** of a run: the four words. The writes of a port are its
number of `s`.

### Measures, each cell alone

Per instance, with the scripts of `../network-circuit/phase1` as they are
when the implementation is frozen, every run pulsing one port at a time
with all the others idle:

1. **Scan** of each port (`cellscan.py`, no noise): training reads 22 units
   apart, one read 16 units after a FIRE, bisection of the threshold. Four
   runs.
2. **Train without noise** (`noisechar.py quiet`, 10 reads per port 18
   units apart). One run.
3. **Trains with noise** (`noisechar.py noise`, 10 reads per port), each in
   its own simulator process. Three runs.

`constants.py` gives per port: the gap from its preset to its threshold, its
dose, the half bracket of the threshold, the help at 16 units and at 18
units after a silence and after a FIRE; and, from the noisy trains, the
noise within a run per port and the noise between runs per instance.

An instance is **measured** when its eight runs are complete and
`constants.py` yields the noise-free constants of its four ports. Otherwise
it is **not measured**: it has no prediction, gets no network run, and
enters no claim.

### The model and the two budgets

The model is `circuit` of
[`CircuitNetwork.lean`](../network-circuit/phase1/CircuitNetwork.lean) and
its mirror `model.py`: integers, one dose of a port is 100 000 units, the
gap of a port is `round(gap / dose x 100 000)`. The **zero-error words** are
those of the queue run of the model on `calendar 8 10 8 10`.

**Noise-free budget**, per port, in mV:

    hi = + max(0, help at 16, help at 18 after a silence, help at 18 after a FIRE) + 0.030 + half bracket
    lo = - (0.015 + 0.030 + half bracket)

0.015 mV is what a pulse 22 units earlier adds over a long silence (phase
0). 0.030 mV is an allowance for the simulator itself: without noise the
latency of the same read repeats within 0.003 from one run to another,
which is 0.02 to 0.03 mV (phase 1). It is added here to the noise-free
budget of `NOISE.md`.

**Noisy budget, `K = 3`**, per port, in mV, as in `NOISE.md`:

    noise = sqrt(within a run^2 + between runs^2 + need x dose noise^2)
    hi = + max(0, the three helps) + 3 x noise + half bracket
    lo = - (0.015 + 3 x noise + half bracket)

Budgets become integers by rounding away from zero.

**Full room.** An instance has full room under a budget when every read of
the zero-error run has room for the budget of its port (`PortMargins`): a
silent read stays silent under `hi`, a FIRE stays a FIRE under `lo`. An
instance is **eligible** when it is measured and has full room under the
noise-free budget.

### Calendars

`calendars.reciprocal(18)` of `../network-circuit/phase1`: A has 18 sources
at 0, 18, ..., 306; B has 8 sources at 2, 20, ..., 128 and 10 at 326, 344,
..., 488; a FIRE of cell `a` dated in [144, 324) sends one pulse to `b1`
7/20 of a unit later; a FIRE of cell `b` dated in [326, 506) sends one
pulse to `a2` 7/20 later; horizon 500. The router refuses and records any
pulse that would start less than 16 units after the previous pulse of its
cell, or while its cell is protected (`guard=16`).

`calendars.reciprocal(8)`: the same with a spacing of 8 units (A at 0, 8,
..., 136; B at 2, ..., 58 and 146, ..., 218; gates [64, 144) and
[146, 226); horizon 230), without guard.

## Order of the campaign

1. **Measures.** Each machine measures its three instances.
2. **Predictions.** From the collected measures of both machines, the frozen
   scripts write one file, `PREDICTED.json`: per instance, whether it is
   measured, its constants, both budgets, whether it is eligible, the
   zero-error words, the per-port verdicts at `K = 3`, the control instance
   and the list of network runs. The same margins are written as a Lean file
   and checked by the Lean kernel. **`PREDICTED.json` is committed and
   pushed before any network run**, and the launcher of the network runs is
   bound to its SHA-256.
3. **Network runs**, on the machine that measured the instance:
   - `quiet`: one run of the 18-unit calendar without noise, for every
     measured instance;
   - `control`: one run of the 8-unit calendar without noise, on the control
     instance;
   - `noisy`: two runs of the 18-unit calendar with noise, for every
     measured instance.
   On each machine the `quiet` runs come first, then the control, then the
   noisy runs.
4. **One analysis**, after both machines have ended.

If the Lean check of step 2 fails, no network run is launched and the
campaign ends there, reported as it is.

**Control instance.** Among the eligible instances, the one whose smallest
margin of a last silence, over its four ports, is the smallest; the lowest
seed in case of a tie. The margin of the last silence of a port is its gap
minus (its need minus one) doses.

## Predictions

**Primary claim: the learned state without noise.**

- **D1.** For every eligible instance, the four words of its `quiet` run
  are the zero-error words written in `PREDICTED.json`.
- **D2.** In those runs the hypotheses hold as built: the guard refuses no
  pulse; two pulses on one cell are never less than 16 units apart; no
  pulse is left in the queue at the horizon; every `s` moves the stored
  voltage of its port by its measured dose within 0.01 mV; and no stored
  voltage moves by more than 0.01 mV during a pulse of another port or of
  a FIRE.

D1 is refuted by one port of one eligible instance whose word differs.
There is no noise to appeal to, and a run without noise can be made again
by anyone: it gives the same waveform.

If D2 fails in a run, D1 is still evaluated on it and the failure of D2 is
reported: the run left the conditions under which the prediction was made.

**Negative control: the 8-unit calendar.**

- **C1.** In the `control` run, the word of at least one port differs from
  its zero-error word. The predictor that ignores the help of a recent
  pulse is wrong at this spacing.

The report says which ports differ and how (one dose fewer, a pulse on a
protected cell, another word). If C1 fails, the control showed nothing on
that instance; it does not touch D1.

**Declared comparisons, not claims.** Reported as counts, with no "holds"
or "fails":

- **N1.** For each noisy run and port, the word against the verdict of
  `PREDICTED.json` at `K = 3`: for an instance with full room under the
  noisy budget, the four words against the zero-error words; for the other
  instances, the per-port verdicts of `predict.py` ("predicted", "learned
  state predicted", "no prediction"), which rest on an argument that is not
  a Lean theorem.
- **N2.** The `quiet` run of each measured instance that is not eligible,
  against its zero-error words and the same per-port verdicts under the
  noise-free budget.
- **N3.** The run offsets and the scatter of the FIRE latency in the noisy
  network runs, against the noise measured on the trains.

## Rules of the analysis

1. **One analysis, at the end.** The analysis script is frozen with the
   implementation. It is run once, on the evidence of the two machines,
   after both have ended their network runs. No word of a network run is
   looked at while a machine is running.
2. **Which runs count.** A run counts when the launcher recorded it
   `complete` and its own record says that it reached its last date. A run
   that failed, reached its time limit or was lost at a restart is a
   **missing run**: listed with its status, neither a success nor a
   failure, never replaced and never run again.
3. **Missing measures.** An instance with a missing measure run is not
   measured.
4. **Missing network runs.** D1 and D2 are evaluated on the eligible
   instances whose `quiet` run counts; an eligible instance whose `quiet`
   run is missing is listed as not tested. D1 needs at least one tested
   eligible instance; with none it is **not established**, not held and not
   failed. C1 needs its run; without it, or without an eligible instance, it
   is not established.
5. **No re-scoping.** The eligible instances and the control instance are
   those of `PREDICTED.json`, fixed before the network runs. Nothing is
   re-scoped after the data are seen.
6. **Shared noise.** Before N1 and N3, the fingerprints of the noisy runs of
   one instance are compared. Of several runs with the same fingerprint the
   first in the order of the manifests is kept; the others are listed as
   duplicates. A noisy train that is a duplicate is noticed only at the
   analysis; the constants are not recomputed.
7. **Failures are reported as they are.** A failed prediction is written
   "fails" with its words. Nothing is adjusted, removed or explained away.

## Execution

- **Executor.** A Claude Code cloud session on behalf of the owner, on two
  cloud containers whose inventories are recorded.
- **Launcher.** The second launch kit,
  [`../sky130-supervisor-closure/launchkit/launch.py`](../sky130-supervisor-closure/launchkit/launch.py),
  unchanged, used twice. First for the measures, with this file as its
  protocol. Then for the network runs, with `PREDICTED.json` as its
  protocol: the launcher refuses to start if that file is not published, or
  differs from its committed version. Each launch has its manifest, with
  every runner, deck source and analysis file frozen by hash, and its
  attempt marker pushed before the launch with the CI state of the exact
  head. One launch per machine and per stage; a claimed machine is never
  launched again for that stage.
- **Environment, identical on both machines and checked by the launcher:**
  ngspice 42 (SHA-256 `820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45`),
  PDK commit `1232782c1b9fab3aacda74d67ce7c92bf7da8105`, Python 3.12.3
  (`e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f`),
  numpy 2.3.5 (`064003bdb6f9f7bb06e46e07cc3398cbfdc3c114dfe55b89d239e564917be2fb`).
- **Budget.** Four runs at a time on each machine.

  | Run | Measured in phase 1, s | Time limit, s | Per machine |
  |---|---|---|---|
  | scan of one port | 198 to 296 | 375 | 12 |
  | train of 10 reads, no noise | not measured; with noise 545 to 556 | 700 | 3 |
  | train of 10 reads, noise | 545 to 556 | 700 | 9 |
  | network run, 18 units, noise | 678 to 686 (nominal cell) | 860 | 6 |
  | network run, 18 units, no noise | not measured | 860 | 3 |
  | control run, 8 units, no noise | not measured | 860 | 1, on one machine |

  The bound of the launcher is, per machine and stage, the sum of (limit +
  10 s) divided by four, plus the largest (limit + 10 s): 3 995 s for the
  measures of a machine, at most 3 045 s for its network runs. For the two
  machines and the two stages: at most 13 862.5 s, under the 14 400 s (4 h)
  allowed. A run that reaches its limit is a missing run.
- **Resume.** If a container restarts, its runs that had never started
  proceed; a run that had started and not ended is recorded lost and is
  never run again. Nothing else allows a resume.
- **Noise cannot be replayed.** ngspice seeds its noise from the number of
  its process. The noisy runs of an instance differ by that number only;
  each records the fingerprint of the noise it drew. A run without noise
  gives the same waveform when made again.
- **Evidence.** Each run writes its deck, the log of the simulator session,
  its waveform with the vectors the analysis needs, its record and its
  fingerprint. Every surviving file is collected byte for byte with its
  SHA-256. Decks, logs, records, fingerprints and the SHA-256 list are
  committed to this repository; the waveforms are committed unchanged to
  the private repository `HevisNico/kernel-R-circuit`, with their SHA-256 in
  the public list. The report is generated by the analysis script and
  committed as generated.

## What this campaign cannot show

- Nothing about silicon, a layout, wires between cells or a real router:
  the cells are transistors, the router is ideal, and each pulse is the
  canonical pulse whatever caused it.
- Nothing about noise. The noisy runs are reported under a noise model that
  overstates the low-frequency noise of the integrator amplifier; a claim
  under noise is deferred to a separate study with an independent noise
  model.
- Nothing about instances without full room: they are run and reported.
- Nothing outside 27 C, the typical corner with mismatch, two cells, one
  calendar of each spacing, six instances.
- Nothing about a network whose pulses come closer than 16 units, beyond
  the one control run.
- The per-cell measures are made on the deck of the network, by the same
  simulator. The claim is that the network does what its cells, measured
  alone, say it will; not that the measures could be made on a chip.
