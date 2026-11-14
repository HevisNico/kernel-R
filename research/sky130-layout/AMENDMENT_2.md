# Amendment 2 to the predictions of phase 1: chronology, report, scope, execution

Declared on 2026-11-13, at the owner's request, **before any run of
stage J or stage P.** [`PREDICTION.md`](PREDICTION.md) and
[`AMENDMENT_1.md`](AMENDMENT_1.md) are not edited. A pushed
`PREDICTION.md` is never edited, even before any run: a change goes in
an amendment.

## Decisions of the owner, recorded

- Decisions D1 to D7 of [`PHASE1_PLAN.md`](PHASE1_PLAN.md): accepted as
  proposed.
- L1 to L13: accepted as the predictions of stage P, with the
  separation between failure (L1, L5, L11) and shift (L2, L3, L8, L9,
  L12).
- JA to JM, stage J: accepted.
- [`AMENDMENT_1.md`](AMENDMENT_1.md), the identity test in two parts I1
  and I2: accepted.

No prediction, no bound, no cell and no threshold of the scope rule is
changed by this amendment.

## 1. Chronology

What happened, with the times GitHub recorded for the branch
`sky130-layout-phase1` (its activity log, UTC, 2026-11-13).

| Time | What |
|---|---|
| 18:01:48 | The branch is created on GitHub at commit `8c0aef7`. That commit holds two files: `PREDICTION.md` and `SCHEMATIC_NO_JUNCTION_AREAS.md` |
| 18:04 to 18:14 | The identity test runs on one machine: simulations of the schematic |
| 18:14:23 | A second push, `8c0aef7` to `5deaa57`: the preparations (`phase1/`, `AMENDMENT_1.md`) |
| after 18:14 | Pull request 125 is opened. It shows the two commits together |

Stated plainly:

- **`PREDICTION.md` was not pushed alone.** Its commit also holds the
  note on junction areas, and nothing else.
- **It did reach GitHub before the preparations**, in a push of its own,
  12 minutes before them. The pull request shows both commits at once
  because it was opened after the second push.
- **No run of stage J and no run of stage P was made before
  `PREDICTION.md` was pushed, and none has been made since.**
- **The only simulations made since are those of the identity test**:
  eight runs of the schematic, with no junction area and no parasitic of
  the cell ([`phase1/IDENTITY.md`](phase1/IDENTITY.md)).
- Two other things were computed since, without any simulation of the
  cell: the table of areas, from each transistor drawn alone by Magic
  (`phase1/areas.csv`), and the tests of the analysis and of the
  execution rules, which simulate nothing.
- No layout of the cell or of a block exists. No extraction of the cell
  has been made.

## 2. What the reports must say about the earlier result at 125 °C

The circuit campaign found that the nominal cell stops at 125 °C and
does not fall silent again (run `pvt_tt_125`, prediction P12, which
holds there). That run had no junction area
([`SCHEMATIC_NO_JUNCTION_AREAS.md`](SCHEMATIC_NO_JUNCTION_AREAS.md)).

**Stage J.** The report carries one of four sentences, fixed in
[`phase1/j_statement.py`](phase1/j_statement.py) before any run:

| JK (with areas, the port falls silent again every 5 to 11 periods) | JL (without areas, it does not) | The report states |
|---|---|---|
| holds | holds | **The earlier 125 °C result, a stop with no relapse after it, was an artifact of netlists without junction areas** |
| fails | any | The arithmetic of phase 0 does not carry to the cell as predicted. No artifact is claimed |
| holds | fails | The relapse is not shown to come from the areas. No artifact is claimed |
| one of them not evaluable | | Nothing is stated |

**Stage P.** If L13 holds, the report of stage P states, in these words:
"The earlier 125 °C result, a stop with no relapse after it, was an
artifact of netlists without junction areas." If L13 fails or is not
evaluable, it does not.

In both reports the sentence is followed by what it rests on: a nominal
simulation, with the areas of devices drawn alone (stage J) or of the
layout (stage P).

## 3. Scope of stage P

The order before stage P is fixed:

1. the layout, DRC and LVS clean, and the list of extracted
   capacitances;
2. the identity test I2 of amendment 1, every capacitance at 0 F;
3. **the timing run**, on machine A alone: the 2-period ramp of the
   nominal cell, once on the schematic and once on the stage-P netlist,
   one after the other, nothing else running. `f` is the second wall
   time divided by the first;
4. **a commit of its own**, `phase1/SCOPE_P.json`, with the two wall
   times, `f`, and the scope that the rule of
   [`PREDICTION.md`](PREDICTION.md) gives for that `f`. Nothing else is
   in that commit. It is pushed before the attempt marker of stage P;
5. the attempt marker of stage P, then the runs.

The scope follows from `f` by the table of
[`PREDICTION.md`](PREDICTION.md) and from nothing else. `f` is not
rounded.

**The outputs of the timing run other than its two wall times are never
read**: not before the campaign, not after it. The simulator writes
them to a folder that the timing script deletes before it prints. They
are not saved, hashed or published.

## 4. Execution on two cloud machines

Both stages run on two machines, A and B, of four cores each.

### Same simulator on both

Each machine, before its first run of a stage:

- checks the hash of the simulator and the commit of the device models
  against the manifest of the stage;
- runs the nominal cell of the schematic and compares it, byte for
  byte, with the committed `../circuit/results/nom.csv`.

A machine that does not reproduce the nominal run **runs nothing**. Its
preflight is pushed as it is.

### The split is fixed

**Stage J.**

| Machine | Runs |
|---|---|
| A | J1, J4, J5 |
| B | J2, J3, J6 |

**Stage P.** Each machine has a queue. A unit is the set of runs of one
cell.

| | Machine A | Machine B |
|---|---|---|
| Nominal runs | cell run, ramp, read, leak scan (27 °C) | refresh under 0.1 TΩ (27 °C), cell run and refresh at 125 °C, the run with resistance |
| Then, alternating | calibration `5001` with its leak scan, cell `t6065` | calibration `5002` with its leak scan, cell `t6030` |
| | calibration `5003`, cell `t6031` | calibration `5004`, cell `t6002` |
| | calibration `5005`, cell `t6074` | calibration `5006`, cell `t6003` |
| | calibration `5007`, cell `t6082` | calibration `5008`, cell `t6051` |

- A calibration unit is the noiseless train and the ramp of its seed.
- A cell unit is, in this order: ramp, read, leak scan, noiseless gain
  run, noisy test run.
- Each machine holds two cells of large room and two of small room, and
  meets them in turn.
- **The three scopes are prefixes of these queues.** Reduced scope stops
  each queue after its second cell, and drops the leak scan of `5002`.
  Minimal scope keeps the nominal runs and the first cell of each queue,
  with no calibration. These are the cells that
  [`PREDICTION.md`](PREDICTION.md) names for each scope.

### One attempt marker

- **One marker per stage covers both machines**:
  `phase1/RUN_ATTEMPT_J.json`, and later `phase1/RUN_ATTEMPT_P.json`.
- Machine A writes it and pushes it **before the first run of the
  stage**. Machine B does not start until the marker is on the branch.
- It names attempt 1, the commit of the code, the split, and the sha256
  of `PREDICTION.md`, of the two amendments, of the manifest and of the
  code that launches. A launch stops if one of them has changed.
- **There is no attempt 2.** A stage that is interrupted goes on under
  the same marker, by the rule below, or ends there.

### A run that started is never run again

- Before a machine starts a run, it pushes the name of the run as
  started. The run begins only when that push has succeeded.
- **After a restart of a container, a run that was pushed as started and
  has no result is recorded as lost. It is never run again**, on either
  machine.
- A run that was never pushed as started may proceed.
- A run that ends in failure stays failed. It is not run again.
- A lost run and a failed run give nothing to the analysis. Nothing
  replaces them.

This is stricter than the repetition campaign, which ran again the runs
that a restart had killed.

### Order: any prefix is usable

- Runs start in the order of the queue, four at a time on each machine.
- Results are pushed as each group of four ends.
- In stage P the queues alternate calibration and cells, so that a
  campaign cut short holds whole cells, of both kinds, with part of the
  calibration.

### Analysis of a truncated campaign, fixed now

A campaign is truncated if a run of its scope has no result. The report
then says so and lists those runs. The rules:

| | Rule |
|---|---|
| A prediction on one run (JA to JL; L1 to L4, L6, L13) | Judged on that run. **Not evaluable** if the run has no result |
| The guard (JM, L5) | Not evaluable if a run of the scope has no result. The events seen are reported in any case |
| A cell | Evaluable if its five runs have a result. A port is evaluable if its cell is |
| The constants `d0`, `kappa`, `mu`, `h_mu` | From the calibration, if at least 4 calibration units and 1 calibration leak scan have their results, and the nominal leak scan too. **Otherwise the constants of `../circuit/certification/CALIBRATION.md` are used for every port**, and the report says so |
| L7 | On the nominal cell and on every evaluable cell |
| L8, L9 | On every evaluable port. L8 needs the nominal ramp and read |
| L10, with `n` evaluable ports | The count agrees on at least `n − 3` ports if `n` is 13 or more, `n − 2` if `n` is 6 to 12, `n − 1` if `n` is 3 to 5. Not evaluable below 3 |
| L11 | On every evaluable port. One contradiction makes it fail. The report gives the number of certified ports it rests on, zero included |
| L12, with `k` of the four large-room ports evaluable | At least 3 certified if `k` is 4, at least 2 if 3, at least 1 if 2; the port is certified if `k` is 1. Not evaluable if `k` is 0 |

For a full, a reduced and a minimal campaign with every run present,
these rules give the thresholds of [`PREDICTION.md`](PREDICTION.md): 13
of 16, 6 of 8, 3 of 4 for L10; 3 of 4, 1 of 2, 1 of 1 for L12.

A prediction that is not evaluable is reported as such. It counts
neither as holding nor as failing.

### How stage J is launched

By [`phase1/execute.py`](phase1/execute.py), which applies the rules
above. `j_stage.py launch` is not used. The rules are tested, with no
simulation, on two throw-away checkouts
([`phase1/test_execute.py`](phase1/test_execute.py)): machine B waits
for the marker, a started run is lost after a restart and is not run
again, a run that never started proceeds, a machine that does not
reproduce the nominal run runs nothing, a changed input stops the
launch.

```sh
python3 -I execute.py launch --machine A --go      # machine A, first
python3 -I execute.py launch --machine B --go      # machine B, once the marker is pushed
python3 -I j_stage.py report && python3 -I j_statement.py     # once, after the last run
```

The launcher of stage P does not exist yet. It will follow the same
rules and be committed, with its tests, before the attempt marker of
stage P.

## 5. Time budget on two machines

Seconds per run are the medians recorded in the committed campaigns.
The wall time is that of the slower machine, with four runs at a time.
Core time is the sum over both machines.

**Stage J**

| Machine | Runs | Simulated periods | Wall time |
|---|---|---|---|
| A | J1, J4, J5, at once | 184 | about 12 min, the nominal preflight included |
| B | J2, J3, J6, at once | 144 | about 8 min |

**Whole campaign**: stage J, the preflights, the runs on the schematic
that check the new runner, and stage P.

| Scope | `f` | Wall time, machine A | Wall time, machine B | Core time |
|---|---|---|---|---|
| Full | 1 | 0.5 h | 0.6 h | 4 h |
| Full | 4 | 1.3 h | 1.5 h | 11 h |
| Full, at its upper `f` | 6 | 1.9 h | **2.1 h** | 16 h |
| Reduced, at its upper `f` | 10 | 1.9 h | **2.0 h** | 16 h |
| Minimal, at its upper `f` | 18 | 1.7 h | **2.3 h** | 16 h |

- With two machines the campaign stays under 2.5 hours of wall time in
  every scope, against 3.7 to 3.9 hours on one.
- The core time does not change: at most about 16 core-hours.
- **The thresholds of the scope rule are not changed.** They were fixed
  for one machine of four cores. Two machines would allow the full scope
  up to a larger `f`; that margin is not used.
- `f` is not measured yet. The drawing of the layout is not in this
  budget.
EOF
cd /home/user/kernel-r/research/sky130-layout && ls --time-style=+%T -l phase1/build/identity/*/work/*.spice* | awk '{print $6, $7}' | sort | sed -n '1p;$p'; ls --time-style=+%T -l phase1/build/identity/*/results/*.csv | awk '{print $6}' | sort | sed -n '1p;$p'