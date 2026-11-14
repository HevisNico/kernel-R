# Amendment 4 to the predictions of phase 1: how stage P is run and read

Declared on 2026-11-13, **before the attempt marker of stage P and
before any run of stage P.** [`PREDICTION.md`](PREDICTION.md) and the
three earlier amendments are not edited. No prediction, bound, cell or
threshold is changed.

The owner gave the go for stage P in full scope
(`phase1/SCOPE_P.json`: `f` = 1.096) and accepted the scope of the
secondary analysis of [`AMENDMENT_3.md`](AMENDMENT_3.md): the seven
nominal runs, after the primary queue of each machine.

This amendment fixes what the earlier documents left to the launcher,
and declares one deviation.

## 1. One deviation: the run with resistance is not in this attempt

[`PREDICTION.md`](PREDICTION.md) lists one nominal cell run with
resistance extracted, reported apart, and
[`AMENDMENT_2.md`](AMENDMENT_2.md) puts it in the queue of machine B.
**Its netlist does not exist.** Resistance splits the nets, so it
cannot be built as the other netlists are, by adding capacitors to the
schematic.

- **It is taken out of the queue of machine B. It is not counted as a
  run without a result.**
- It decided no prediction and was to be reported apart.
- It may be made later, under a declaration of its own. Until then
  stage P says nothing about the resistance of the wires.

The queues are otherwise those of [`AMENDMENT_2.md`](AMENDMENT_2.md):
`python3 -I phase1/p_plan.py` prints them, 37 runs on machine A and 35
on machine B, the seven secondary runs last.

## 2. The runs are made by the runners of the campaigns, unchanged

| Run of stage P | Runner, not edited |
|---|---|
| Nominal cell run and refresh runs, at 27 °C and 125 °C | `../circuit/run.py`, with the arguments of runs J1, J4, J2 and J5 of stage J |
| Ramp, read, calibration runs, noisy test run | `../circuit/certification/cert_run.py` |
| Leak scan and noiseless gain run of a cell | `../circuit/certification-unconditional/uncond_run.py`, then `uncond_early.py` |

- The certification runners look their runs up in a manifest beside
  them and call the simulator by the path it gives. Each run is
  therefore made in a mirror: copies, byte for byte, of the files the
  runners read, with a manifest written by `phase1/p_run.py`.
- That manifest gives `phase1/p_shim/ngspice` as the simulator. The
  shim rewrites the deck with `netlist.py` and starts ngspice. **The
  metadata of a run therefore carry the hash of the shim where the
  campaigns carry that of ngspice**; the hash of ngspice is in
  `phase1/p_manifest.json` and is checked before a launch.
- The nominal read is `nom_read`, a run of `cert_run.py` in its mode
  "read". The campaigns have no such run of the nominal cell.
- The noisy test run of cell `tNNNN` uses the noise identifier
  700000 + NNNN, with the preload built from
  `../circuit/repetition/fakepid.c`.
- The two leak scans of the calibration are those of seeds 5001 and
  5002, the first of each queue.
- The compact traces stay on the machine that made them. The charges
  that status 3 needs are computed there, right after the run, and are
  pushed with its rows.

**The harness was checked on the schematic** (`phase1/ref_p/check.txt`,
`phase1/ref_p/check_extra.txt`): simulations of the schematic, no area
and no capacitance of the layout.

| Run of the harness, deck of the schematic | Against | Result |
|---|---|---|
| `nom_ramp`, `t6065_ramp` | committed static levels | identical |
| `nom_leak`, `t6065_read`, `c5001_train` | committed rows | identical byte for byte |
| `u6065_leak`, `u6065_train` | committed rows, charges and early charges | identical byte for byte |
| `t6065_train` with noise, made twice with one noise identifier | each other | identical byte for byte |
| `nom_cell` with the supply current saved, and the option `rel=1` of `run.py` as in stage J | `../circuit/results/nom.csv` | flags, stored voltages, lowest voltage and steps identical; the six times within 0.0003 unit, which is the resolution `rel=1` adds |

One more check was made on the expanded netlist with the areas of the
layout and every capacitor at 0 F: an operating point, no transient,
to see that the two transistor currents that `uncond_run.py` saves keep
their names. They do. The two values were printed, 67 nA and 75 nA.

Before its first run each machine checks, besides the nominal schematic
run, that the noise preload builds and that the simulator starts under
it. A machine that fails runs nothing.

## 3. What the analysis reads, fixed now

`phase1/p_analyze.py`. The rules of the campaigns are applied by their
own scripts, run unchanged in a mirror on the results of stage P:
`cert_analyze.py` (constants, need, budget), `uncond_analyze.py` and
`uncond_amend1.py` (status 3). Rule A1 is computed with the functions
of `../reusable-controller/physical/asymmetric_check.py`.

| | Read as |
|---|---|
| L1 to L4 | On `nom_cell`. L4: the step of the pulsed port, on every firing pulse |
| L5 | The two predicates of the guard of `../circuit/analyze.py` on every row of every primary run, and the protection in the period at rest. Not evaluable if a primary run has no result |
| L6, L13 | On `nom_refresh` and `nom_refresh125`: at least two silent pulses after the stop, every interval in the range, as JF and JK were read |
| L7 | Static level of the ramp, against the committed static level of the same cell |
| L8 | The gap is that of `cert_analyze.py predict`. **The nominal shift is taken port by port**: both must be in the range, and each port of a cell is compared with the nominal shift of the port of the same number. The schematic gap of the nominal cell comes from `phase1/ref_p/nom_read.csv`, a schematic run made by the harness, with the constants of the campaign |
| L9 | Need of `predict` here, against the committed `predictions.csv` |
| L10 | The count agrees as `cert_analyze.py certify` says it does |
| L11 | A port is certified if its status 3 is "certified" or if rule A1 finds it eligible. One contradiction of either makes L11 fail |
| L12 | Certified again: status 3 is "certified" |

Three things differ from the campaigns because stage P is smaller.
None is a choice made after seeing a result.

- **Two allowances are largest values over the noisy test runs**: `eps`
  of `certify` and `epsKappa` of rule A1. Here they are taken over 8
  runs, in the campaigns over 100. They can only be smaller here, which
  makes a room a little larger: on the committed results of the
  schematic, taken for the 8 cells alone, the room at status 3 of a
  port moves by up to 0.0003.
- Rule A1 was published as a projection on a frozen snapshot of 200
  ports. Here its formulas are applied to the tables of this stage.
- `h_mu` is the worst case over three leak scans, as
  [`PREDICTION.md`](PREDICTION.md) says.

**The analysis was tried on the committed results of the schematic**
(`phase1/test_p_stage.py`, no simulation): with the constants of the
campaign, the scripts run in the mirror give again the committed need,
gap, count and status 3 of each of the 16 ports.

## 4. The secondary analysis

The seven runs `s_nom_…`, with `phase1/p_caps.csv`. The report gives
their readings beside those of the primary analysis: silent pulses
before the first FIRE, steps, static level, silent pulses after the
stop at 27 °C under 0.1 TΩ and at 125 °C, the guard. No calibration is
made with the secondary list, so no gap and no need are given for it.

## 5. The supply current

Read on `nom_cell`: the shim adds the current of the 1.8 V source to
the saved signals and writes it to a file, from which `p_run.py` keeps
the mean current of each period of 440 µs. The report gives the mean
current at rest, in a period with a silent pulse and in a period with
a firing pulse. Reported, not predicted. The references, bias sinks
and clocks are ideal sources outside the cell: their consumption is
not in this figure.

## 6. Machines

Machine A and machine B are the two sessions that were A and B in
stage J. Machine A pushes `phase1/RUN_ATTEMPT_P.json`; it pins this
amendment, the three before it, `SCOPE_P.json`, the manifest, the
queues, the launcher, the runner, the shim, the analysis and the three
tables of the layout.

```sh
python3 -I p_execute.py launch --machine A --go      # machine A, first
python3 -I p_execute.py launch --machine B --go      # machine B, once the marker is pushed
python3 -I p_analyze.py report                       # once, after the last run of both machines
```
