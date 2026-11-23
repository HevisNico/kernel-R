# Layered networks on the circuit: deck builder, measure, Lean check, batch driver

**Development only. Nothing here is preregistered, and nothing here is a campaign.** Simulations with ngspice 42 and
the SKY130 models (typical corner with mismatch, `tt_mm`, 27 °C, no noise). No layout exists.

One package, one configuration ([`config.json`](config.json)), one driver ([`lnet.py`](lnet.py)):

| File | Role |
|---|---|
| `spec.py` | the network spec (structure only), checked against the Lean types: gates, sources, stimuli, the front end, the expected function; the design timing of each layer |
| `deck.py` | one SPICE deck with every R cell, every inverter, their stimulus sources and their write gates |
| `session.py` | one ngspice process driven through a pipe |
| `run.py` | the router and the calendar: training layer by layer, then every input pattern; `record.json` |
| `measure.py` | every quantity of the Lean chain, and the Python checks; `measure.json` |
| `lean.py` | the Lean file of the instance and its check by `decide +kernel`; `lean.json` |
| `lnet.py` | `deck`, `run`, `measure`, `lean`, `job` (the three in a row), `batch JOBS OUT` |

Stable pieces imported, all unchanged: the circuit files `research/circuit/cell.spice` and `blocks.spice` (read as
text and wrapped in sub-circuits), the SKY130 models at the pinned commit, the ngspice 42 binary (its sha256 is
checked), and the Lean modules of `research/learned-coincidence` listed in `config.json` (compiled into `build/`).
No Python code of older campaigns is imported; their method is followed (cited in each file's docstring).

## The circuit

- **R cell**: `cell.spice` unchanged, made a sub-circuit; each port has its own admission, reset and precharge
  signals and its pulse date and amplitude, set while the run is stopped (the method of `network-circuit/net.py`).
  Amplitudes: 0.49 on a `both` port, 1.0 on a `copy` or `either` port (the family campaign's values). A `copy` cell
  uses port 1 only. Write gate: the port's dose source `idis` at 0 (the read-only gate of `learned-dnf-circuit/gate.py`).
- **Inverter**: the cell of `research/circuit/inverter/inverter.py` (proof/circuit-inverter-composition 062a2862):
  main charge, comparator and latch of the R cell, gated help sink, inhibitory PMOS input, reset gate, with
  **J0 = 4.0** (the redesign); the other design values are those of that file. Its clocks are set per slot.
- **Mismatch**: section `tt_mm` and `setseed SEED` for every device of every cell and inverter.
- **Router**: an emission of a line or a cell sends one pulse to every port wired to it, `delta` later. A FIRE is
  the rise of the protection latch through 0.9 V; its pulses are launched at the first date of the 0.4 µs noise grid
  at or after latch + delta, so the recorded emission (launch − delta) is at most 0.4 µs (0.02 tu) after the latch.
  The wire delays are realised by the router, not by elements in the deck.

## The calendar

Slots are 22 tu apart (the slot of the learned-DNF campaigns). Write gates are set 3 tu before each slot.
- **Lessons**, in the order of `TrainingTrace` (layer, cell, group, round). The cells of a layer whose group has the
  same stimulus share one slot per round. The lower layers replay read-only. A cell's rounds stop after it has fired
  twice in a row (`hold`), at most 10; its Lean `maxWrites` is its number of rounds minus one.
- **Tests**: every input pattern, read-only, routed through every layer.

Design timing (`config.json`, fixed before a run): wire delay `delta` = 0.12 tu on every port; read start
`s(l+1) = s(l) + delta` (no latency lower bound is assumed); `skew(1) = w`, `skew(l+1) = skew(l) + dmax_design`,
`deadline = skew + dmax_design`, `dmax_design` = 1.2 tu. Front end: inputs at `T`, direct rails delayed by
`emit_early` = 0.44 tu, `emit_late` = 0.64 tu, `w = emit_late − emit_early` = 0.2 tu, inverter window 0.

## What is checked

`measure.py` extracts per layer `s`, skew, deadline, every emission date, `dmin` and `dmax` (the delay from the later
of the read start and the last arrival to the emission), the wire delays, the external window `w`, and with a front
end the inverter emission offsets and the direct-rail lag. The Lean file states the value of each library checker on
the measured data (Python's value) and the kernel must agree:
`checkLayeredValid`, `checkChainDates` with `λmax = skew + dmax`, and for every test pattern `checkScheduled`,
`checkIntrinsicDelays`, `checkLatencies`, `checkLayeredFront` (or `checkExternalWindow`), the realised pattern, the
observed output against the function; for every lesson `checkTrainingScheduled`, `checkTrainingChainDates`,
`checkTrainingPulses`, the intrinsic delays and the front end. A walk with the library's `routed` Boolean checks the
routing (that walk has no soundness proof).

**Not checked**: the calibration checkers (`checkLayeredTrainingCalibration`, `checkLayeredReadCalibration`). They
need measured scores in calibration units and cell parameters fitted to the circuit; this run produces neither. The
cells in the Lean file are `canonical` placeholders. So the kernel checks the timing chain and the decisions on
measured data, not the recognition theorem's calibration premises.

## Run

```
python3 lnet.py job specs/xor3.json OUT 9803
python3 lnet.py batch JOBS.dev OUT          # at most 4 jobs at a time, one OUT/<name>.status per job
```
Needs ngspice 42 on PATH (the pinned binary), the models (`research/circuit/fetch_pdk.sh`), Lean 4.35.0 on PATH.

## Development instances

See [`DEV_REPORT.md`](DEV_REPORT.md).
