# Circuit simulation of one R cell

A transistor-level simulation of one R cell with two ports, in the
SkyWater 130 nm process, with ngspice and the open SKY130 device models.

**These are simulations. No chip was built and no layout was drawn.
Nothing here is a proof, and nothing here is a hardware measurement.**
The Lean proofs of the model are in [`proof/lean/`](../../proof/lean/README.md).

## Question

Does a cell, left alone with a train of identical pulses, raise its
gain and stop by itself, with device mismatch and noise? Does it hold
its gain when the stored voltage leaks?

## What this does not test

Two trained ports of this circuit fire together near 0.267 time units.
The window proved for the ideal model is (0.239, 0.2554]. The circuit
is outside that window, and no result here is a test of it. The
campaign tests the mechanism: a write on a silent pulse, no write on a
firing pulse, a stop that holds, and a read that agrees between cells.

## Files

| File | Contents |
|---|---|
| [`DESIGN.md`](DESIGN.md) | The circuit, the reason for each design choice, the noise, the solver settings, what is not modelled |
| [`PREDICTION.md`](PREDICTION.md) | Checks and predictions, written before the campaign |
| [`cell.spice`](cell.spice), [`blocks.spice`](blocks.spice) | The netlist of the cell and its building blocks |
| [`run.py`](run.py) | Runs one cell and writes one row per pulse |
| [`campaign.py`](campaign.py) | The 146 runs of the campaign |
| [`analyze.py`](analyze.py) | Applies the guard, gives a verdict on each prediction, draws the figures |
| [`noise.py`](noise.py), [`noise.json`](noise.json) | Noise analysis of each block and the levels injected |

## Method

- **Predictions first.** [`PREDICTION.md`](PREDICTION.md) was committed
  on 2026-11-12 at 07:22 UTC in the working repository of the campaign.
  The first run started at 07:23 UTC. The file here is identical; its
  SHA-256 is
  `8c17bf311e7f1353a6a41da84ad8f9c4fd3b4b6ff150c2a6009b620e935181e8`.
  The predictions are not blind: the file says what was known when it
  was written.
- **One netlist, one set of options.** Every run of the campaign uses
  the same netlist, the same solver options and the same largest time
  step.
- **A guard on every run.** A run with a protection that rises at the
  pulse edge, after the pulse, twice, without an end, or with no pulse,
  is reported as an anomaly and left out of the statistics. A run that
  the simulator aborts is listed as failed.
- **A failed prediction stays** in the report with its verdict.

## The campaign

| Series | Runs | Conditions |
|---|---|---|
| Nominal cell | 2 | Typical corner, 27 °C, no noise. One run with 26 pulses per port |
| Noise | 20 | Typical corner, noise on |
| Mismatch and noise | 100 | Monte Carlo mismatch, noise on |
| Corners and temperature | 6 | ss, ff, sf, fs at 27 °C; typical at −40 and 125 °C; no noise |
| Refresh | 5 | One port, 150 to 560 pulses; no leak, 0.1 TΩ or 1 TΩ; with and without noise |
| Refresh with mismatch and noise | 8 | One port, 100 pulses, 0.1 TΩ |

One time unit is 20 µs. A cell run is 22 periods of 440 µs.

## Running

ngspice 42 and Python 3 with numpy 2 and matplotlib are needed.

```sh
cd research/circuit
sh fetch_pdk.sh
cp spiceinit.txt .spiceinit
mkdir -p work results
python3 campaign.py
python3 analyze.py
```

`fetch_pdk.sh` fetches the SKY130 primitive models at a fixed commit.
They are not part of this repository. The campaign takes about two and
a half hours on four cores.
