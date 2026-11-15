# A circuit network that learns (A and B) or (C and D): phase 0

**Status: design only, for review.** Nothing here is preregistered and no `PREDICTION.md` exists. No new instance
has been simulated: every measure below is on the **nominal cell** (model section `tt`, no mismatch, no seed). The
cell, the simulator and its noise model are unchanged.

The guarded theory is #168 to #171 ([`../learned-coincidence`](../learned-coincidence)): an AND-OR cascade trained
only by its own emitted pulses learns exactly the monotone Boolean functions (`MonotoneCharacterization`,
`TwoLayerMonotoneRecognition`). This phase designs its circuit version for `(A and B) or (C and D)` with three cells
of [`../circuit/cell.spice`](../circuit/cell.spice), and settles what the theory leaves to a circuit refinement: the
read-only test gate, the calibration of `CalibratedAdditiveRead`, and the timing.

| File | What it is |
|---|---|
| [`gate.py`](gate.py) | the read-only test gate, measured on the nominal cell |
| [`calibrate.py`](calibrate.py) | the calibration of one cell: empty, singleton and pair reads at each dose stage, guard on and guard off |
| [`summarize.py`](summarize.py), [`CALIBRATION.json`](CALIBRATION.json), [`phase0/`](phase0) | the fit and its calibration and validation split; the records of the runs |
| [`dnf.py`](dnf.py) | the cells, the calendar and its routing, the zero-error predictor, the timing checks, the cost |

The bench is that of [`../network-circuit`](../network-circuit) (`net.py`, `measure.py`), used without any change.

## 1. The network

| Cell | Port 1 | Port 2 | Learns | Pulse amplitude |
|---|---|---|---|---|
| a, layer 1 | input A | input B | A and B, by joint training on AB | 0.49 |
| b, layer 1 | input C | input D | C and D, by joint training on CD | 0.49 |
| c, layer 2 | the FIRE of a | the FIRE of b | the OR, each line trained alone by the actual FIRE of a or b | 1.0 |

**Why a pulse amplitude of 0.49 on layer 1.** At amplitude 1 the two charges of a joint read add up and the nominal
pair **fires from the preset** (latency 0.30 to 0.34 unit, `phase0/cal-10-on.json`), so an AND cell would have
nothing to learn, while the guarded checker requires at least one silent round (`1 <= k_i`). The pulse amplitude is
a testbench constant (the `amp` source of each port, already in `net.py`). At 0.49 the nominal pair is silent at the
preset, gains 0.0387 of the FIRE level per joint dose, and first fires at **stage 4**, with a margin of 0.38 dose at
its last silence and 0.62 dose at its first FIRE; each input alone then reaches 0.57 of the FIRE level, eleven doses
short of firing. At 0.5 the first FIRE came at stage 3 with a margin of 0.05 dose only; 0.49 centres it as a
single port of campaigns 1 to 3 is centred (gap 3.59 doses). Layer 2 keeps amplitude 1: each line alone learns as a
port of the campaigns (need 4 on the nominal cell).

## 2. Read-only tests: the gate

**Proposed: a testbench read gate.** The write of a port is the current of its bias source `idis` (8.2 nA) that the
steering switch sends into the integrator while the write signal is high. Setting that source to zero
(`alter i.x<cell>.x<port>.idis dc = 0`, 3 units before the slot, the cell at rest) removes the charge of every write
and leaves the read untouched: FIRE is decided by the main charge, which the gain mirror feeds and the sensor does
not touch. Nothing in the circuit changes. The other option, restoring a saved trained state before each test (a
fresh deck with `vinit` set to the trained stored voltages), changes no source but restores only the stored node,
needs a deck per test and a repeatability check of the rested state; it is kept as a fallback.

**Measured on the nominal cell** ([`gate.py`](gate.py), `CALIBRATION.json`, `gate`):

| | Result |
|---|---|
| a gated silent read, port 1, port 2, both | stored voltages move by at most **0.00001 mV** |
| every gated read of the calibration (192) | at most **0.00004 mV** |
| an ungated silent read, before and after gating | one dose, 1.3494 to 1.3495 mV, on the read port only |
| a clock-only joint dose (the stage step of the calibration) | 1.3494 to 1.3495 mV on each port |
| the same FIRE read ungated and gated | latency 0.9142 / 0.9161 and 0.9144 / 0.9134 unit: equal within the repeatability of the simulator (0.003) |
| across a FIRE read, gated or not | at most 0.00003 mV: a FIRE has an empty write footprint |

So **a gated silent read moves the stored voltage by less than 0.01 mV**, by a factor of 250 or more.

## 3. The calibration of CalibratedAdditiveRead

**Observable.** The score of a read is the peak of the main charge `q` (0.1 at rest, 1 at the FIRE level) over the
read, from the **matched guard-disabled probe**: the same deck with the FIRE reference `vfire` at 0 V, so that the
cell cannot fire and the charge is not reset at the FIRE. A guard-on pass of the same deck gives the FIRE bit and
its latency. At each dose stage `k` (one clock-only dose on both ports of a cell between stages) the deck reads,
under the gate, 22 units apart: the empty read, port 1 alone, port 2 alone, both at one date.

**Model.** `Z(S) = h + sum over active ports j of g_j(k)`, a constant help `h` and a linear gain path
`g_j(k) = g_j0 + d_j k`, in units of the FIRE level (`theta = 1`). Nominal cell, amplitude 0.49
(`CALIBRATION.json`):

| Stage k | u, mV | port 1 | port 2 | both | additive model | FIRE, latency |
|---|---|---|---|---|---|---|
| 0 | -10.60 | 0.4949 | 0.4949 | 0.8782 | 0.8749 | no |
| 1 | -11.95 | 0.5125 | 0.5123 | 0.9125 | 0.9124 | no |
| 2 | -13.30 | 0.5306 | 0.5311 | 0.9483 | 0.9500 | no |
| 3 | -14.65 | 0.5501 | 0.5498 | 0.9855 | 0.9876 | no |
| 4 | -16.00 | 0.5699 | 0.5701 | **1.0241** | 1.0252 | **pair, 0.880** |
| 5 | -17.34 | 0.5905 | 0.5909 | 1.0645 | 1.0627 | pair, 0.763 |
| 6, 7 (held out) | | 0.61 to 0.64 | 0.61 to 0.64 | 1.106 to 1.150 | | pair, 0.683 to 0.620 |

Fit on stages 0 to 5: `h = 0.1141` (the empty read is 0.100), `g_j0 = 0.3804`, `d_j = 0.0188` per port and dose.

- **Residual `Z - G`**: -0.0022 to +0.0034 on the calibration stages (singles and pairs); +0.005 to +0.012 on the
  held-out stages 6 and 7: the true gain path is geometric (about 4 % per dose), and a linear path drifts beyond
  the stages it was fitted on. An AND cell stops writing at its first FIRE, so a campaign reaches stages 0 to
  `need` only; **the calibration of an instance must cover every stage from 0 to its predicted need plus one**.
- **The FIRE bit is the threshold comparison** `Z >= 1` on all 32 reads of each amplitude (guard-on against
  guard-off pass).
- **Decision window.** The first FIRE of a pair rises at 0.88 unit, later ones at 0.76 to 0.62; a single port of
  layer 2 first fires at 0.91 to 0.99. The window is that of the bench, **a FIRE rising within one unit and 2 us of
  the start of the read**, and the full cycle (6 units) is checked for a late FIRE. The 0.2675 of the native
  timing note is a pair read far above threshold (amplitude 1: 0.23 to 0.34 here); the ideal native window
  (0.239, 0.256] does not apply to this circuit read, which is decoded by the bench window.
- **Layer 2, amplitude 1: the pair saturates.** Both lines together give 1.60 to 1.81 instead of the additive 1.65
  to 2.2 (residual down to -0.37, `phase0/cal-10-off.json`): far above the threshold, but outside any small
  symmetric residual. The OR read of both lines is certified here by monotonicity (it is never below the larger
  single line, measured at every stage), not by additivity. **Open point for the review**: the guarded premise asks
  one symmetric residual per cell; the theory needs either a one-sided (or per-mask) residual for the OR cell, or
  a smaller line amplitude that keeps the pair linear (at 0.49 a single line would need about 19 doses).

**Split proposed for a campaign.** Calibration: the guard-off probe of each instance, stages 0 to `need + 1` of each
cell, fitted before anything else is read. Validation: the guard-on pass (FIRE bits against `Z >= 1`), the held-out
stages, and the network runs themselves, whose predicted stops and test outputs are the claims.

## 4. The calendar

[`dnf.py`](dnf.py) (`calendar`, `separation`, `settled`). One slot every **22 units** (every read is an isolated
read, as in the calibration). The write gates of a slot are set 3 units before it, every cell at rest.

| Stage | Slots | External inputs | Writes enabled | Routing to c |
|---|---|---|---|---|
| 1, layer 1 | `max(need_a, need_b) + 3` rounds | A, B, C, D at one date (a and b train in the same slot) | a, b | off |
| 2, layer 2 | `max(need_c1, need_c2) + 3` rounds of two slots | AB in the first slot of a round, CD in the second | c | on |
| 3, tests | 16 | each pattern of {A, B, C, D}, its inputs at one date | none | on |

Routing: a FIRE of a (b) rising within the decision window of a routed slot sends one pulse of amplitude 1 to port 1
(port 2) of c, **1.5 units after the FIRE**, as `router.py` does. An upstream silence sends nothing. Timing, whatever
the latencies (0 to 1.06 unit) and a pulse 0.02 unit late: two pulses of one cell are at least **18.9 units apart**
(c) and 21.98 (a, b), above the 16 units under which the constants hold; the last pulse of a slot starts within 4.6
units of the slot, so with a cycle of 6 units and a protection of at most 6.5 units every slot is settled before the
gates of the next one are set. On the nominal predictor: 37 slots, 16.5 ms, 110 pulses.

## 5. Candidate predictions

From the per-cell calibration of each instance, with `need` the first stage at which the calibrated read fires:

| | Candidate | From |
|---|---|---|
| L1 | **layer-1 stops**: cell a writes exactly `need_a` doses on both its ports, then fires on every further round (word `s^need F^3`); the same for b | the guarded single-layer theorem and the pair calibration |
| L2 | **layer-2 per-line counts**: port 1 of c writes exactly `need_c1` doses, port 2 `need_c2`, each then fires alone | `TwoLayerMonotoneRecognition`, the singleton calibration of c |
| T | **the outputs**: on each of the 16 patterns, c fires exactly when `(A and B) or (C and D)` (7 of 16), a exactly when `A and B`, b exactly when `C and D` | the same, with the test reads read-only |
| G | **read-only**: no stored voltage moves by more than 0.01 mV across a gated read | the gate |
| H | the hypotheses observed: pulses of a cell at least 16 units apart, no late FIRE, every routed line delivered once, nothing delivered after an upstream silence | the calendar |

**Negative controls.**

- **Untrained network** (`calendar(..., "untrained")`): the 16 tests on the preset state. Predicted: no output fires
  on any pattern (the nominal pair is 0.12 below threshold at the preset), so the trained predictor would be wrong
  on the 7 true patterns: the output comes from the training.
- **Skewed coincidence** (`"skew"`): after the tests, AB and CD with the second input 2 units late. The predictor that
  ignores timing says FIRE; the charge of the first input has then decayed (leak of 2 units), so the cell is expected
  silent. It can fail without touching the other claims.

**Nominal predictor** (`dnf.nominal`): every cell nominal, need 4 everywhere, words `ssssFFF`, the outputs of the
truth table. Reported against the measured predictor as in campaigns 1 to 3 (ports and patterns where they differ).

## 6. Noise

- **Primary claim, without noise**: L1, L2, T on every eligible instance, one discrepancy refutes it.
- **Per-output claims under noise**: an output (a, b or c) whose training reads and test reads all have room under a
  `K = 3` budget gives its predicted answer on every test pattern in every noisy run; one failure refutes that
  output's claim. Its training reads must have room too, or noise could stop its training at another stage and the
  test reads would be other reads.
- **The calibration residual includes the noise**: the budget of a read is `hi, lo = residual bound + 3 sigma`, with
  `sigma` the read noise in score units, the stored-voltage noise times the measured sensitivity of the read (q per
  mV on each active port; 0.0143 per port for a pair at 0.49, 0.0267 for a line at 1).
- **Noise model**, fixed in `PREDICTION.md` and not changed afterwards: the independent model of the committed noise
  study (`research/network-noise-study-commitment`) if it is validated before this campaign is preregistered,
  otherwise the simulator's current model, with its stated limit (it overstates the low-frequency noise of the
  integrator amplifier). Today the noise study is a commitment only, so the second applies.
- **Noise constants**, proposed fixed beforehand: those observed in campaign 3 (M5: 0.111 mV between runs, 0.094 mV
  within a run), larger than the fixed constants of campaigns 2 and 3 (0.090, 0.064), with 0.009 mV per dose; for a
  joint read, the offsets of its two ports added linearly (a common cause cannot be excluded). On the nominal cell:
  `sigma` is 0.147 mV per port, so `3 sigma` is 0.0126 q for a pair, against margins of 0.0145 (last silence) and
  0.0241 (first FIRE) before the residual: the pair's last silence would keep room by a hair, its test read would
  have it; a line of c (margin 0.014 at its first FIRE, `3 sigma` 0.0117) would be as tight.

## 7. Cost, size and eligibility

`dnf.sizing`, with the cost model of the ring (3.7746 s per cell and simulated ms, 3.9820 s per cell and pulse, x 1.3861
with noise, four runs at a time). On the one-cell decks of this phase it is about twice the measured wall (125 to
152 s against 258 s): the figures below are prudent.

| Run | Expected |
|---|---|
| calibration deck of an instance (3 cells, 7 stages, guard on or off) | 1 680 s, two per instance |
| network run without noise (37 slots, 110 pulses) | 1 501 s |
| network run with noise | 2 081 s |
| untrained control (16 slots) | 560 s |
| **rehearsal on the nominal cell** (two calibration decks, one run without noise, one noisy, the untrained control) | 7 500 s of CPU, about 1 h of wall on one machine |

Instances that fit in **expected machine time**, two machines, two stages, counted as in campaigns 2 and 3, by noisy
runs per measured instance (11 of 12 measured, as campaign 3):

| Budget | 0 noisy runs | **1 noisy run** | 2 | 3 |
|---|---|---|---|---|
| 4 h | 8 | **5** | 4 | 3 |
| 6 h | 14 | **9** | 7 | 6 |
| 8 h | 20 | **13** | 10 | 8 |

**Eligibility expected from campaigns 1 to 3.** An instance here needs four learning reads with room (two pairs,
two lines), as a ring instance needs four ports. Noise-free own room per port, campaigns 2 and 3: 54 of 60 ports
(0.90), so about 0.66 of measured instances; measured, campaign 3 with the robust scan: 11 of 12. About **0.6
eligible per drawn instance** (campaigns 1 to 3 gave 13 of 24 per drawn instance for the ring and the two-cell
network). With one noisy run per instance, as campaign 3 showed more instances to be worth more than more runs: 5
instances in 4 h (about 3 eligible), 9 in 6 h (about 5), 13 in 8 h (about 8).

## What the review must decide

1. The gate (`idis` off) as the read-only mechanism, or the restored state.
2. The layer-1 amplitude 0.49, chosen on the nominal cell to centre the first pair FIRE at stage 4.
3. The calibration: observable (guard-off peak charge), model (constant help, linear gain path), split, and the
   stages it must cover.
4. **The OR cell's saturated pair**: a one-sided residual (or per-mask budget) in the guarded premise, or another
   line amplitude.
5. The noise constants and the rule that a per-output claim needs room on its training reads too.
6. The budget and the size: one noisy run per instance; 4, 6 or 8 h.
7. The controls (untrained, skew) and the nominal predictor.

Then, as before: `PREDICTION.md` pushed alone, the implementation frozen and rehearsed through the launch kit,
review, one launch per machine.

## Reproduce

```sh
"$PY" -B research/learned-dnf-circuit/gate.py /a/new/folder "$NGSPICE" "$PDK"
```

```sh
"$PY" -B research/learned-dnf-circuit/calibrate.py /a/new/folder "$NGSPICE" "$PDK" 0.49 off
```

```sh
"$PY" -B research/learned-dnf-circuit/summarize.py research/learned-dnf-circuit/phase0 research/learned-dnf-circuit/CALIBRATION.json
```

```sh
python3 research/learned-dnf-circuit/dnf.py
```
