# One inverter cell at transistor level: the contract quantities

**Development work. Nothing here is preregistered, and nothing here is a campaign.**

This is a simulation of one cell, with ngspice 42 and the SKY130 models, at the typical corner and 27 °C,
with no noise and no mismatch. No layout exists. The waveforms stay local and are not committed; every trace
is identified below by its sha256.

It measures the quantities that the hypotheses of `inhibited_silence` and `uninhibited_first_crossing`
([`../lean/CircuitInverter.lean`](../lean/CircuitInverter.lean)) need, for the subset of section 3.4 of the
design note asked for:
- the leak on both sides of rest;
- the wrong-sign charge, as an L1 integral;
- the off-current charge;
- the help window.

It does not show that the circuit meets those hypotheses in general: one corner, one temperature and no
noise are a single sample, not a bound.

Tags: [K] measured or read here; [I] inferred; [G] guessed.

## The cell

The starting point is the frozen cell, `research/circuit/cell.spice` at `ecfcd1c1`
(sha256 `cc322898…aed9ad`, identical on main). Lines 129-154 of that file are kept unchanged:
- the main capacitor `cq` = 5 pF and its leak `rleak = 2 tu / cq` toward `vr0` = 1.25 V;
- the FIRE comparator with its switched reference, and the protection latch.

The noise sources of those lines are held at zero, and `blocks.spice` is unchanged (sha256 `7677efdb…bfd1bd`).
The learning ports are removed. This is an untrained cell.

Added, all as design choices [G], none optimised:

| Element | Choice |
|---|---|
| Help | an ideal reference current into a diode NMOS (w 2, l 4), mirrored by a second NMOS (w 2, l 4); the mirror sinks from the main capacitor through an NMOS switch (w 1, l 0.15) gated on `[h, h + hl]` = `[0.30, 0.60]` time units; nominal 4.5 units per time unit (0.5625 µA) |
| Inhibitory input | the input pulse drives the reference of a PMOS mirror (two PMOS, w 4, l 4, from vdd); the mirror feeds the main capacitor through a PMOS admission switch (w 2, l 0.15) open on `[0, τ]` = `[0, 0.25]`; nominal input 3 units per time unit (0.375 µA) while present, so 0.75 units by `τ` |
| Reset | a transmission gate (NMOS w 1, PMOS w 2, l 0.15) from the main capacitor to `vr0`, on `[1.0, 1.1]` time units |
| Ammeters | 0 V sources in series with the help path and the inhibitory path, at the main capacitor |

One time unit is 20 µs. The coordinate is `x = (vr0 - vq) / vunit`, with `vunit` = 0.5 V, so one unit is
2.5 pC. FIRE is at `x = 0.9` (`vq = vfire = 0.8 V`). The sign conventions are those of the Lean
hypotheses:
- help `H` = current out of the main capacitor (raises `x`);
- inhibition `J` = current into it (lowers `x`).

The integration step is limited to 5 ns in the slot runs and 20 ns in the leak runs, and the switch edges
last 1 ns. Integrals are trapezoidal over the saved points.

### Iteration 1, kept on record

The first reset was an NMOS switch alone. It cannot pull the main capacitor above about `1.8 V - Vth`: after
the reset `x` was 0.335 (input absent) and 0.328 (input present), not 0 [K]. It was replaced by the
transmission gate above. Every other element is unchanged. Iteration 1's numbers are in
[`MEASURES_iteration1.json`](MEASURES_iteration1.json); all the numbers below are from iteration 2.

## Runs

| Run | Input | Help | Reset | Length | Purpose |
|---|---|---|---|---|---|
| R1 | absent | on | on | 1.3 | firing without inhibition, off-current, help window |
| R2 | present | on | on | 1.3 | silence under inhibition, delivered charge, headroom, wrong-sign charge |
| R3 | absent | on | off | 4 | leak above rest, fitted after the help window (from 1.0 to 4.0) |
| R4 | present | off | off | 4 | leak below rest, fitted after the input window (from 0.5 to 4.0) |

## Measurements (iteration 2) [K]

### Decisions

| | Result |
|---|---|
| R1 (absent) | fires. `x` reaches 0.9 at 0.5138; the protection latch rises at 0.5145 (13 ns later); `x` reaches 1.226 at most in the slot. The FIRE kicks the main capacitor back by about 0.011 units (5.5 mV) |
| R2 (present) | silent through the slot. `x` reaches 0.694 at most, at the end of the help window, a margin of 0.206 units below the threshold. `x` falls to -0.650 at least |

### Leak

| | Fit `x(a) exp(-k t)` | Fit with a constant offset |
|---|---|---|
| R3 above rest | `k` = 0.4770 per time unit | `k` = 0.4807, asymptote `x` = +0.0037 |
| R4 below rest | `k` = 0.4851 | `k` = 0.4886, asymptote `x` = -0.0016 |

The nominal value is `k` = 0.5. The two sides differ by about 0.008 per time unit (1.6 %), and both are 2 to
5 % below nominal.

### Inhibitory path

| | R1 (absent) | R2 (present) |
|---|---|---|
| Delivered by `τ`, `∫_0^τ J⁺` | | 0.709 units (nominal 0.75; current 2.965 of 3.0 at the end of the window) |
| After `τ`, `∫ abs(J)` | | 0.0039 |
| Wrong-sign charge, `∫_0^D J⁻` (L1) | 0.0069 | 0.0035 |
| Off-current charge, `∫_0^D abs(J)` (L1) | 0.0139, of which the signed integral is only 0.0002 | |

In R1, the signed integral hides excursions of both signs: the switch injects charge at its edges.

### Headroom

`vq` reaches 1.575 V at most in R2 and R4, which leaves 0.225 V to vdd. The 5.5 % shortfall of delivered
charge is the mirror's settling and its loss of headroom as `vq` rises [I]. Neither was separated from the
other.

### Help window

| | R1 | R2 |
|---|---|---|
| Charge in the window (nominal 1.35) | 1.372 | 1.381 |
| Current inside the window, mean (min, max) | 4.579 (4.329, 5.075) | 4.596 (4.567, 4.615) |
| L1 help error on every prefix, `max_t ∫_0^t abs(H - H0)` | 0.029 | 0.037 |
| `∫ abs(H)` outside the window, within the slot | 0.0061 | 0.0048 |

### Rest after the reset

`x` = -0.00014 (R1) and -0.00015 (R2).

## Against the hypotheses of the Lean theorems [I]

- **Same leak.** The theorems assume one leak `a` for the actual response and the reference. The circuit gives
  0.481 to 0.489 depending on the side and the fit. That difference is not covered by the present
  statements; it needs a separate bound, as the bridge README says for uncertainty in the leak rate.
- **Silence margin.** Take `a` = 0.4886 (the larger, which is worse here) and `D = 1`, so `exp(aD)` = 1.630.
  Take R1's `x` maximum, 1.226, for the maximum of the help-alone reference. Take `ε₀` = 0.00015,
  `ηH` = 0.037 and `ηm` = 0.0035. Then the silence condition holds with `Q` = 0.709 provided the threshold
  error `δ` is below about 0.068 units (34 mV). `δ` was not measured.
- **Firing margin.** `BF = ε₀ + ηH + ηJ + δ` = 0.043 + `δ`. The deadline margin at 0.6 is `x` = 1.226 against
  0.9, which leaves room for `δ` up to about 0.28. Using R1's actual trace in place of the reference is an
  approximation [I].
- **Output dates.** The emission (latch rise) is at 0.5145. The theorem's `contact_time_error` needs a
  lower slope of the reference and a bound on `δ`, and neither was computed here.

## Not measured, not checked

- The threshold error `δ`, and the comparator offset.
- Noise, mismatch, corners and temperature.
- A layout.
- The second FIRE: a single emission per slot was not tested beyond these runs.
- The input pulse is an ideal current into the mirror's reference, not a FIRE from another cell.
- The clocks (help window, admission window, reset) are ideal, like the clocks of the frozen cell.
- Whether the margin keeps under a different help or input amplitude.
- The stage-J junction areas used by the network bench were not applied, because this deck is not built
  by that tool.

## Files

| File | sha256 |
|---|---|
| [`inverter.py`](inverter.py) (netlist and runner, iteration 2) | `d19fdf05b048b37928a9100a27320f861cd81937792c4fb50796f6b1ba0b29a4` |
| [`measure.py`](measure.py) | `60c30aae6efd9aa0e08f2368fa376fd158749208774e1eb53127674e2f38e741` |
| [`MEASURES.json`](MEASURES.json) (every number above, and the sha256 of each deck, trace and log) | `76d15dd250341c7b05473ccc317bd08d7c10a49ac4e233d416abae089f813c2a` |
| [`MEASURES_iteration1.json`](MEASURES_iteration1.json) | `4ad350d02b190044520e24f7197c6a451cb83e2b0a5c7ee64252e0a2394da7d2` |
| local only: R1 `trace.txt` | `117d3142e0eaae5777c911751be915fdd56050b0abdcfaac9351b7fa4dc83c93` |
| local only: R2 `trace.txt` | `1d8cb10cf895b98d71c9e3ad4dc13fbe22954c3d1bb7f88bded398b6cb4029d5` |
| local only: R3 `trace.txt` | `f4c11c228715f0f1553deba71d0764534bab0937c7e6898f8e277effa6e30760` |
| local only: R4 `trace.txt` | `d970baa8624d2ff818f5b6a47e8bd26dbd3c94fb2c7e79a38c66495663a2182b` |

Environment:
- ngspice 42 from apt (`42+ds-3build1`, binary sha256 `82065831…b7fc45`);
- `sky130_fd_pr` at `1232782c1b9fab3aacda74d67ce7c92bf7da8105`;
- Python 3.12.3 with numpy 2.3.5 in a venv.

To reproduce, place `pdk/`, `blocks.spice` and `spiceinit.txt` beside the scripts and run
`python measure.py`.
