# The three development instances: cost first

**Development only, nothing preregistered.** One mismatch draw each (`tt_mm`, seeds 9801–9803, outside every
campaign range), no noise, 27 °C. Data in [`dev/`](dev/): `record.json` (every slot, every read), `measure.json`,
`Dev<TAG>.lean`, `lean.json`. Run on the session's 4-core container, two or three jobs at a time; each ngspice
process is single-threaded (CPU time = wall time within 1 %).

| Group | Instance | Network | Seed |
|---|---|---|---|
| 1 | NOT1 | front end (1 inverter) + `copy(¬x)` (1 layer) | 9801 |
| 2 | ANDOR3 | `both(x0,x1)`, `copy(x2)` / `either` / `copy` (3 layers) | 9802 |
| 3 | XOR3 | front end (2 inverters) + `both(x0,¬x1)`, `both(¬x0,x1)` / `either` / `copy` (3 layers) | 9803 |

## Cost (machine-minutes, one core)

| Instance | Deck setup | Training | Test of all patterns | Total | Slots (lessons + tests) | Simulated |
|---|---|---|---|---|---|---|
| NOT1 | 0.3 | 0.7 | 0.25 (2 patterns) | 1.2 | 6 + 2 | 3.4 ms |
| ANDOR3 | 0.3 | 12.6 | 3.9 (8 patterns) | 16.8 | 23 + 8 | 13.3 ms |
| XOR3 | 0.3 | 26.3 | 2.4 (4 patterns) | 29.0 | 33 + 4 | 16.2 ms |

Plus the Lean check: 1.3 s, 3.4 s, 4.3 s (one `lean` call each; the imported modules are compiled once, 92 s).
The cost is about 30 s per slot for a 4-cell deck and 47 s per slot for the 4-cell, 2-inverter deck: the 22 tu slot
at a 200 ns largest step dominates. Training is 75–90 % of the cost of a 3-layer instance.

## Deck size

| Instance | R cells | Inverters | Transistors | Voltage nodes (expanded, incl. PDK sub-circuit internals) |
|---|---|---|---|---|
| NOT1 | 1 | 1 | 278 | 1054 |
| ANDOR3 | 4 | 0 | 928 | 3497 |
| XOR3 | 4 | 2 | 1020 | 3843 |

## Training words and outputs

Words per (layer/cell/group), `s` silent, `F` FIRE: NOT1 `ssssFF`; ANDOR3 `ssssFF`, `sssFF` / `ssssFF`, `sssFF` /
`ssssFF`; XOR3 `ssssFF`, `sssFF` / `sssssFF`, `ssssssFF` / `sssssFF`. No cell fell silent after its first FIRE.
Every output equals the function on every pattern (2, 8, 4 patterns), and every cell of every layer emits exactly
when the cascade predicts.

## Measured quantities (time units, exact fractions in `measure.json`)

| Instance | Layer | skew | deadline | dmin | dmax | λmax = skew + dmax | chain margin |
|---|---|---|---|---|---|---|---|
| NOT1 | 1 | 0.20 | 1.40 | 0.92 | 0.92 | 1.12 | 0 (layer 1 skew = w) |
| ANDOR3 | 1 | 0 | 1.20 | 1.00 | 1.00 | 1.00 | 0 |
| | 2 | 1.20 | 2.40 | 0.28 | 1.00 | 2.20 | 0.20 |
| | 3 | 2.40 | 3.60 | 0.98 | 0.98 | 3.38 | 0.20 |
| XOR3 | 1 | 0.20 | 1.40 | 0.86 | 0.86 | 1.06 | 0 (layer 1 skew = w) |
| | 2 | 1.40 | 2.60 | 0.88 | 0.98 | 2.38 | 0.34 |
| | 3 | 2.60 | 3.80 | 0.92 | 0.92 | 3.52 | 0.22 |

Wire delay 0.12 on every port. Front end: inputs at T, direct-rail lag 0.44 (= emit_early, by construction), every
inverter emission at T + 0.52 (latch at 0.51–0.52; the router's 0.4 µs grid rounds it up), inside (0.44, 0.64];
w = 0.20, inverter window 0. The chain margin is `s(l+1) + skew(l+1) − (s(l) + λmax(l) + delta)`; the
start inequality holds with margin dmin. The ANDOR3 layer-2 dmin of 0.28 is the OR cell on pattern 111: it fires
0.28 after its second arrival.

## Verdicts

| | NOT1 | ANDOR3 | XOR3 |
|---|---|---|---|
| Chain inequalities (`checkChainDates`, λmax = skew + dmax), tests and lessons | hold | hold | hold |
| Scheduled, intrinsic delays, latencies, arrival windows, decoder clause, routing (Python) | hold | hold | hold |
| Front end (`checkLayeredFront`) / external window | holds | holds | holds |
| Kernel (`decide +kernel`, every checker value) | accepted | accepted | accepted |

A negative control (NOT1 with dmax lowered by 0.02) is rejected by the kernel, at the two intrinsic-delay theorems.

## Not checked, and deviations

- **Calibration premises are not checked**: no measured score in calibration units, no fitted cell parameters; the
  Lean cells are `canonical` placeholders. The kernel checks the timing chain, the front end and the decisions on
  measured data, not `LayerReads`, so the recognition theorems are not applied to these traces.
- One mismatch draw per instance, no noise, one temperature: a sample, not a bound. dmin = dmax in several layers
  because the emission dates are on the router's 0.4 µs grid (0.02 tu).
- The wire delays are realised by the router (pulses launched while the run is stopped), not by elements in the deck.
- The routed `Checker.routed` walk in the Lean file has no soundness proof.
- `share_lessons`: ANDOR3's two layer-1 cells share one stimulus (`{x0,x1,x2}`, valid for both by `Node.Valid`), so
  they train in the same slots. The witness on proof/layered-composition uses separate stimuli.
- ngspice prints "Too many iterations without convergence" once per run, at the first interrupt (20 µs); the run
  goes on and no other solver message appears.
- No junction areas or wire capacitances (no layout); the slot length (22 tu) and step (200 ns) are those of the
  learned-DNF campaigns. They are the main cost levers and were not changed.
