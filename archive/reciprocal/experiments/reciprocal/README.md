# Reciprocal R — cells stay alive and learn from one another

Three R cells take part: A learns, teaches B, then learns from B's responses. C is
introduced later and encounters a faster cadence. This experience travels back to
B and A. All introduced cells remain alive; the live network state is never reset
between stages.

This is a numerical exploration. The measured skills are responsiveness at a port
and cadence tracking. Semantic memory, general learning and a hardware advantage
have not been demonstrated.

## Open and explore

Extract the ZIP and open `03_Visualization/OPEN_IN_BROWSER.html`. The viewer replays
recordings: each scenario is a separately computed simulation. The slider and Play
button browse recorded states; they do not integrate the equations in the browser.
Settings are sampled every 2 model time units.

The display shows gains g0/g1/g2, recovery b, reserve E and permitted pulse links.
A dashed link indicates a recent settings copy. E is a model reserve, not a measured
energy in joules.

## Model and experimental protocol

Each cell retains R's main charge q, three auxiliary charges m, three log-gains z,
recovery b, reserve E, main modes READY/FAST/SLOW, auxiliary modes
READY/MARK/SILENT/ERROR and active raw currents. Direct hybrid ODE integration
locates threshold crossings and parameter caps.

All three cells have nominal physical parameters in this first network experiment.
The local laws are R's. Reciprocal connections, delays, staged introductions,
settings copies and communication windows are an added experimental protocol;
they are outside the existing A22 certificate.

Each transmitted pulse has the canonical waveform `ln(4)*exp(-ln(4)*age)` for one
time unit, following a connection delay of 0.35. Port roles are imposed by the bench:

- g0: local experience;
- g1: teaching received from the cell to the left;
- g2: feedback from the cell to the right, or a new local input.

## Six stages

| Time | Experience |
|---|---|
| 0–160 | A receives its first source on port 0. |
| 160–320 | B is introduced. A's outputs reach B's port 1. |
| 320–480 | B receives a new source on port 2. Its outputs reach A's port 2. |
| 480–640 | C is introduced. B's outputs reach C's port 1. |
| 640–800 | C receives a period-4 source instead of period 8. Its outputs reach B; B's reach A. |
| 800–1000 | Both directions open simultaneously. External inputs end at 860, followed by quiet observation. |

The first five stages use turn-taking link windows. The last opens the reciprocal
network. Cells keep evolving without input. Exact sources and windows are in
`04_Results/plan.json`.

## Pulse learning and settings transfer

Pulses engage R's native plasticity: auxiliary ERROR phases during main READY
increase gains; auxiliary MARK phases while the main cell is protected increase b.

Settings copying is external to the kernel. At times 160, 470, 480 and 800, the
protocol can transfer the three log-gains and b. The recipient takes the maximum
of its own and the received setting, bounded by its physical caps. Copies occur
only in quiescence and cannot reduce an acquired setting. Ports are matched by
role; this correspondence is not learned. No physical copying cost is modeled.

Charges, modes, reserves and currents are not copied. Parents remain present.
The `before` and `after` fields contain `[z0,z1,z2,b]`, where z=log(g).

## Observations

Probes use separate, resting test cells initialized with the acquired gains and b,
with peer links removed and plasticity disabled. They measure retained behavior
without changing the live network.

### A learns from B before a feedback settings copy

Between t=319.9 and t=459.9, no settings are copied. With pulse exchange, A's
feedback-port gain rises from **0.3 to 1.814894**.

| Scenario | A's probe before B's feedback | A's probe afterwards |
|---|---:|---:|
| Pulses + settings | 0/8 | 8/8 |
| Pulses only | 0/8 | 8/8 |
| Settings only, before the copy at 470 | 0/8 | 0/8 |
| No exchange | 0/8 | 0/8 |
| Pulses without feedback to parents | 0/8 | 0/8 |

The probe supplies eight pulses spaced by 20 on port 2. Acquired gain and isolated
responsiveness establish a minimal local learning effect; circulating events alone
would not establish that effect.

### C's faster cadence travels back to B and A

In the full scenario, between t=639.9 and t=789.9, b rises from **0.18 to 0.38** in
A, B and C. Their period-4 probes improve from **4/8 to 8/8**. There is no settings
copy in this interval. Parents without pulse feedback do not acquire this ability
on the tested port before later copies.

### What do settings add?

Pulses alone suffice for the two effects above. In C's fast stage, inherited settings
allow 23 responses to 25 inputs, versus 20/25 with pulses only. In this recording,
the uninterrupted response sequence starts at t=656 instead of t=668. This is one
deterministic scenario, not a general guarantee of faster learning.

No emissions occur after t=900 in any of the six runs, following the end of external
sources at 860. This does not establish stability for other delays, settings or durations.

## Scenarios and verification

Six configurations: pulses + settings, pulses only, settings only, no exchange,
pulses without feedback to parents, and pulses without plasticity.

All **55 numerical and structural checks** pass: parameter and reserve bounds,
cell persistence, monotonicity, causal pulse origins, copy conditions, relearning
probes, tighter solver tolerances, and independent replay of all three cells using
recorded arrivals from the pulses-only scenario.

The largest firing-time difference in these independent replays is 2.55e-11.
Simultaneous numerical events are grouped by tolerance; all weak event orderings
have not been certified. The observed reserve E stays above 98.89.

The interface was executed in a minimal DOM environment and its SVGs rendered at
widths 320, 390 and 736. A full browser was unavailable for automated inspection.
Verification records distinguish these checks.

## Limitations

R's gains and b only increase. There is no active forgetting or unlearning rule.
The four adjustable settings do not store arbitrary content. Schedules, sources
and transfers are orchestrated; spontaneous organization has not been established.
Long-term behavior, saturation and fabrication robustness require further experiments.

## Run again

The recorded runs used Python 3.12, NumPy 2.3.5 and SciPy 1.17.0. No native compilation
or repository access is required. From the extracted ZIP's main directory:

```sh
python -m pip install -r 02_R_Simulation/requirements.txt
python -u -B 02_R_Simulation/simulate.py --out 04_New_Results
python -u -B 02_R_Simulation/analyse.py --out 04_New_Results
python -u -B 02_R_Simulation/validate.py --out 04_New_Results
```

The supplied recordings remain in `04_Results`. To refresh the standalone viewer:

```sh
python 02_R_Simulation/make_viewer.py --results 04_New_Results --target 03_Visualization/NEW_FRAGMENT.html --standalone-template 03_Visualization/OPEN_IN_BROWSER.html --standalone-target 03_Visualization/NEW_REPLAY.html
```

The editable fragment is included. The supplied standalone page opens directly.
Historical machine identifiers are documented in `01_Guide/DATA_DICTIONARY.md`.

The two single-cell reference simulators originate from `HevisNico/a22-going-further`,
commit `269483eb2c6227b369cffb2c46f86eaae5272bb8`. The original MIT license is included.
These numerical checks are not a formal proof, an electronics experiment or a
validation of the complete parameter space.

## Further experiment: a learned teaching choice

The first reciprocal-network viewer remains in `03_Visualization`. The later
teaching-efficacy study is in `06_Learning_To_Teach`. The new, explicitly extended
architecture that learns a conditional curriculum choice is in
`07_Learned_Pedagogy`: open its `RESULTS.html` and read its `README.md` for the
boundary between the unchanged R kernel and added feedback/readout components.


The next stage is `08_Adaptive_Lessons`: a learned within-lesson stopping policy,
with causal native-R readout and two fresh learner lots. Its report separates
adaptation, a programmed-controller reference, and the still-unrun invention test.


`09_Certified_A_Learns_From_B` contains a local interval theorem from an explicit
prepared section, for ±0.3% and ±10% physical boxes. See its theorem for the
unproved earlier-history section-entry obligation; this does not certify the
whole reciprocal or adaptive prototype.


`10_Certified_Section_Entry` discharges that entry condition for the pulses-only
READY birth family and composes the local theorem from initialization through
459.9. The result does not include settings copies or later open recurrence.

`11_Certified_Cadence_Cascade` extends the pulses-only birth-family proof through
789.9. It covers C's introduction and the C->B->A fast feedback chain over all
45 per-port physical parameters at ±0.3% and ±10%, with independent wire jitter.
Each cell gains exactly 0.2 in b during the fast block. A's isolated frozen
period-4 probe improves from 4/8 to 8/8; cutting either reverse link leaves A
at 4/8. C's pulses-only baseline is 0/8 on its unused port 0, unlike the full
settings-copy baseline above. Settings copies and the open phase after 800
remain outside these new proofs.
