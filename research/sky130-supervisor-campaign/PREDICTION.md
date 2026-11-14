# SKY130 supervisor campaign: predictions

Written and pushed alone, before any implementation of the campaign: no
runner, no manifest, no analysis exists when this file is committed. Nothing
in it may be changed afterwards; a wrong rule is corrected by an amendment
file pushed before the run or the computation it concerns.

Everything here is a transistor-level simulation of the two-port R cell
(ngspice 42, SKY130 models), on netlists with the junction areas of stage J of
the layout study. There is no layout, no wire capacitance and no silicon.

## What is tested

A supervisor keeps the trained cell serving under a jump of its leakage. Each
port is watched and maintained by a kernel whose safety is proved in Lean
under explicit bounds
([`../sky130-supervisor-qualification/lean/Model.lean`](../sky130-supervisor-qualification/lean/Model.lean)).
The qualification measured those bounds on nine configurations
([`../sky130-supervisor-closure/README.md`](../sky130-supervisor-closure/README.md)).
This campaign asks whether, with these bounds, the services stay correct when
the leak jumps **inside** the proved domain; whether the kernel says so when
the leak jumps **outside** it; and what the same cell does **without**
supervisor under the same jump.

The headline is safety: no failed service under the jump, where the cell left
to refresh itself fails services (7 of 146 in the earlier campaign, about
5 %). Cost is secondary. **No energy claim of any kind is made.**

No leakage jump was simulated before this file was written: the
qualification used constant leaks only, and nothing below was tried.

## Decisions of the owner that this file applies

1. **Joint read window: P7, [0.250, 0.280].** It is a circuit
   specification. It is **outside the window of the proved model,
   (0.239, 0.256]**: the circuit reads near 0.267, and this campaign does not
   claim that the circuit verifies the model window.
2. **Bounds: version `k = 2`** of
   [`BOUNDS_JUNCTION.json`](../sky130-supervisor-closure/BOUNDS_JUNCTION.json)
   (SHA-256 `1d01ce86e1af8c3ceb1c2bdf415bff15445d45fe162e9b9ed3d3a1c58dcf7b70`):
   margins of 2 standard deviations of the measured noise.
3. **-40 C: a noise-free claim only, with version `k = 0`**; it is excluded
   from the noisy claim (no bounds with a noise margin exist there).
4. **Scope: 24 services per run, 62 runs per machine, two machines.**

## Definitions

**Deck.** `sim.deck(junction="areas")` of the qualification: the circuit of
`../circuit/cell.spice`, expanded, with the areas of
`../sky130-supervisor-closure/junction/areas.csv`; slot-by-slot stimulus; no
ammeter. Noise, when on, is the four calibrated sources of
`../circuit/noise.json`.

**Configurations.** In-domain: `tt27`, `ss27`, `ff27`, `sf27`, `fs27`,
`tt125`, `mm2001`, `mm2002` (as in
`../sky130-supervisor-closure/configs.json`), with the bounds of version 2.
`tt-40` with the bounds of version 0, without noise only.

**Run.** One simulator process. Slots of 220 us. Two idle slots, then the
**preparation**: one clock-only cycle per slot on each port that has its
headroom, until both ports hold an entry certificate, as in the
qualification (at most 40 slots; a run that does not enter is complete and
has no service). Then **24 service periods** of 440 us, numbered 0 to 23:
a maintenance slot, then a read slot. The reads cycle: port 1, port 2, both
(period `n` reads `n mod 3`).

**Kernel.** [`../sky130-supervisor-closure/kernel.py`](../sky130-supervisor-closure/kernel.py),
the mirror in exact integers of the Lean definitions (unit 0.1 uV), one per
port, with the bounds of that port.

**Observer.** Before each maintenance slot, for each port: the mean, over
the 40 us that ended 20 us earlier, of the stored node minus the summing
node; the reserve is the threshold of the port minus that voltage.

**Modes.**
- *supervised*: in each maintenance slot each port does what its kernel
  answers (`maintenance`: one clock-only cycle; `wait`: nothing). After a
  `refuse` on a port the run goes on to its 24th service with the rule of the
  preparation on that port; nothing is claimed after a refusal.
- *self-refresh*: the same preparation and entry, then no maintenance at all:
  every maintenance slot is idle. The kernel is not consulted.

**Leak.** A conductance `g` on the summing node of both ports. The reference
is `g0 = 1e-11 S` (1e11 ohm). Every run has `g0` during the preparation and
the periods 0 to 7, and its jump value from the maintenance slot of period 8
to the end. The new value is set after the observation of period 8: the
kernel is not told.

| Jump | Value from period 8 | Where it stands |
|---|---|---|
| inside | `3e-11 S` (3 times the reference) | below the largest leak of version 2 on every in-domain configuration (the smallest is 3.39 times the reference, at `ff27`) |
| inside, -40 C | `2e-11 S` | below the largest leak of version 0 at `tt-40` (2.43 times) |
| outside | `2e-10 S` (20 times) | loss of 1.15 to 1.37 mV per period, against `H` of 0.21 to 0.79 mV: 1.7 times `H` at `tt125`, at least 3.9 times elsewhere |

**Service.** The read of a service period. It is **correct** when the read
slot holds exactly one FIRE, with a latency in [0.5, 1.0] for a single read
and in [0.250, 0.280] for the joint read, and no write on either port.
Otherwise it is **failed**. Latency: from the start of the pulse to the
rise of the FIRE output through 0.9 V, in units of 20 us.

**Refusal.** The kernel of a port answers `refuse` at a period.

## Scenarios, split and order

Eleven scenarios, in this order:

`main-tt27`, `main-ss27`, `main-ff27`, `main-sf27`, `main-fs27`,
`main-tt125`, `main-mm2001`, `main-mm2002`, `quiet`, `outside`, `self`.

Each machine runs 62 runs: its run number `i` (0 to 61) belongs to scenario
number `i mod 11` of that list. Every prefix of a machine's list is therefore
balanced: the counts of two scenarios never differ by more than one. Machine
`a` and machine `b` have the same list of scenarios; they differ by their
seeds and by the configurations of the last three scenarios.

| Scenario | Mode | Noise | Jump | Configuration | Runs (a + b) |
|---|---|---|---|---|---|
| `main-<c>` | supervised | yes | inside | `<c>` | 6 + 6 for the first seven, 5 + 5 for `main-mm2002`: 94 |
| `quiet` | supervised | no | inside | occurrence `j` (0 to 4): on `a`, `tt27, ss27, ff27, sf27, fs27`; on `b`, `tt-40, tt125, mm2001, mm2002, tt27` | 5 + 5 |
| `outside` | supervised | no | outside | on `a`, `tt27, ss27, ff27, sf27, fs27`; on `b`, `tt125, mm2001, mm2002, tt27, ss27` | 5 + 5 |
| `self` | self-refresh | yes | inside | as `outside` | 5 + 5 |

124 runs, 2976 services at most. The `quiet` run at `tt-40` uses version 0
and the jump "inside, -40 C"; every other supervised run uses version 2.
The `self` runs use the bounds of version 2 for the preparation and the entry.

**Seeds.** Run `i` of machine `a` has number `10000 + i`, of machine `b`
`20000 + i`. On a configuration without mismatch the run issues `setseed`
with its number: measured in the qualification, this changes the noise and
nothing else. On `mm2001` and `mm2002` the `setseed` is the instance itself
(2001, 2002) and cannot change.

**The noise cannot be replayed.** ngspice 42 also seeds its noise from the
number of its process, which the launcher does not control (it refuses the
preloaded library that would). No run can be reproduced bit for bit, and a
lost run cannot be reconstructed. Each run records the fingerprint of the
noise it drew.

## Predictions

A prediction is evaluated on the complete runs that count (see the rules
below). "Every" means every such run.

**Main claim: supervised, with noise, jump inside (94 runs, 8 configurations).**

- **M1.** Every run enters service (both ports hold their entry certificate
  within the 40 slots of the preparation), and no kernel refuses, on either
  port, at any period.
- **M2.** Every service is correct.
- **M3.** Every clock-only cycle writes exactly one dose on the port it was
  commanded on and none on the other; no FIRE in a slot that is not a read.
- **M4.** At every period the reserve observed on each port lies in the
  interval `[lower, upper]` that its kernel computed for that period.

M2 is a statistical claim: noise is not a bounded error. If it holds on `n`
runs, the report states that no run of `n` had a failed service and gives the
one-sided 95 % Clopper-Pearson bound on the fraction of runs that would have
one, `1 - 0.05^(1/n)` (3.1 % for `n` = 94). Services of one run are not
independent and are not pooled into a rate per service. If M2 fails, the
report gives the failed services, the runs and the configurations as they are,
and the two-sided 95 % Clopper-Pearson interval of the fraction of runs with
a failed service.

**Deterministic claim: supervised, no noise, jump inside (9 configurations).**

- **Q1 to Q4.** As M1 to M4, on every `quiet` run.
- **Q5.** Every read happens with both reserves between `S` and the capacity
  of their port (the smaller of the two capacities of the bounds).
- **Q6.** The premises of the kernel hold in the run, from one observation to
  the next: on a port, a period without maintenance loses between 0 and `H`;
  a period with maintenance gains between `Dmin - H` and `Dmax`.

Here a single failure refutes the claim for its configuration: there is no
noise to appeal to.

**Control outside the boundary: supervised, no noise, jump outside.**

- **O1.** Every run enters service; periods 0 to 7: no refusal and eight
  correct services.
- **O2.** The kernels of both ports answer `refuse` at period 9, the first
  period whose observation follows one whole period at the new leak, in
  every run.
- Nothing is predicted about the services from period 8 on. They are reported.

O2 says that the guarantee is not kept silently outside its domain. It does
not say that the supervisor repairs anything.

**The cell without supervisor: self-refresh, with noise, jump inside.**

- **R1.** Every run has at least one failed service.
- **R2.** Over all these runs together, at least 5 % of the services failed.

**Comparison.** If M2, R1 and R2 hold, the report states: under the same
jump, the supervised cell failed no service in `n` runs, and the cell left to
itself failed `x` of `y` services. It states no more than that.

## Rules of the analysis

1. **One analysis, at the end.** The analysis script is frozen with the
   implementation, before the launch. It is run once, on the evidence of the
   two machines, after both have ended. No count is looked at while a machine
   is running.
2. **Which runs count.** A run counts when the launcher recorded it
   `complete` and its own record says that it ended at the last slot of its
   plan. A run that failed, reached its time limit or was lost at a restart
   is a **missing run**: it is listed with its status, it is neither a
   success nor a failure, and it is never replaced or run again.
3. **Truncated campaign.** Each prediction is evaluated on the runs that
   count, whatever their number, provided there are enough:
   M1 to M4 need at least 40 runs; Q1 to Q6 are stated per configuration and
   need the run of that configuration (the claim "on the nine configurations"
   needs the nine); O1, O2 and R1, R2 need at least 5 runs each. Below these
   numbers the prediction is reported **not established**, not held and not
   failed. No prediction is re-scoped after the data are seen.
4. **Shared noise.** Before any count, the fingerprints of all noisy runs
   that count are compared. Of several runs with the same fingerprint, the
   first in the order of the manifest (machine `a` before machine `b`) is
   kept; the others are listed as duplicates and do not count.
5. **Failures are reported as they are.** A failed prediction is written
   "fails" with its numbers. Nothing is adjusted, removed or explained away.
6. **Preparation is not service.** Clock-only cycles and silences before the
   entry are counted and reported, never as services.

## Execution

- **Executor.** A Claude Code cloud session on behalf of the owner, on two
  cloud containers whose inventories are recorded.
- **Launcher.** The second launch kit,
  [`../sky130-supervisor-closure/launchkit/launch.py`](../sky130-supervisor-closure/launchkit/launch.py),
  frozen by hash in the manifest with every runner, deck source, bound file
  and analysis file. The attempt marker RUN_ATTEMPT.json covers both
  machines and is pushed, with the CI state of the implementation head it
  observed, before any launch. One launch per machine; a claimed machine is
  never launched again.
- **Environment, identical on both machines and checked by the launcher:**
  ngspice 42 (SHA-256 `820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45`),
  PDK commit `1232782c1b9fab3aacda74d67ce7c92bf7da8105`, Python 3.12.3
  (`e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f`),
  numpy 2.3.5 (`064003bdb6f9f7bb06e46e07cc3398cbfdc3c114dfe55b89d239e564917be2fb`).
  The simulator start file is the committed
  `../sky130-supervisor-closure/runtime/spinit`, given by the launcher.
- **Budget.** Four runs at a time on each machine. Every run: estimate 280 s,
  time limit 420 s. The bound of the launcher is 7095 s per machine,
  14 190 s for the two, under the 14 400 s (4 h) allowed. A run that reaches
  its time limit is a missing run.
- **Resume.** If a container restarts, its runs that had never started
  proceed; a run that had started and not ended is recorded lost and is never
  run again. Nothing else allows a resume.
- **Evidence.** Each run writes its deck, the log of the simulator session
  (every command sent and every answer), a waveform of the first 30 us with
  the noise sources, the waveform of the whole run with the vectors the
  analysis needs (FIRE output, stored node, summing node and write node of
  each port), its record and its fingerprint. Every surviving file is
  collected byte for byte with its SHA-256. The decks, logs, records,
  fingerprints, the small waveforms and the SHA-256 list of everything are
  committed to this repository. The waveforms of the whole runs, about
  1.7 GB, cannot be committed here nor attached to a release from the
  session: they are committed unchanged to the private repository
  `HevisNico/kernel-R-circuit`, and their SHA-256 are in the public list.
  The report is generated by the analysis script and committed as generated.

## What this campaign cannot show

- Nothing about silicon, a layout, wire capacitance, or a real observer: the
  observer reads two node voltages of the simulation.
- Nothing outside the nine configurations, between the three temperatures,
  or for a leak that is not a conductance on the summing node.
- Nothing about the model window (0.239, 0.256] of the joint read.
- Under noise, a count of runs without failure, with its bound; not a proof
  and not a rate per service.
- At -40 C, nothing under noise.
- Nothing about energy.
