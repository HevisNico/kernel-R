# Periodic ring of R cells: predictions

Written and pushed alone, before any implementation of the campaign: no
runner, no manifest, no analysis exists when this file is committed. Nothing
in it may be changed afterwards; a wrong rule is corrected by an amendment
file pushed before the run or the computation it concerns.

Everything here is a transistor-level simulation (ngspice 42, SKY130
models) of three R cells of [`../circuit/cell.spice`](../circuit/cell.spice),
with the junction areas of stage J of the layout study, joined by an ideal
router outside the simulator. There is no layout of a network, no wire
between the cells and no silicon. The circuit does not verify the proved
read window, and nothing here says that it does.

## What is tested

A periodic ring of three cells learns: a root launches one pulse per lap,
each port takes doses until it fires and then passes the pulse on, and the
return port of the root trains and afterwards only acknowledges. The ring
model of [`../network-circuit-ring/RingNetwork.lean`](../network-circuit-ring/RingNetwork.lean)
(phase 0, pull request 165) says what each port learns when its reads have
room for their error, for every N and in any order of service:
`ring_port_shaped` (the port's own reads have room) and `ring_words` (the
reads of every port up to it have room). The model takes, per port, numbers
measured on that port alone.

This campaign asks whether, on cells with mismatch that no one has looked
at, **the learned state of the ring is the one computed beforehand from
those per-port measures**.

The primary claim is deterministic: one run without noise per eligible
instance, one discrepancy refutes it. A claim under the simulator's noise is
made per port, at `K = 3`, on two levels; one failing port-run refutes the
level it belongs to.

## Decisions of the owner that this file applies

1. **N = 3**, no second size. Six new instances, seeds 7301 to 7306. No
   development instance is reused. If no instance is eligible the primary
   claim is "not established", with no extra draw.
2. **Size F3s.** Per measured instance: one run without noise and three
   shortened noisy runs; one control run. The owner counts the 4 h as
   expected machine time: 218 minutes expected for the two machines and the
   two stages. **The kit budget, the time if every run took its whole
   limit, is 19 200 s in the worst case, above 4 h; the owner accepted
   this.** On every machine the runs without noise and the control come
   first and the noisy runs last, so that an overrun can only cost noisy
   runs. A noisy run that reaches its limit is a missing run, never
   replaced.
3. **Noise constants fixed beforehand**: 0.090 mV between runs, 0.064 mV
   within a run, 0.009 mV per dose. This is a departure from "computed from
   the measures" and it applies to the noisy budget only; the noise-free
   budget stays computed from the measures.
4. **Shortened noisy runs**: three laps after the predicted freeze.
5. **Two levels of the noisy claim**, N-own (`ring_port_shaped`) and N-word
   (`ring_words`), each refuted by one failing port-run. A port-run with
   fewer than `need` pulses does not count for N-own, and the number of such
   port-runs is reported.
6. **The control** is run on the eligible instance whose return port has the
   smallest margin of its last silence; its result on the nominal cell is
   stated below, in advance.
7. **Per-instance laps** are fixed by the measures before the network stage,
   as in campaign 1.
8. **Waveforms above 100 MiB** are split into parts below 95 MB, with the
   SHA-256 of every part and of the whole file, and published on an evidence
   branch after the campaign.
9. **The noise model is unchanged.** It overstates the low-frequency noise
   of the integrator amplifier
   ([`../network-circuit/phase1/NOISE.md`](../network-circuit/phase1/NOISE.md)).
   The claim under noise is a claim about the simulator with this noise
   model, not about the noise of a fabricated cell; a study with an
   independent noise model stays deferred.
10. One launch per machine and per stage; two machines; at most one machine
    `b` for the campaign.

## What was run before this file

- Campaign 1 ([`../network-circuit-campaign`](../network-circuit-campaign)):
  two-cell networks, instances 7201 to 7206; phase 1: development instances
  7101, 7102, 7103. None of them is used here.
- Phase 0 of this campaign
  ([`../network-circuit-ring`](../network-circuit-ring/README.md),
  [`REHEARSAL.json`](../network-circuit-ring/REHEARSAL.json)), on the
  **nominal cell** only (model section `tt`, no mismatch, no seed): the ring
  of 26 laps without noise and with noise, the control with a return 8 units
  and 10 units after the launch, a scan of one port on the deck of three
  cells, the train of 10 reads per port without noise and with noise; a scan
  on the deck of six cells. A ring of six cells was stopped unfinished; it
  has no record.

Nothing was ever simulated with the seeds 7301 to 7306. No ring was ever
run on a cell with mismatch.

## Definitions

**Time unit.** 20 us, the length of a pulse.

**Instance.** One deck with three cells, `a` (the root), `b` and `c` (the
relays): `net.deck` of `../network-circuit/net.py` with the model section
`tt_mm`, 27 C, the junction areas of stage J, and the simulator command
`setseed` with the seed of the instance before the deck is read, which fixes
its mismatch sample. Six instances: seeds **7301, 7302, 7303** (machine `a`)
and **7304, 7305, 7306** (machine `b`). Each instance is measured and run on
its machine.

**Ports**, in the order a pulse meets them (`ring.ports(3)`):

| Index `k` | Port | Cell | Receives |
|---|---|---|---|
| 0 | `a1` | root | the launch: one external pulse per lap |
| 1 | `b1` | first relay | the wire from the root |
| 2 | `c1` | second relay | the wire from `b` |
| 3 | `a2` | root | the return wire from `c` |

Ports `b2` and `c2` are never pulsed: the **unused ports**.

**Stored voltage `u`** of a port: stored node minus summing node, in mV. A
more negative `u` is a higher gain.

**Word** of a port in a run: one letter per pulse addressed to the port, in
the order of the dates. `s`: no FIRE of the cell from the start of the pulse
to one unit and 2 us later, and exactly one write on that port during the
cycle of the pulse. `F`: one FIRE in that window and no write. Any other
pulse (refused by the router, not delivered, arriving while the cell is
protected, a FIRE with a write, neither a FIRE nor a write) gets its own
letter and is neither `s` nor `F`. FIRE: the protection latch of the cell
rises through 0.9 V. Write: the write signal of the port rises through
0.9 V. The writes of a port are its number of `s`; the pulses it receives
are the letters of its word.

**Lap** of a pulse: `floor(d / P) + 1`, where `d` is the start of the pulse
in units after date 0 and `P` the period of the calendar.

### Measures, each port alone

Per instance, with the scripts of `../network-circuit/phase1` and
`../network-circuit-ring/ring.py` as they are when the implementation is
frozen, every run pulsing one port at a time with the others idle:

1. **Scan** of each of the four ports `a1`, `b1`, `c1`, `a2`
   (`cellscan.py`, no noise, its list of cells set to `a`, `b`, `c`):
   training reads 22 units apart, one read 16 units after a FIRE, bisection
   of the threshold. Four runs.
2. **Train without noise** (`ring.train(3, 10)`: 10 reads per port 18 units
   apart, the relays 2 and 4 units after the root). One run.

No noisy train is run: the noise constants are fixed (decision 3).

The function `port` of `constants.py` gives, per port, from its scan and its
train: the preset, the threshold, the half bracket of the threshold, the
dose, the gap from the preset to the threshold, the help at 16 units after a
FIRE and at 18 units after a silence and after a FIRE. The function
`instance` of `constants.py` is not used: it needs noisy trains.

An instance is **measured** when its five runs count and `port` yields the
constants of its four ports. Otherwise it is **not measured**: it has no
prediction, gets no network run, and enters no claim. A scan that gives no
threshold (campaign 1, instance 7206, port `a2`) leaves its instance not
measured.

### The model and the two budgets

Integers, as in `CircuitNetwork.lean` and `RingNetwork.lean`: one dose of a
port is 100 000 units, the gap of a port is `round(gap / dose x 100 000)`.
The **need** of a port is the least `n >= 0` with `n x 100 000 >= gap`.
With `S_k = need_0 + ... + need_k` (and `S_-1 = 0`), the **zero-error word**
of port `k` on a ring of `L` laps is `need_k` letters `s` then
`L - S_k` letters `F` when the ports before it let `L - S_(k-1) >= need_k`
pulses through; in general it is `min(need_k, m)` letters `s` then
`m - need_k` letters `F`, with `m` the pulses the ports before it let
through (`arriving` of `RingNetwork.lean`, `ring.zero_error`).

**Noise-free budget**, per port, in mV, as in campaign 1:

    hi = + max(0, help at 16, help at 18 after a silence, help at 18 after a FIRE) + 0.030 + half bracket
    lo = - (0.015 + 0.030 + half bracket)

0.015 mV is what a pulse 22 units earlier adds over a long silence (phase 0
of campaign 1); 0.030 mV is the allowance for the simulator itself.

**Noisy budget, `K = 3`**, per port, in mV, with the fixed constants:

    noise = sqrt(0.064^2 + 0.090^2 + need x 0.009^2)
    hi = + max(0, the three helps) + 3 x noise + half bracket
    lo = - (0.015 + 3 x noise + half bracket)

Budgets become integers in units of 1/100 000 dose by rounding away from
zero (`lo` down, `hi` up).

**Own room.** A port has own room under a budget when `Own gap d lo hi k
need` of `RingNetwork.lean` holds (`d = 100 000`): its `need` silent reads
stay silent under `hi`, the read after them is a FIRE under `lo`. **Room up
to port `k`**: every port `j <= k` has own room.

An instance is **eligible** when it is measured and its four ports have own
room under the noise-free budget.

**Margin of the last silence** of a port, in mV: `(gap - (need - 1) x
100 000)` units, times the dose of the port divided by 100 000. A port with
`need = 0` has no last silence.

### Calendars

**The ring** (`ring.ring(3, L)`): a launch on `a1` at dates `0, 37, ...,
37 (L - 1)`; every wire has the delay 17/3 units; a FIRE of the root is
carried to `b1` only if it rises within 2 units after a launch date, one
edge per lap; a FIRE of `b` goes to `c1`, a FIRE of `c` to `a2`; a FIRE of
the root on `a2` goes nowhere. The router refuses and records any pulse
that would start less than 16 units after the previous pulse of its cell, or
while its cell is protected (guard 16). With FIRE latencies from 0 to 1.06
unit, two pulses of one cell are at least 16.74 units apart by construction
(`ring.separation`, `ring.holds_by_construction`).

**The control** (`ring.control(3, L)`): the same with every wire delay
1.767 units and a period of 19 units, so that the return pulse starts about
8 units after the launch (for latencies near 0.9 unit), the spacing of the
control of campaign 1; the pulses of each relay stay 16 units apart. Played
without the guard. It leaves the timing condition on the root only.

**Laps.** For a measured instance with needs summing to `S_3`:
`L = S_3 + 10` for its run without noise and for the control;
`L' = S_3 + 3` for its noisy runs. Fixed in `PREDICTED.json` before any
network run.

## Order of the campaign

1. **Measures.** Each machine measures its three instances.
2. **Predictions.** From the collected measures of both machines, the frozen
   scripts write `PREDICTED.json`: per instance, whether it is measured, its
   constants, the integers of both budgets, the need of each port, which
   ports have own room under each budget, whether it is eligible, its laps,
   its zero-error words for `L` and for `L'`, the control instance, and the
   list of network runs with their limits. The same per-port statements are
   written as a Lean file, one `Own ... := by decide +kernel` or
   `¬ Own ... := by decide +kernel` per port and budget, and checked by the
   Lean kernel. **`PREDICTED.json` is committed and pushed before any
   network run**, and the launcher of the network runs is bound to its
   SHA-256.
3. **Network runs**, on the machine that measured the instance, in this
   order on each machine:
   - `quiet`: one run of `ring.ring(3, L)` without noise, for every
     measured instance, in the order of the seeds;
   - `control`: one run of `ring.control(3, L)` without noise, on the
     control instance, on its machine;
   - `noisy`: three runs of `ring.ring(3, L')` with the simulator's noise,
     for every measured instance: first the first noisy run of each
     instance in the order of the seeds, then the second of each, then the
     third.
4. **One analysis**, after both machines have ended.

If the Lean check of step 2 fails, or disagrees with `PREDICTED.json`, no
network run is launched and the campaign ends there, reported as it is.

**Control instance.** Among the eligible instances whose return port `a2`
has `need >= 1`, the one whose `a2` has the smallest margin of its last
silence; the lowest seed in case of a tie. None if there is no such
instance.

## Predictions

**Primary claim: the learned state without noise.** For every eligible
instance, in its `quiet` run:

- **P1, words.** The word of each port `k` is its zero-error word for `L`
  laps: `need_k` letters `s` then `L - S_k` letters `F`. In particular the
  return port receives 10 pulses after its last write, and port `k`
  receives `L - S_k` after its last write.
- **P2, lap of the freeze.** The last write of the ring is at lap `S_3`,
  and port `k` receives its first pulse at lap `S_(k-1) + 1`.

The primary claim is refuted by one port of one eligible instance whose word
differs from P1, or one eligible instance whose laps differ from P2. There
is no noise to appeal to, and a run without noise can be made again by
anyone: it gives the same waveform.

**Reported with the primary claim, never refuting it.** In the `quiet` runs
of the eligible instances:

- **H, the hypotheses, observed.** The guard refuses no pulse; no pulse
  arrives on a protected cell; every pulse is delivered; nothing is left in
  the queue at the horizon; two pulses of one cell are never less than 16
  units apart; every FIRE of the root on `a1` is carried to `b1` and no FIRE
  on `a2` is carried anywhere; every `s` moves the stored voltage of its
  port by its measured dose within 0.01 mV; between two pulses of a port,
  and across each of its pulses that is not an `s`, its stored voltage moves
  by at most 0.01 mV; the waveform reaches the horizon.
- **P4, final stored values.** The stored voltage of port `k` at the
  horizon (mean over the 28 us that end 2 us before it) is within
  `(2 n + 1) x 0.01` mV of its value at the start of the run (mean over the
  35 us that end 5 us before date 0) minus its writes times its measured
  dose, where `n` is the number of pulses it received; each unused port
  ends within 0.01 mV of its value at the start of the run.

If H fails in a run, P1 and P2 are still evaluated on it and the failure is
reported: the run left the conditions under which the prediction was made.
P4 holds or fails on its own and does not touch P1 or P2.

**The claim under noise, per port, at `K = 3`.** Over every measured
instance and every noisy run that counts:

- **N-own** (`ring_port_shaped`). A port with own room under the noisy
  budget, in a noisy run in which it receives at least `need` pulses, has a
  word made of exactly `need` letters `s` followed only by letters `F`: it
  makes exactly its predicted writes, all before its first FIRE. Its number
  of FIRE depends on the ports before it and is not claimed. A port-run in
  which the port receives fewer than `need` pulses does not count; the
  number of such port-runs is reported.
- **N-word** (`ring_words`). A port with room up to it under the noisy
  budget reads exactly its zero-error word for `L'` laps.

Each level is refuted by one port-run that fails it. Each needs at least
one port-run that counts; with none it is **not established**.

**Negative control, on the control instance.**

- **C.** In the `control` run, the return port `a2` fires earlier than its
  zero-error word for `L` laps: its word begins with fewer than `need_3`
  letters `s` before its first `F`.

The other three ports are expected to keep their zero-error words: the
launch port has made its writes before any return pulse exists, the relays
keep 19 units between their pulses, and the help of a recent pulse can only
bring a FIRE forward. The report gives the four words. **Stated in advance:
on the nominal cell C fails.** In the rehearsal of phase 0 the control gave
the four zero-error words; the last silences of the nominal cell hold by
0.80 mV. C fails on an instance whose return port keeps its last silence
against the help of a pulse 8 units earlier, which this campaign does not
measure. If C fails, the control showed nothing on that instance; it does
not touch P1, P2 or the claim under noise.

**Declared comparisons, not claims.** Reported as counts, with no "holds"
or "fails":

- **M1.** Ports without own room under the noisy budget, in the noisy runs:
  how many port-runs have the zero-error word, and how many the predicted
  writes.
- **M2.** Ports with own room but not room up to them under the noisy
  budget, in the noisy runs: how many port-runs have the zero-error word.
- **M3.** The `quiet` run of each measured instance that is not eligible,
  against its zero-error words, per port, with whether the port has own
  room and room up to it under the noise-free budget.
- **M4.** The nominal predictor, which ignores the measures and gives every
  port a need of 4: for each eligible instance, the number of ports whose
  zero-error word differs from the nominal word for its `L`; for each
  `quiet` run that counts, the number of ports whose word differs from it.
  If the first number is 0 for every eligible instance, P1 cannot tell the
  measured predictor from the nominal one, and the report says so.
- **M5.** The offset and the scatter of the FIRE latency of each port in
  each noisy run, against the latencies of the `quiet` run, converted to mV
  with the slope of its train: against the fixed constants 0.090 and
  0.064 mV.
- **M6.** H and P4 on the runs where they are not reported above: the
  `quiet` runs of the instances that are not eligible, and the noisy runs.

## Rules of the analysis

1. **One analysis, at the end.** The analysis script is frozen with the
   implementation. It is run once, on the evidence of the two machines,
   after both have ended their network runs. No word of a network run is
   looked at while a machine is running: only the statuses of the
   launcher.
2. **The predictions are those of the measures.** The analysis first checks
   that `PREDICTED.json` is what the frozen prediction script gives from
   the evidence of the measures, and writes the answer at the top of the
   report. If the answer is no, every claim is reported "not established",
   whatever the counts.
3. **Which runs count.** A run counts when the launcher recorded it
   `complete` and its own record says that it reached its last date. A run
   that failed, reached its time limit or was lost at a restart is a
   **missing run**: listed with its status, neither a success nor a
   failure, never replaced and never run again.
4. **Missing measures.** An instance with a missing measure run is not
   measured.
5. **Missing network runs.** P1 and P2 are evaluated on the eligible
   instances whose `quiet` run counts; an eligible instance whose `quiet`
   run is missing is listed as not tested. The primary claim needs at least
   one tested eligible instance; with none it is **not established**. C
   needs its run; without it, or without a control instance, it is not
   established. A missing noisy run removes its port-runs; nothing replaces
   them.
6. **No re-scoping.** The eligible instances, the needs, the ports with own
   room and with room up to them, the laps and the control instance are
   those of `PREDICTED.json`, fixed before the network runs.
7. **Shared noise.** The noise fingerprints of the noisy runs of one
   instance are compared. Of several runs with the same fingerprint the
   first in the order of the manifest is kept; the others are listed as
   duplicates and enter no count.
8. **Failures are reported as they are.** A failed prediction is written
   "fails" with its words. Nothing is adjusted, removed or explained away.

## Execution

- **Executor.** A Claude Code cloud session on behalf of the owner, on two
  cloud containers whose inventories are recorded. Machine `b` is a new
  session created for this campaign.
- **Launcher.** The second launch kit,
  [`../sky130-supervisor-closure/launchkit/launch.py`](../sky130-supervisor-closure/launchkit/launch.py),
  unchanged, used twice: for the measures with this file as its protocol,
  then for the network runs with `PREDICTED.json` as its protocol. Each
  launch has its manifest, with every runner, deck source and analysis file
  frozen by hash, and its attempt marker pushed before the launch with the
  state of the CI on the exact source commit. One launch per machine and
  per stage; a claimed machine is never launched again for that stage.
- **Environment, identical on both machines and checked by the launcher:**
  ngspice 42 (SHA-256 `820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45`),
  PDK commit `1232782c1b9fab3aacda74d67ce7c92bf7da8105`, Python 3.12.3
  (`e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f`),
  numpy 2.3.5 (`064003bdb6f9f7bb06e46e07cc3398cbfdc3c114dfe55b89d239e564917be2fb`).
- **Four runs at a time** on each machine.
- **Time limits.** Measures: a scan 410 s, the train 730 s. Network runs:
  per run, from the cost model of phase 0
  ([`cost.py`](../network-circuit-ring/cost.py)), fitted on the rehearsal:

      expected = 3 x (3.7746 s x simulated ms + 3.9820 s x pulses) x (1.3861 if the run has noise)
      limit    = 1.3 x expected, rounded up to 10 s

  with the simulated time of its calendar and the pulses of the zero-error
  words of its instance for its laps. The launcher's estimate of a run is
  its expected time rounded up to 10 s.

  | Run | Expected (phase 0, needs of 4.3 on average) | Limit at 5 doses per port |
  |---|---|---|
  | scan of one port | 313 s | 410 s |
  | train, no noise | 561 s | 730 s |
  | run without noise | 1 263 s | 1 730 s |
  | control | 1 151 s | 1 570 s |
  | noisy run, three laps after the freeze | 1 206 s | 1 680 s |

- **Budget.** The bound of the launcher, per machine and stage, is the sum
  of (limit + 10 s) divided by four, plus the largest (limit + 10 s); it
  must be at most 14 400 s per manifest, for the two machines together. At
  five doses per port: 5 110 s for the measures, 14 090 s for the network
  runs, 19 200 s in all. Expected, with the needs of campaign 1: 218
  minutes for the two machines and the two stages. If the network runs of
  `PREDICTED.json` would exceed 14 400 s for the two machines together, the
  last noisy run of the machine whose bound is the larger (machine `a` if
  equal) is removed, again and again, until they fit; the removed runs are
  listed in `PREDICTED.json` as not run for the budget, enter no count, and
  are not missing runs.
- **Resume.** If a container restarts, its runs that had never started
  proceed; a run that had started and not ended is recorded lost and is
  never run again. Nothing else allows a resume.
- **Noise cannot be replayed.** ngspice seeds its noise from the number of
  its process; each run is its own process. The noisy runs of an instance
  differ by that number only; each records the fingerprint of the noise it
  drew. A run without noise gives the same waveform when made again.
- **Evidence.** Each run writes its deck, the log of the simulator session,
  its waveform, its record and its noise fingerprint. Every surviving file
  is collected byte for byte with its SHA-256. Decks, logs, records,
  fingerprints and the SHA-256 lists are committed to this repository. The
  waveforms go unchanged to the private repository
  `HevisNico/kernel-R-circuit` during the campaign, and after the one
  analysis to an evidence branch of this repository with no shared history.
  A waveform above 100 MiB is stored as consecutive parts of 90 000 000
  bytes (the last one shorter), whose concatenation in order is the file;
  the SHA-256 of every part and of the whole file is recorded, and both are
  checked before and after each push. The report is generated by the
  analysis script and committed as generated.

## What this campaign cannot show

- Nothing about silicon, a layout, wires between cells or a real router:
  the cells are transistors, the router is ideal, and each pulse is the
  canonical pulse whatever caused it.
- Nothing about the noise of a fabricated cell. The claim under noise holds
  for the simulator's noise model, which overstates the low-frequency noise
  of the integrator amplifier, with noise constants fixed beforehand rather
  than measured on each instance.
- Nothing about the native periodic ring of
  `NativePeriodicRingTarget.lean`: the circuit ring departs from that class
  in the ten ways listed in phase 0 (doses per port, the launch and return
  ports, timing, router, cell, frozen value, cells from the start, noise,
  finite prefix), and this campaign does not refine it.
- Nothing about ports without own room: they are run and reported.
- Nothing outside 27 C, the typical corner with mismatch, three cells, one
  calendar of each kind, six instances.
- Nothing about a ring whose pulses come closer than 16 units on a cell,
  beyond the one control run.
- The per-port measures are made on the deck of the ring, by the same
  simulator. The claim is that the ring does what its ports, measured alone,
  say it will; not that the measures could be made on a chip.
