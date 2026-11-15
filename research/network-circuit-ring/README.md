# Periodic ring of R cells at transistor level: campaign 2, phase 0

**Status: design only, for review.** Nothing here is preregistered and no
`PREDICTION.md` exists. No simulation has been run on a new instance: the seeds
7301 to 7306 have not been used. The rehearsal ran on the **nominal cell**
(model section `tt`, no mismatch, no seed), which is not an instance. The
circuit, the simulator and its noise model are unchanged.

The owner wants the release to show proof and measurement on the same family
of networks. The one-token ring is proved for every N in
[#161](https://github.com/HevisNico/kernel-R/pull/161), and the periodic ring
is specified in [#163](https://github.com/HevisNico/kernel-R/pull/163): a root
launches periodically, each relay takes doses until it transmits, then the
return port trains and afterwards only acknowledges; the memory is frozen
while pulses keep arriving. Campaign 2 asks whether that protocol, played by
three circuit cells with mismatch that no one has looked at, ends in the state
computed beforehand from measures made on each port alone. The size is fixed
by the owner: **N = 3**, six new instances.

| File | What it is |
|---|---|
| [`ring.py`](ring.py) | the ports, the calendar that the unchanged router plays, the control, the model |
| [`RingNetwork.lean`](RingNetwork.lean) | the ring as an instance of the guarded model, for every N; what each port learns |
| [`check.sh`](check.sh), [`Audit.lean`](Audit.lean) | compile it with the pinned Lean, warnings as errors, and audit the axioms |
| [`rehearse.py`](rehearse.py), [`REHEARSAL.json`](REHEARSAL.json) | the rehearsal on the nominal cell and its record |
| [`cost.py`](cost.py), [`COST.json`](COST.json) | the cost of each option, from the wall times of the rehearsal |
| [`test_ring.py`](test_ring.py) | checks without a simulator; run by `.github/workflows/network-circuit-ring.yml` |

The bench is that of [`../network-circuit`](../network-circuit/README.md)
(`net.py`, `router.py`, `measure.py`, `phase1/cellscan.py`), used without any
change.

## 1. The network and its calendar

Three cells in one deck: `a` is the root, `b` and `c` are the relays. Four
ports carry pulses, in the order a pulse meets them:

| Port | Cell | Receives |
|---|---|---|
| 0, `a1` | root | the launch: one external pulse per lap |
| 1, `b1` | first relay | the wire from the root |
| 2, `c1` | second relay | the wire from `b` |
| 3, `a2` | root | the return wire from `c` |

Port 2 of each relay is never pulsed and keeps its preset. A FIRE of a relay
is always carried to the next port. A FIRE of the root is carried to `b` only
if it rises within 2 units of a launch date: one edge per lap, each with its
own date band. A FIRE of the root on its return port falls outside every band
and goes nowhere: the return port only acknowledges.

Times in units of 20 us, as everywhere in the bench:

| | N = 3 | Rule (`ring.py`, every N) |
|---|---|---|
| Wire delay | 5.667 | 17 / N: the return pulse starts at least 17 units after the launch |
| Latest return of a lap | 20.26 after the launch | 17 + 0.02 + N x 1.08: FIRE latency up to 1.06 unit, a pulse up to 0.02 unit late |
| Period | 37 | the next launch at least 16.5 units after the latest return, rounded up |
| Two pulses of the root | 16.74 apart at least | whatever the latencies |
| Two pulses of a relay | 34.82 apart at least | one pulse per lap |
| Router guard | 16 | refuses, and records, a pulse sooner after the previous pulse of its cell, or on a protected cell |
| Laps | sum of the predicted needs + 10 | ten laps after the predicted freeze |

Every lap is settled before the next one starts: the last pulse of a lap
starts at most 20.26 units after its launch, a port is busy 6.2 units and a
cell is protected at most 6.4 units after a firing pulse. The separation of
16 units is the condition under which the constants of phase 1 hold; it is
guaranteed by the calendar, and the guard is there to show it: a refusal in a
run inside the condition would be a failure of the hypotheses, reported as
such.

**The negative control** (`ring.control`) leaves the timing condition on the
root only. The wires are shortened so that the return pulse starts about 8
units after the launch (wire delay 1.767, for the FIRE latencies of 0.87 to
0.92 unit seen on the nominal cell), the spacing of the control of campaign 1;
the period (19) keeps the pulses of each relay 16 units apart. It is played
without the guard.

### Departures from the native class

The native periodic ring is `NativePeriodicRingTarget.lean` of #163. The
circuit ring is not in that class, and this campaign does not refine it:

1. **Doses per port.** The native class allows at most 2 doses per port. A
   circuit port needs what its mismatch gives: 3 to 6 doses on the 20 ports
   of campaign 1, 4 on the nominal cell. The need is measured, not chosen.
2. **The launch port.** The native root launches from the first lap (no dose
   on port 0). The launch port of the circuit root is a port like the others
   and needs its 3 to 6 doses: the first laps launch nothing.
3. **The return port.** The native class asks for at least one dose there.
   The circuit asks for nothing: a return port that needs no dose would be
   read as such.
4. **Timing.** Native delays are in [8, 9] and the period exceeds 10 (N + 1).
   Here the only condition is 16 units between two pulses of one cell: wire
   delays of 17 / N, a period of 37 for N = 3.
5. **The router.** It is ideal and outside the simulator: it sees the
   protection latch rise, and starts a standard pulse on the next port after
   the delay. The native root routes within one unit of a launch date; here
   within 2 units, because a FIRE can rise up to 1.06 unit after the start of
   its pulse.
6. **The cell.** Gain only: no MARK, no recovery memory, no FAST and SLOW
   phases. The protection latch is the cell's own.
7. **The frozen value.** Native: prepared + 3/5 x writes. Circuit: preset
   minus need x dose, in mV, with the dose measured on each port.
8. **The cells exist from the start**, and one mismatch seed gives the three
   cells of an instance.
9. **Noise.** The native class has none. The simulator's noise is Gaussian and
   unbounded: a budget at K = 3 is not a bound.
10. **Finite prefix.** A run has a fixed number of launches.

The circuit never verifies the proved read window, and nothing here says so.

## 2. The Lean instance, for every N

[`RingNetwork.lean`](RingNetwork.lean) builds on `CircuitNetwork.lean` and
`DatedOrder.lean` of campaign 1, which it does not change. No `sorry`, no
axiom beyond `propext`, `Classical.choice`, `Quot.sound` (`Audit.lean`).

**The model.** `ring N gap`: `N + 1` ports; a pulse is named by its port;
`score = - gap + d x writes`, FIRE iff `0 <= score + error`; a FIRE of port
`k < N` sends one pulse to port `k + 1`; `launches N laps` is the finite
prefix of the periodic calendar.

**The certificate** (`certificate`, `ring_certified`, `ring_predicted`), for
every N, gap and number of laps: the instance satisfies
`AutonomousFeedback.certified_feedback`, as the two-cell network does. No
port has more than `laps` writes; the queue is empty after `laps x (N + 1)`
reads whatever the errors; with room on every read, the run with errors is
the zero-error run.

**What each port learns, port by port.** On the ring every pulse that waits
on a port is the same probe (every launch is routed), so the order of service
does not matter. Campaign 1 needed a lemma on the order of the dates and the
absence of ties; the ring needs none. The theorems hold for any run that
serves one pending pulse at a time, in any order, with each error inside the
budget of the port read:

- `Own gap d lo hi k n`: port `k` needs `n` doses and each of its reads has
  room: its `n` silent reads stay silent under the largest error, the read
  after them is a FIRE under the smallest. Decidable: the per-instance check.
- `ring_port_shaped` (**own room**): a port with `Own` has read silent reads
  then FIRE, has at most `n` writes, and exactly `n` once it has fired,
  whatever the other ports did.
- `ring_words` (**room up to the port**): if every port up to `k` has `Own`
  and the run ends with nothing pending, port `k` has `min (need k) m` writes
  and its reads are these silent reads then `m - need k` FIRE, where `m` is
  the number of pulses the ports before it let through (`arriving`). Nothing
  is asked of the ports after `k`.
- `ring_dated_words`: the same for runs in the order of the dates, where two
  pulses with one date may be served either way; `ring_queue_words`: the same
  for the queue of the guarded model, which gives the zero-error words in
  closed form.
- `nominal_own`, `nominal_ring`: for every N, every port of the nominal ring
  needs four doses with room for the budget of `CircuitNetwork.lean`, ends
  with four writes, and port `k` has fired `laps - 4 (k + 1)` times: the ring
  is frozen from lap `4 (N + 1)` on. The kernel also checks `PortMargins` on
  the queue run for N = 3 (26 laps) and N = 6 (38 laps).

**From the constants to the words.** For an instance, the prediction step
would write, as campaign 1 did, the integers of each port (gap and bounds in
units of 1/100000 dose) and one line per port, `Own gap d lo hi k need := by
decide +kernel`. `ring_words` then gives the zero-error word of every port
whose predecessors have room, and `ring_port_shaped` the writes of a port
that has room alone.

**What Lean does not carry.** The lap of each read (the model has no laps:
the lap of the freeze is read off the words, since a port receives at most
one pulse per lap and serves them in order); the stored voltages; the timing
condition, which is a property of the calendar checked by `ring.py`; the
router.

## 3. Candidate predictions without noise

**Measures**, per instance (deck of three cells, section `tt_mm`, its seed),
with `phase1/cellscan.py` and `phase1/constants.py` as they are: one scan per
port (`a1`, `b1`, `c1`, `a2`; preset, threshold, dose, need, help at 16
units) and one train without noise (`ring.train`: each port alone, 10 reads
18 units apart; help at 18 units). The noise-free budget is that of campaign
1: `hi = largest help + 0.030 mV + half bracket`, `lo = -(0.015 + 0.030 +
half bracket)`. It covers every spacing of at least 16 units: the largest
help is that at 16 units, the smallest is none.

**Eligible instance**: measured (four thresholds), and its four ports have
`Own` for the noise-free budget, checked by the Lean kernel.

For each eligible instance, one run without noise of `ring.ring(3, laps)`
with `laps = sum of the needs + 10` and the guard at 16 units. With
`S_k = need_0 + ... + need_k`:

| | Candidate | From |
|---|---|---|
| P1 | **words**: port `k` reads `need_k` silent reads then `laps - S_k` FIRE | `ring_words` |
| P2 | **lap of the freeze**: the last write of the ring is at lap `S_3`; port `k` receives its first pulse at lap `S_(k-1) + 1` | P1 and one pulse per lap |
| P3 | **pulses after the last write**: `laps - S_k` on port `k`; 10 on the return port | P1 |
| P4 | **final stored values**: the stored voltage of port `k` ends at its value before date 0 minus `need_k` x its measured dose, within `(2 n + 1) x 0.01` mV for `n` pulses; the unused ports stay within 0.01 mV | P1 and the check below |
| H | **hypotheses, observed**: no pulse refused, none on a protected cell, none undelivered, nothing queued at the end; the root's FIRE routed after a launch and never after a return; a stored voltage moves only by its doses (0.01 mV otherwise) | the calendar |
| C | **negative control**, on the eligible instance whose return port has the smallest margin of its last silence: at 8 units the return port fires at least one read earlier than its zero-error word | the help of a pulse 8 units earlier |

As in campaign 1: the primary claim is P1 (with P2 and P3, which it
implies) on the eligible instances, and one discrepancy refutes it; a failed
H never refutes P1 and is reported; C can fail without touching P1, and it
would fail on the nominal cell (below). The instances that are not eligible
are run and reported without a claim.

## 4. Rehearsal, cost and size

### Rehearsal on the nominal cell

[`REHEARSAL.json`](REHEARSAL.json): four simulations at a time on one machine
of four processors, as a campaign machine runs them.

| Run | Result | Wall time |
|---|---|---|
| ring, 26 laps, no noise, guard 16 | the four words of the model (`ssss` then 22, 18, 14 and 10 FIRE); freeze at lap 16; no pulse refused; closest pulses of the root 17.2 units apart; the 10 FIRE of the return port routed nowhere; largest move that is not a dose 0.0001 mV; final values at preset minus 4 doses within 0.004 mV | 1 172 s |
| the same with the simulator's noise | the same four words | 1 625 s |
| control, return 8 units after the launch | the same four words: **C would fail on the nominal cell**, whose last silences hold by 0.80 mV; no pulse on a protected cell | 1 066 s |
| first control, return 10 units after the launch | the same four words | 1 068 s |
| scan of one port, deck of 3 cells | need 4 | 313 s |
| train of 10 reads per port, no noise / noise | `ssssFFFFFF` on the four ports | 521 s / 717 s |

The first control (`ring.ring(3, 26, 7.2, 8.0)`) was timed for a return 10
units after the launch; it was
shortened to 8 units, the spacing of campaign 1, before anything else was
decided from it. Both are kept. A ring of 6 cells and a scan on its deck were
started before the owner fixed N = 3. The scan is in `REHEARSAL.json` (703 s)
and is not used for the sizing. The ring of 6 cells was stopped unfinished,
at about lap 25 of 38 after 48 minutes, when the size was fixed: it has no
record, and nothing is said about it.

### The cost model

`wall = cells x (3.77 s x simulated ms + 3.98 s x pulses)`, times 1.39 with
noise: fitted on the two rehearsal runs that have the same pulses and
different lengths, and about 8 % above the trains, which it was not fitted on.
Pulses cost, not simulated time. Per run at N = 3 ([`COST.json`](COST.json)):

| Run | Expected | Limit (1.3 x the cost at 5 doses per port) |
|---|---|---|
| scan of one port | 313 s | 410 s |
| train, no noise / noise | 561 s / 778 s | 730 s / 1 020 s |
| run without noise, 28 laps expected | 1 263 s | 1 730 s |
| control | 1 151 s | 1 570 s |
| noisy run, ten laps after the freeze | 1 751 s | 2 390 s |
| noisy run, three laps after the freeze | 1 206 s | 1 680 s |

An instance costs about 2.3 times one of campaign 1: three cells instead of
two, and 80 to 100 pulses per run instead of 56.

### What fits in 4 h

Six instances, three per machine; per measured instance one run without
noise; one control. Two ways of counting the 4 h:

- **kit budget**, as campaign 1 counted: every run takes its whole limit. A
  stage on a machine costs the sum of (limit + 10 s) / 4 plus the largest
  (limit + 10 s). Campaign 1 was sized at 13 862 s this way and used 109
  minutes.
- **expected machine time**: the sum of the expected times / 4 plus three
  quarters of the largest, per stage and machine. The same formula gives 126
  minutes for campaign 1.

| Option | Noise measures | Noisy runs per instance | Kit budget | Expected | Port-runs tested: own room / room up to the port |
|---|---|---|---|---|---|
| I0 | 3 noisy trains per instance | 0 | 16 810 s | 191 min | 0 |
| I1s | 3 noisy trains per instance | 1, shortened | 19 345 s | 221 min | 10 / 6 |
| I3s | 3 noisy trains per instance | 3, shortened | 24 415 s | 282 min | 30 / 17 |
| F0 | fixed constants | 0 | 11 595 s | 127 min | 0 |
| **F1s** | fixed constants | 1, shortened | **14 130 s** | 157 min | 10 / 5 |
| F2 | fixed constants | 2, full | 20 115 s | 227 min | 20 / 9 |
| **F3s** | fixed constants | 3, shortened | 19 200 s | **218 min** | 30 / 14 |

Expected, with the rates of campaign 1: 5.1 instances measured of 6 (one scan
in 24 gave no threshold), **4.1 eligible instances** (19 ports of 20 had room
for the noise-free budget), 10 ports with own room at K = 3.

**The trade-off.** Measuring the noise on each instance (three noisy trains)
costs more than its scans and its noise-free train together. With it, six
instances do not fit in the kit budget even without a single noisy run (I0),
and in expected time they leave one shortened noisy run each (I1s). With
noise constants fixed beforehand:

- by the kit budget, as campaign 1 was counted: **F1s**, one shortened noisy
  run per instance, about 10 port-runs;
- by expected machine time: **F3s**, three shortened noisy runs per instance,
  about **30 port-runs with own room and 14 with room up to the port**. Its
  worst case is 5.3 h if every run takes its whole limit; each of its two
  stages stays under the 14 400 s that the launch kit allows a manifest
  (5 110 s and 14 090 s). The runs without noise and the control go first, so
  that a machine that runs out of time loses noisy runs only.

**Proposed: F3s**, if the owner counts the 4 h as expected machine time;
F1s otherwise.

Evidence: about 0.6 GB of waveforms per instance with F3s, 3.7 GB in all.

## 5. The claim under noise

The noise model of the simulator is unchanged. It **overstates the
low-frequency noise** of the integrator amplifier
([`../network-circuit/phase1/NOISE.md`](../network-circuit/phase1/NOISE.md)):
a run shifts every read of a port by one offset, 0.090 mV rms. A claim under
this noise is a claim about the model with this noise, not about the noise of
a fabricated cell; the study with an independent noise model stays deferred.

**The budget at K = 3**, per port: `hi = largest help + 3 x noise + half
bracket`, `lo = -(0.015 + 3 x noise + half bracket)`, with `noise =
sqrt(within^2 + between^2 + need x dose noise^2)`, as campaign 1 reported it.

**Per port, not per instance.** A port has *own room* if `Own` holds for its
K = 3 budget (Lean kernel), and *room up to it* if the ports before it in the
chain have own room too. Two levels, because the theorems have two:

- **N-own** (`ring_port_shaped`): in every noisy run in which it receives at
  least `need` pulses, a port with own room makes exactly `need` writes, all
  before its first FIRE: it learns its predicted state. Its number of FIRE
  depends on the ports before it and is not claimed.
- **N-word** (`ring_words`): in every noisy run, a port with room up to it
  reads exactly its zero-error word.

One port-run that fails refutes the level it belongs to. The ports without
own room are run all the same; their rates are declared comparisons, with no
claim, as in campaign 1 (where the ports without a prediction gave their
zero-error word in 7 port-runs of 12).

**The noise constants.** Either measured on each instance (three noisy
trains, as campaign 1), or fixed beforehand: 0.090 mV between runs, 0.064 mV
within a run (both from `NOISE.md`), 0.009 mV per dose. Campaign 1 measured
0.055 to 0.102 mV between runs on its five instances, from 10 to 12 offsets
each, and 0.075 mV on the 54 together: the instances do not differ by more
than their sampling error, and the fixed values are above the pooled ones.
With them, 10 of the 20 ports of campaign 1 would have had own room, the
same number as with its measured values on 16 ports. The fixed constants
cost nothing and give every measured instance a budget (one instance of
campaign 1 lacked its noise measures); they are the departure from "computed
from the measures" that makes the claim fit, and the choice is the owner's.

**How many noisy runs.** The dominant error is one offset per port per run,
so the number of runs matters more than their length. Three runs per
measured instance, each with three laps after the predicted freeze instead of
ten (every port still shows all its silent reads and at least three FIRE),
give about 30 port-runs for N-own and 14 for N-word. With no failure, 30
port-runs bound the failure rate under 10 % at 95 %.

## What the review must decide

1. **How the 4 h are counted**: kit budget (F1s) or expected machine time
   (F3s).
2. **Noise constants**: fixed beforehand, or measured per instance (then at
   most one shortened noisy run each, in expected time only).
3. **Shortened noisy runs**: three laps after the freeze instead of ten.
4. **The two levels** of the noisy claim, and that a port-run with fewer than
   `need` pulses does not count for N-own.
5. **The control**: one port can differ, the return port; it would fail on
   the nominal cell.
6. **Per-instance laps**: the calendar of a run is fixed by the measures of
   its instance (sum of the needs + 10), so the manifest of the network stage
   is written after the measures, as in campaign 1.

`PREDICTION.md` is not started: it waits for this review and for the owner to
say who carries the campaign.

## Reproduce

```sh
bash research/network-circuit-ring/check.sh
```

```sh
"$PY" -B -m unittest research/network-circuit-ring/test_ring.py
```

```sh
"$PY" -B research/network-circuit-ring/rehearse.py /a/new/folder/n3-quiet 3 26 quiet "$NGSPICE" "$PDK"
```

```sh
"$PY" -B research/network-circuit-ring/cost.py research/network-circuit-ring/REHEARSAL.json
```
