# Periodic ring of R cells, campaign 3: predictions

Written and pushed alone, before any implementation of campaign 3: no runner, no manifest, no analysis of
campaign 3 exists when this file is committed, and none of its seeds has been simulated. Nothing in it may be
changed afterwards; a wrong rule is corrected by an amendment file pushed before the run or the computation it
concerns.

It is the protocol of campaign 2
([`../network-circuit-ring-campaign/PREDICTION.md`](../network-circuit-ring-campaign/PREDICTION.md), commit
`7ae9710`, SHA-256 `cc16b94e6aa4eca8f065724db3d7a32a3640c90e4eaaf4c73fe250e9ea6208e7`), with exactly the
corrections of [`COMMITMENT.md`](COMMITMENT.md) (`d758fdb`), its budget as replaced by
[`AMENDMENT_1.md`](AMENDMENT_1.md) (`e1e4a60`), and the additions of [`AMENDMENT_2.md`](AMENDMENT_2.md)
(`b74dae2`). It is written out in full below so that it can be read alone. Where it differs from campaign 2, the
section says so.

Everything here is a transistor-level simulation (ngspice 42, SKY130 models) of three R cells of
[`../circuit/cell.spice`](../circuit/cell.spice), with the junction areas of stage J of the layout study, joined by
an ideal router outside the simulator. There is no layout of a network, no wire between the cells and no silicon.
The circuit does not verify the proved read window, and nothing here says that it does.

## What is tested

The same as in campaign 2: whether, on cells with mismatch that no one has looked at, the learned state of the
periodic ring of three cells is the one computed beforehand from per-port measures, through `ring_port_shaped` and
`ring_words` of [`../network-circuit-ring/RingNetwork.lean`](../network-circuit-ring/RingNetwork.lean).

The primary claim is deterministic: one run without noise per eligible instance, one discrepancy refutes it. The
claim under the simulator's noise is made per port, at `K = 3`, on two levels, N-own and N-word, each refuted by
one failing port-run; and, in addition, on the same port-runs with a stricter definition of a write, N-own' and
N-word'.

## Decisions of the owner that this file applies

From the commitment and its two amendments:

1. **Campaign 3 runs whatever campaign 2 gave**, and is the last campaign of this series for this claim.
2. **Twelve new instances**, seeds 7401 to 7412, never simulated, none reused.
3. **Four corrections from the measures of campaign 2**, and no other:
   1. scan time limit **640 s**;
   2. a **robust scan**: after the first FIRE, two more isolated reads at one and two further doses, so that every
      port has at least three fired states; rehearsed on the nominal cell before freezing;
   3. **contradictory states** (the case of 7206 in campaign 1): the isolated reads at the two disputed states are
      repeated and the majority is taken;
   4. **one run without noise and one shortened noisy run** per measured instance; one control run.
4. **Budget**: expected machine time, two machines, two stages, about 269 minutes if all twelve instances are
   measured and about 229 minutes if nine are (238 with the extra reads of the robust scan); the kit's worst case
   25 665 s (7.1 h). Both are above the 4 h first fixed, and the owner accepted them.
5. **write', N-own' and N-word'** (amendment 2), in addition to N-own and N-word, never instead; evaluated on
   campaign 3 only and never pooled.
6. **Reporting**: each campaign separately, with its own verdicts. Pooled figures are sums of counts only. A
   pooled claim holds only if it holds in each campaign; one failure in either refutes it. N-own' and N-word' are
   never pooled.
7. **Everything else unchanged**: N = 3, the ring and its calendars, both budgets, the fixed noise constants, the
   predictor, N-own and N-word, the rule of the control instance, the analysis, the noise model, the launch kit,
   one launch per machine per stage.

## What was run before this file

- Campaign 1 (instances 7201 to 7206) and its development instances (7101 to 7103); phase 0 of the ring on the
  nominal cell; campaign 2 (instances 7301 to 7306), ended and analyzed once (`REPORT.md`, commit `ebae4e7`).
- The diagnosis of the N-own failure of campaign 2 ([`DIAGNOSIS_N_OWN.md`](DIAGNOSIS_N_OWN.md)) read the
  waveforms of campaigns 1 and 2; it ran no simulation.

Nothing was ever simulated with the seeds 7401 to 7412. The robust scan has not been run yet.

## Definitions

As in campaign 2, with these instances.

**Time unit.** 20 us, the length of a pulse.

**Instance.** One deck with three cells, `a` (the root), `b` and `c` (the relays): `net.deck` of
`../network-circuit/net.py` with the model section `tt_mm`, 27 C, the junction areas of stage J, and the simulator
command `setseed` with the seed of the instance before the deck is read. Twelve instances: seeds **7401 to 7406**
(machine `a`) and **7407 to 7412** (machine `b`). Each instance is measured and run on its machine.

**Ports**, in the order a pulse meets them: 0 `a1` (launch port of the root), 1 `b1`, 2 `c1`, 3 `a2` (return port
of the root). Ports `b2` and `c2` are never pulsed: the **unused ports**.

**Stored voltage `u`** of a port: stored node minus summing node, in mV. A more negative `u` is a higher gain.

**FIRE**: the protection latch of the cell rises through 0.9 V within one unit and 2 us after the start of the
read. **Write**: the write signal of the port rises through 0.9 V during the cycle of the pulse (from its start to
6 units later).

**Word** of a port in a run: one letter per pulse addressed to the port, in the order of the dates. `s`: no FIRE
and exactly one write. `F`: one FIRE and no write. Any other pulse (refused by the router, not delivered, arriving
while the cell is protected, a FIRE with a write, neither a FIRE nor a write, two writes) gets its own letter and
is neither `s` nor `F`. The writes of a port are its number of `s`; the pulses it receives are the letters of its
word.

**write'** (amendment 2): a rising crossing of 0.9 V by the write signal of the port, during the cycle of the
pulse, that stays above 0.9 V for at least 1 us, from that crossing to the next falling crossing of 0.9 V wherever
it falls. **Word'**: the word with write' in place of write.

**Lap** of a pulse: `floor(d / P) + 1`, where `d` is the start of the pulse in units after date 0 and `P` the
period of the calendar.

### Measures, each port alone

Per instance, every run pulsing one port at a time with the others idle:

1. **Robust scan** of each of the four ports `a1`, `b1`, `c1`, `a2`, no noise, on the deck of the ring. **Changed
   from campaign 2.** It is the scan of `../network-circuit/phase1/cellscan.py` (training reads 22 units apart from
   the preset until the first read that fires with a latency of at most one unit; the reference read; the read 16
   units after it; the coarse descent; the bisection of the threshold to 20 uV), with two changes:
   - **Two more fired states.** Right after the read 16 units after the reference, the scan writes one dose with a
     clock-only pulse, reads the port isolated (22 units after the previous pulse), writes a second dose, and
     reads again. These two reads are isolated reads like the others. Then an imposed leak on this port alone
     brings the stored voltage back to the state of the first FIRE (within 2 uV, in steps of at most 1.2 mV, as the
     bisection does), and the coarse descent and the bisection go on unchanged.
   - **Contradictory states.** At the end of the bisection, if among the isolated reads a state that fired is not
     stronger than a state that stayed silent (the largest stored voltage that fired is not below the smallest
     stored voltage that stayed silent), the scan brings the port back to each of the two disputed states, the
     largest stored voltage that fired and the smallest that stayed silent (within 2 uV, as above), and reads each
     of them twice more, isolated. One such round at most.

   `cellscan.py` itself is frozen by hash in the manifests of campaigns 1 and 2, and is not edited: the robust scan
   is a new file of campaign 3, `cellscan.py` with only these two changes, rehearsed on the nominal cell before the
   implementation is frozen. Four runs.
2. **Train without noise** (`ring.train(3, 10)`), unchanged. One run.

**The majority rule** (applied by the prediction step to the records of a scan, before the constants): a
disputed state that was read three times counts once, with the outcome of the majority of its three reads (FIRE
or not); its other reads enter nothing else. If the isolated reads are still contradictory after that, or if
either of the two extra reads did not fire and no round of repeats resolved it, the port has no threshold.

The function `port` of `../network-circuit/phase1/constants.py`, unchanged, then gives per port its preset,
threshold, half bracket, dose, gap, and helps at 16 units after a FIRE and at 18 units after a silence and after a
FIRE. An instance is **measured** when its five runs count and `port` yields the constants of its four ports;
otherwise it is not measured, has no prediction, gets no network run and enters no claim.

### The model and the two budgets

Unchanged from campaign 2. Integers, one dose is 100 000 units, the gap of a port is
`round(gap / dose x 100 000)`, its **need** is the least `n >= 0` with `n x 100 000 >= gap`; with
`S_k = need_0 + ... + need_k` (`S_-1 = 0`), the **zero-error word** of port `k` on `L` laps is `min(need_k, m)`
letters `s` then `m - need_k` letters `F`, with `m` the pulses the ports before it let through
(`ring.zero_error`).

**Noise-free budget**, per port, in mV:

    hi = + max(0, help at 16, help at 18 after a silence, help at 18 after a FIRE) + 0.030 + half bracket
    lo = - (0.015 + 0.030 + half bracket)

**Noisy budget, `K = 3`**, per port, in mV, with the fixed constants (a departure from "computed from the
measures", for the noisy budget only):

    noise = sqrt(0.064^2 + 0.090^2 + need x 0.009^2)
    hi = + max(0, the three helps) + 3 x noise + half bracket
    lo = - (0.015 + 3 x noise + half bracket)

Budgets become integers in units of 1/100 000 dose by rounding away from zero.

**Own room** under a budget: `Own gap d lo hi k need` of `RingNetwork.lean` holds (`d = 100 000`). **Room up to
port `k`**: every port `j <= k` has own room. **Eligible**: measured, and own room on its four ports under the
noise-free budget. **Margin of the last silence** of a port: `(gap - (need - 1) x 100 000)` units times its dose
divided by 100 000, in mV; none if `need = 0`.

### Calendars

Unchanged. **The ring** `ring.ring(3, L)`: a launch on `a1` every 37 units, wires of 17/3 units, the root routed
forward only within 2 units after a launch, guard 16. **The control** `ring.control(3, L)`: wires of 1.767 units,
period 19, the return about 8 units after the launch, without the guard. **Laps**: `L = S_3 + 10` for the run
without noise and the control, `L' = S_3 + 3` for the noisy run, fixed in `PREDICTED.json` before any network run.

## Order of the campaign

1. **Measures.** Each machine measures its six instances.
2. **Predictions.** From the collected measures of both machines, the frozen scripts write `PREDICTED.json` (per
   instance: measured or not and why, the records kept by the majority rule, constants, integers of both budgets,
   needs, own room and room up to each port under each budget, eligibility, laps, zero-error words for `L` and
   `L'`; the control instance; the network runs with their limits) and the Lean file of `Own` or its negation per
   port and budget, checked by the Lean kernel. **`PREDICTED.json` is committed and pushed before any network
   run**, and the launcher of the network runs is bound to its SHA-256. If the Lean check fails or disagrees, no
   network run is launched and the campaign ends there.
3. **Network runs**, on the machine that measured the instance, in this order on each machine: `quiet`, one run of
   `ring.ring(3, L)` without noise per measured instance, in the order of the seeds; `control`, one run of
   `ring.control(3, L)` without noise on the control instance, on its machine; `noisy`, **one** run of
   `ring.ring(3, L')` with the simulator's noise per measured instance, in the order of the seeds. **Changed from
   campaign 2** (three noisy runs there).
4. **One analysis**, after both machines have ended.

**Control instance.** Among the eligible instances whose `a2` has `need >= 1`, the one whose `a2` has the smallest
margin of its last silence; the lowest seed in case of a tie. None if there is no such instance.

## Predictions

**Primary claim: the learned state without noise**, unchanged. For every eligible instance, in its `quiet` run:

- **P1, words.** The word of each port `k` is its zero-error word for `L` laps: `need_k` letters `s` then
  `L - S_k` letters `F`.
- **P2, lap of the freeze.** The last write of the ring is at lap `S_3`, and port `k` receives its first pulse at
  lap `S_(k-1) + 1`.

Refuted by one port of one eligible instance whose word differs from P1, or one eligible instance whose laps differ
from P2.

**Reported with the primary claim, never refuting it**, unchanged: **H**, the hypotheses observed (no pulse
refused, none on a protected cell, every pulse delivered, nothing queued at the horizon, two pulses of one cell
never less than 16 units apart, every FIRE of the root on `a1` carried to `b1` and none on `a2` carried anywhere,
every `s` moving its stored voltage by its measured dose within 0.01 mV, at most 0.01 mV between two consecutive
pulses of a port and across each of its pulses that is not an `s`, the waveform reaching the horizon); **P4**, the
final stored values (within `(2 n + 1) x 0.01` mV of the start of the run minus writes times the measured dose, for
`n` pulses received; each unused port within 0.01 mV).

**The claim under noise, per port, at `K = 3`**, over every measured instance and its noisy run if it counts:

- **N-own**, unchanged. A port with own room under the noisy budget, in a noisy run in which it receives at least
  `need` pulses, has a word made of exactly `need` letters `s` followed only by letters `F`. A port-run in which the
  port receives fewer than `need` pulses does not count; their number is reported.
- **N-word**, unchanged. A port with room up to it under the noisy budget reads exactly its zero-error word for
  `L'` laps.
- **N-own'** (amendment 2). N-own on the same port-runs, with the word' of the port in place of its word.
- **N-word'** (amendment 2). N-word on the same port-runs, with the word' of the port in place of its word.

Each of the four is refuted by one port-run that fails it, and is not established without a port-run that counts.
N-own and N-word are reported with their own verdicts; N-own' and N-word' in addition, never instead.

**Negative control, on the control instance**, unchanged. **C**: in the `control` run, the return port `a2` fires
earlier than its zero-error word for `L` laps: its word begins with fewer than `need_3` letters `s` before its
first `F`. Stated in advance: C failed on the nominal cell in the rehearsal of phase 0, and on the control instance
of campaign 2 (7306), whose four words were the zero-error words. If C fails, the control showed nothing on that
instance; it does not touch the other claims.

**Declared comparisons, not claims**, unchanged from campaign 2: **M1** (ports without own room at K = 3, noisy
runs: port-runs with the zero-error word and with the predicted writes), **M2** (own room but not room up to them:
port-runs with the zero-error word), **M3** (the `quiet` runs of the measured instances that are not eligible,
against their zero-error words, with own room and room up to each port under the noise-free budget), **M4** (the
nominal predictor, need 4 on every port), **M5** (run offsets and scatter of the FIRE latency in the noisy runs,
against 0.090 and 0.064 mV), **M6** (H and P4 on the other runs). Added: **M7**, per port-run of the noisy runs,
whether its word and its word' differ, and every rising crossing of the write signal that is a write but not a
write', with its date in the cycle and its width.

**Expected size**, from the rates of campaign 2 (own room at K = 3 on 6 of 16 measured ports, room up to them on 2
of 16), with one noisy run per instance and 9 to 12 measured instances: about 13 to 18 port-runs for N-own and
N-own', and 4 to 6 for N-word and N-word'.

## Rules of the analysis

Unchanged from campaign 2, with campaign 3's own files:

1. **One analysis, at the end**, frozen with the implementation, run once on the evidence of the two machines after
   both have ended their network runs. No word of a network run is looked at while a machine is running: only the
   statuses of the launcher.
2. **The predictions are those of the measures.** The analysis first checks that `PREDICTED.json` is what the
   frozen prediction script gives from the evidence of the measures; if not, every claim is "not established".
3. **Which runs count.** A run counts when the launcher recorded it `complete` and its own record says that it
   reached its last date. A run that failed, reached its time limit or was lost at a restart is a **missing run**:
   listed with its status, neither a success nor a failure, never replaced and never run again.
4. **Missing measures.** An instance with a missing measure run is not measured.
5. **Missing network runs.** P1 and P2 are evaluated on the eligible instances whose `quiet` run counts; the
   primary claim needs at least one, otherwise it is **not established**. C needs its run and a control instance. A
   missing noisy run removes its port-runs; nothing replaces them.
6. **No re-scoping.** The eligible instances, the needs, the ports with own room and with room up to them, the laps
   and the control instance are those of `PREDICTED.json`.
7. **Shared noise.** Noisy runs of one instance with the same noise fingerprint: the first in the order of the
   manifest is kept, the others are duplicates and enter no count. (With one noisy run per instance, none is
   expected.)
8. **Failures are reported as they are.** A failed prediction is written "fails" with its words.

**Reporting across campaigns.** Campaign 3 is reported on its own, with its own verdicts. Where campaigns 2 and 3
are put side by side, the pooled figures are sums of counts only, and a pooled claim holds only if it holds in each
campaign: N-own, which failed in campaign 2, stays refuted for the series whatever campaign 3 gives. N-own' and
N-word' are reported for campaign 3 alone and never pooled. The report of campaign 2 is not changed.

## Execution

- **Executor.** A Claude Code cloud session on behalf of the owner, on two cloud containers whose inventories are
  recorded.
- **Launcher.** The second launch kit, unchanged, used twice: for the measures with this file as its protocol, then
  for the network runs with `PREDICTED.json` as its protocol. Each launch has its manifest, every runner, deck
  source and analysis file frozen by hash, and its attempt marker pushed before the launch with the state of the CI
  on the exact source commit. One launch per machine and per stage.
- **Environment, identical on both machines and checked by the launcher**: ngspice 42
  (`820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45`), PDK commit
  `1232782c1b9fab3aacda74d67ce7c92bf7da8105`, Python 3.12.3
  (`e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f`), numpy 2.3.5
  (`064003bdb6f9f7bb06e46e07cc3398cbfdc3c114dfe55b89d239e564917be2fb`).
- **Four runs at a time** on each machine.
- **Time limits.** Measures: a robust scan **640 s** (changed), the train 730 s. Network runs: per run, from the
  cost model of phase 0, unchanged:

      expected = 3 x (3.7746 s x simulated ms + 3.9820 s x pulses) x (1.3861 if the run has noise)
      limit    = 1.3 x expected, rounded up to 10 s

  with the simulated time of its calendar and the pulses of the zero-error words of its instance for its laps. The
  launcher's estimate of a run is its expected time rounded up to 10 s.
- **Budget.** As fixed by amendment 1. The bound of the launcher per machine and stage is the sum of (limit + 10 s)
  divided by four plus the largest (limit + 10 s), at most 14 400 s per manifest for the two machines together. At
  five doses per port: 5 750 s per machine for the measures, 7 280 s and 6 885 s for the network runs, **25 665 s in
  all**. If the network runs of `PREDICTED.json` would exceed 14 400 s for the two machines together, the last
  noisy run of the machine whose bound is the larger (machine `a` if equal) is removed, again and again, until they
  fit; the removed runs are listed in `PREDICTED.json` as not run for the budget, enter no count, and are not
  missing runs.
- **Resume**, **noise** and **evidence** as in campaign 2. Each run writes its deck, its session log, its waveform,
  its record and its noise fingerprint; every surviving file is collected byte for byte with its SHA-256. Decks,
  logs, records, fingerprints and the SHA-256 lists are committed here; the waveforms go unchanged to
  `HevisNico/kernel-R-circuit` during the campaign, and after the one analysis to an evidence branch of this
  repository with no shared history. A waveform above 100 MiB is stored as consecutive parts of 90 000 000 bytes,
  with the SHA-256 of every part and of the whole file, checked before and after each push.

## What this campaign cannot show

As in campaign 2: nothing about silicon, a layout, wires between cells or a real router; nothing about the noise of
a fabricated cell (the claims under noise hold for the simulator's noise model, which overstates the low-frequency
noise of the integrator amplifier, with constants fixed beforehand; a separate noise study is committed on
`research/network-noise-study-commitment`); nothing about the native periodic ring of
`NativePeriodicRingTarget.lean`, from which the circuit ring departs in the ten ways of phase 0; nothing about
ports without own room; nothing outside 27 C, the typical corner with mismatch, three cells, one calendar of each
kind, twelve instances; nothing about pulses closer than 16 units on a cell beyond the one control run. The
per-port measures are made on the deck of the ring by the same simulator. And N-own' and N-word' rest on a
definition chosen after seeing the data of campaigns 1 and 2: they are evaluated on campaign 3 alone.
