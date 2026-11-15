# Amendment 2 to the commitment of campaign 3

Pushed alone on the branch `research/network-circuit-ring-campaign-3-commitment`, after
[`COMMITMENT.md`](COMMITMENT.md) (`d758fdb`), [`AMENDMENT_1.md`](AMENDMENT_1.md) (`e1e4a60`) and
[`DIAGNOSIS_N_OWN.md`](DIAGNOSIS_N_OWN.md) (`e69fab5`), none of which it edits, and before the `PREDICTION.md` of
campaign 3. It **adds** a definition and two claims, asked for by the owner after the diagnosis, which the owner
accepted. It removes and changes nothing.

## Why

In campaign 2, N-own failed on one port-run (`a-7301-ring-noisy1`, `c1`, pulse 5): a clean FIRE with no write and
no charge, whose letter was `?` because a spike of about 4 ns on the write signal, at the edge of the testbench 6
units after the start of the pulse, fell inside the interval in which the analysis counts writes. In campaigns 1
and 2, real writes stay above 0.9 V for 3.1 to 7.9 us; the two spikes found, one per campaign, for 4.45 and 19.6
ns. This amendment is motivated by that failure, and the condition below was chosen after seeing the data of
campaigns 1 and 2.

## 1. write'

**write'**: a rising crossing of 0.9 V by the write signal of the port, inside the cycle of the pulse (from its
start to 6 units later), that **stays above 0.9 V for at least 1 us**: from that crossing to the next falling
crossing of 0.9 V, wherever it falls.

The **word'** of a port is its word with write' in place of write: `s` is a pulse with no FIRE of the cell from
its start to one unit and 2 us later and exactly one write' on that port during its cycle; `F` is one FIRE in that
window and no write'; any other pulse gets its own letter and is neither `s` nor `F`, as in the word.

## 2. N-own' and N-word'

- **N-own'**: the claim N-own, on the same ports (own room under the noisy budget at K = 3) and the same noisy runs,
  with word' in place of word. A port-run with fewer than `need` pulses does not count, and the number of such
  port-runs is reported.
- **N-word'**: the claim N-word, on the same ports (room up to them under the noisy budget at K = 3) and the same
  noisy runs, with word' in place of word.

Each is refuted by one port-run that fails it, and is not established without a port-run that counts. **Both are
evaluated on campaign 3 only and never pooled with campaigns 1 and 2**, whose data shaped the condition.

## 3. N-own and N-word stay

N-own and N-word are evaluated in campaign 3 with the committed definition of a write, exactly as in campaign 2,
and reported with their own verdicts. N-own' and N-word' are reported **in addition, never instead**. N-own stays
refuted for the series by the pooled rule of the commitment: it failed in campaign 2. The report of campaign 2 is
not changed.

## 4. Nothing else changes

The same cells, testbench, simulator and noise model; the same budgets and fixed noise constants; the same
noise-free claim (P1 and P2, with H and P4), control and declared comparisons; the corrections of the commitment
(scan limit 640 s, robust scan, majority on contradictory states, one run without noise and one shortened noisy run
per measured instance, one control) and its budget as amended by amendment 1. write' enters no claim other than
N-own' and N-word'.
