# Diagnosis of the N-own failure of campaign 2

Written after campaign 2 ended and was analyzed (`REPORT.md` of `../network-circuit-ring-campaign`, commit
`ebae4e7`), and before the preregistration of campaign 3. It reads the waveforms and records of campaigns 1 and 2
only. **No simulation was run** for it: none was needed. It changes neither the report of campaign 2 nor its
verdicts: N-own of campaign 2 fails, and stays failed.

## 1. The failing port-run

`a-7301-ring-noisy1`, port `c1` (need 4), word `ssss?FFFFFF`. The fifth pulse starts at calendar date 531.045.
Times below are in units after its start, from the waveform, with the protection latch `v(xc.p)` and the write
signal of the port `v(xc.x1.si)`, both read at 0.9 V.

| | Pulse 4 (silent read) | Pulse 5 (the `?`) | Pulse 6 (FIRE) |
|---|---|---|---|
| protection latch rises (FIRE) | no | 0.934 | 0.946 |
| protection released | | 5.396 | 5.405 |
| write signal during the ERROR phase | high from 2.073 to 2.409 (peak 1.87 V) | **never above 0.001 V** | never above 0.001 V |
| stored voltage across the cycle | -1.359 mV (one dose) | **0.0000 mV** | 0.0000 mV |
| other crossing of 0.9 V by the write signal | none | **at 6.000, 4.45 ns wide, peak 1.78 V** | none |

The read was a clean FIRE. **There was no write**: the ERROR phase of the pulse did not open, and the stored
voltage did not move. The "write" that made the letter `?` is a spike of about 4 ns on the write signal, at
6.000 units after the start of the pulse, 0.6 unit after the protection was released. The analysis counts the
writes of a pulse as the rising crossings of the write signal in `[start, start + 6 units)`, and the spike falls
inside that interval by a fraction of a nanosecond.

## 2. The mechanism

At exactly 6 units after the start of a pulse the testbench of `../network-circuit/net.py` (`Session.pulse`)
switches two controls of the port at once, each with a 1 ns edge: the reset of the sequencing latches (`kr`)
comes back, and the window `kp` ends. The spike is on that edge. It is not a race between the FIRE latch and the
write gate: the latch rose at 0.934 and was released at 5.396, and the ERROR phase, which opens at 1.46 to 2.07
units on the ports of campaign 2, stayed closed.

## 3. Every other such event in campaigns 1 and 2

- **Records.** Among the 3 853 reads of the network runs, scans and trains of campaigns 1 and 2 (2 450 FIRE),
  this is the only read recorded with a FIRE and a write, and the only write with no end inside its cycle.
- **Waveforms.** Every rising crossing of 0.9 V by every write signal of the 46 waveforms of campaign 2 and the
  64 of campaign 1 was classified. Apart from the writes of silent reads, there are **two** crossings, one
  per campaign, both on the edge at 6 units, both in a noisy run. The writes of silent reads, from the records of
  the two campaigns (1 115 writes): rising 1.46 to 2.24 units after the start of their pulse, 3.1 to 7.9 us from
  rise to fall, a step of the stored voltage of 1.32 to 1.38 mV.

| Campaign | Run, port, pulse | Read | Spike after the start | Width | Peak | Stored voltage across it |
|---|---|---|---|---|---|---|
| 2 | `a-7301-ring-noisy1`, `c1`, 5 | FIRE (latency 0.934) | 5.9999 units | 4.45 ns | 1.78 V | -0.0024 mV |
| 1 | `a-7201-net-noisy2`, `a1`, 5 | silent, one real write at 1.570 (1.338 mV) | 5.9997 units | 19.6 ns | 1.80 V | -0.0025 mV |

In campaign 1 the second crossing gave that silent read two writes, hence its letter `?` (word
`ssss?FsFFFFFFFFFFF`), in a declared comparison that carried no claim. Neither spike wrote charge.

Rates: 2 spikes in 1 189 pulse cycles of noisy network runs (558 in campaign 1, 631 in campaign 2), none in the
742 cycles of the runs without noise, and none in the scans and trains.

## 4. No margin on the first FIRE read

The read that failed is ordinary. Its latency (0.934) is inside the range of the 1 365 FIRE of the network runs
of both campaigns (0.81 to 1.00, median 0.88 to 0.91). The room of its first FIRE (0.550 mV) is the 8th of the 16
measured ports of campaign 2 (0.04 to 1.34 mV); its least room at K = 3 is 0.184 mV. A stricter margin on the first
FIRE read that excluded it would exclude half of the ports, and it would not rest on the mechanism, which is not
about the read. **No clean margin condition exists: by the owner's rule, campaign 3 runs exactly as committed.**
No amendment N-own' is proposed.

## 5. What the mechanism would support instead, for the owner

The spike is told apart from a write by every feature measured, each with a wide margin: its width (4 to 20 ns
against 3 100 to 7 900 ns), its date (on the edge at 6 units against 1.46 to 2.24 units) and its effect on the
stored voltage (0.003 mV against a step of 1.32 to 1.38 mV). A condition resting on the mechanism would be a definition of
a write in the analysis, for example: *a write is a rising crossing of 0.9 V by the write signal that stays above
0.9 V for at least 1 us*, which every real write of campaigns 1 and 2 meets by a factor of 3 or more and both
spikes miss by a factor of 50 or more.

That is a change of the analysis, which the commitment of campaign 3 keeps unchanged, and not the kind of
condition the owner asked for here (a margin on the first FIRE read). It is not proposed as an amendment. If the
owner wants it, it would come as an amendment to the commitment pushed before the preregistration of campaign 3,
reported in addition to the committed analysis, never instead of it, as the owner set for N-own'.

What staying as committed means for campaign 3, from the rate above: about 12 noisy runs of about 35 pulse
cycles each, so about 420 noisy cycles; at 2 in 1 189, the chance of at least one spike is about 50 %, and a
spike makes a port-run fail only on a port counted for N-own or N-word (about 6 ports in 16 in campaign 2), so a
failure of that origin has a chance of roughly 20 to 25 %, whatever the cells do.
