# Verdicts

Written by `analyze.py` from the results. The statements are those of `PREDICTION.md`.

22 hold, 2 fail, 0 not evaluable, of 24.

| | Statement | Measured | Status | Reason |
|---|---|---|---|---|
| C1 | pattern ssssFFFFFF on both ports, FIRE on the joint pulse | ssssFFFFFF ssssFFFFFF F | holds | — |
| C2 | silent steps between 1.345 and 1.348 mV | 1.346 to 1.347 mV | holds | — |
| C3 | firing steps below 0.002 mV | largest 0.001 mV | holds | — |
| C4 | write window 1.777 to 2.040, protection ends at 5.59 | 1.777 to 2.039, end 5.59 | holds | — |
| C5 | joint read between 0.2665 and 0.2685 | 0.2675 | holds | — |
| P1 | 4 silent pulses on both ports in at least 18 of 20 runs, never fewer than 3 or more than 5 | 20 of 20 runs, range 4 to 4 | holds | — |
| P2 | sigma of the joint read below 0.0012, every read between 0.264 and 0.271 | sigma 0.00128 (±16% for 20 runs), 0.2645 to 0.2700 | fails | sigma is not below 0.0012 |
| P3 | a port at rest changes over a period with a sigma between 0.05 and 0.10 mV | 0.071 mV | holds | — |
| P4 | sigma of a silent step, read noise removed, below 0.067 mV | 0.000 mV (silent step 0.070 mV) | holds | — |
| P5 | firing steps: mean within 0.01 mV of zero, sigma within 25% of the sigma at rest | mean -0.0019 mV, sigma 0.069 mV (0.97 of rest) | holds | — |
| P6 | both ports of every cell stop within 10 pulses, after 2 to 8 silent pulses | 200 of 200 ports stop, 1 to 6 silent pulses (ports per count: 1: 1, 2: 7, 3: 48, 4: 74, 5: 60, 6: 10) | fails | 1 ports are outside 2 to 8 silent pulses |
| P7 | every cell fires on the joint pulse; sigma 0.0025 to 0.0042; reads between 0.250 and 0.280; every pair within 0.05 | 100 of 100 fire, sigma 0.0029, 0.2595 to 0.2730, 4950 of 4950 pairs | holds | — |
| P8 | a port relapses only if its first FIRE came after 0.95; 4% to 14% of ports relapse; none twice; each relapse within 20% of a dose | 9 of 200 ports (4.5%), first FIRE of these 0.971 to 0.998, 0 relapse twice, steps 1.313 to 1.451 mV | holds | — |
| P9 | ports without relapse: total change over the firing pulses has mean within 0.03 mV of zero and sigma below 1.5 times the sigma at rest | mean -0.0022 mV, sigma 0.071 mV (1.05 of rest), 191 ports | holds | — |
| P10 | no firing pulse steers the sensor current to the integrator, in any run | 0 of 3526 firing pulses in 141 runs | holds | — |
| P11 | over 22 firing pulses the stored voltage moves by less than 0.01 mV | -0.0050 mV and -0.0050 mV over 22 and 22 firing pulses | holds | — |
| P12 | the six corner runs stop after 4, 4, 4, 4, 2 and 7 silent pulses; joint read between 0.262 and 0.272 | ss_27: 4/4, 0.2705; ff_27: 4/4, 0.2645; sf_27: 4/4, 0.2635; fs_27: 4/4, 0.2700; tt_m40: 2/2, 0.2645; tt_125: 7/7, 0.2705 | holds | — |
| P13 | no leak, no noise: no relapse, stored voltage within 0.05 dose after the stop | 0 relapses, band 0.025 dose | holds | — |
| P14 | no leak, with noise: at most one relapse | 0 relapses, band 0.29 dose | holds | — |
| P15 | 0.1 TΩ: a relapse every 22 or 23 periods, never two silent pulses in a row, relapse steps 1.27 to 1.31 mV, band within 1.05 dose | 7 relapses, distances [22, 23], steps 1.288 to 1.288 mV, band 0.99 dose | holds | — |
| P16 | 1 TΩ: first relapse between pulses 85 and 100, relapses 220 to 224 periods apart | relapses at [93, 314, 535], distances [221, 221] | holds | — |
| P17 | 0.1 TΩ with noise: relapses 17 to 28 periods apart, never two silent pulses in a row, band within 1.6 dose | 7 relapses, distances [21, 22, 23, 25], band 1.11 dose | holds | — |
| P18 | 8 cells with mismatch and noise under 0.1 TΩ: mean distance between relapses 17 to 29, two silent pulses in a row at most once, band within 1.8 dose | cell: mean distance, doubles, band in doses. 3001: 21.7, 0 double, 1.07; 3002: 22.7, 0 double, 1.12; 3003: 23.7, 0 double, 1.03; 3004: 23.7, 0 double, 1.14; 3005: 24.0, 0 double, 1.12; 3006: 23.0, 0 double, 1.12; 3007: 22.7, 0 double, 1.10; 3008: 22.2, 0 double, 1.18 | holds | — |
| P19 | no run fails and the guard reports nothing | 141 of 141 runs with a result, 0 failed, 0 missing, 0 not readable, 0 with a protection that is not a FIRE, 0 with an event against the mechanism | holds | — |

## Runs

The plan of `campaign.py` has 141 runs.

| State | Runs | Which |
|---|---|---|
| complete | 141 | — |
| left out by the guard | 0 | — |
| failed | 0 | — |
| not evaluable: run missing | 0 | — |
| not evaluable: result not readable | 0 | — |

## Guard

- Runs with a protection that is not a FIRE, left out of the statistics: none.
- Runs with an event against the mechanism, kept in the statistics: none.
- Latest FIRE of the campaign: 1.0000 units after the start of its pulse. The pulse ends at 1.

## Observations made after the campaign

These are not predictions.

### The dose in log-gain

Measured from the peak of the main charge at consecutive silent pulses.

| Runs | Dose in log-gain | Steps measured |
|---|---|---|
| nominal, 27 °C | 0.0422 | 6 |
| ss, ff, sf, fs at 27 °C | 0.0423 (sigma 0.0004) | 24 |
| typical, −40 °C | 0.0519 | 2 |
| typical, 125 °C | 0.0330 | 12 |
| mismatch and noise, 27 °C | 0.0423 (sigma 0.0028) | 615 |

### The count of silent pulses and the start gap

The start gap of a port is the log of the ratio of the swing at which its cell fires to its swing at the first pulse, in doses of that port. A port should need the next whole number of doses.

- 190 of 200 ports have a count of silent pulses equal to their start gap rounded up.
- The 10 others have a start gap within 0.06 dose of a whole number, where the estimate of the firing swing decides.
- Start gap over the 200 ports: mean 3.55 doses, sigma 0.90, from 0.65 to 5.42.
- A normal law with this mean and sigma puts 0.4 of 200 ports at one silent pulse or fewer, and 99.8% of the ports between 2 and 8.
- Port 2 of `mc_2027` has 1 silent pulse: its start gap is 0.65 dose. The other port of that cell has 4 silent pulses. The joint read of that cell: FIRE at 0.2695.

### Intervals of the numbers that come from noise

A noisy run cannot be replayed: its seed does not set its noise (COMPLEMENT.md). Running the campaign again gives other runs from the same distribution. The intervals below are 95% intervals, from resampling the runs of the campaign.

| Number | Value | 95% interval | Runs |
|---|---|---|---|
| Sigma of the joint read, noise only (P2) | 0.00128 | 0.00068 to 0.00166 | 20 |
| Sigma of the change of a port at rest, noise only (P3) | 0.071 mV | 0.065 to 0.077 mV | 20 |
| Sigma of a silent step, noise only (P4) | 0.070 mV | 0.062 to 0.078 mV | 20 |
| Sigma of a firing step, noise only (P5) | 0.069 mV | 0.062 to 0.076 mV | 20 |
| Sigma of the joint read, mismatch and noise (P7) | 0.0029 | 0.0025 to 0.0032 | 100 |
| Share of the ports with a relapse, mismatch and noise (P8) | 4.5% | 2.0 to 7.5% | 100 |
| Sigma of the total change over the firing pulses (P9) | 0.071 mV | 0.064 to 0.077 mV | 100 |
| Mean distance between two relapses, one value per cell under 0.1 TΩ (P18) | 22.9 | cells from 21.7 to 24.0, sigma 0.8 | 8 |
| Band of the stored voltage after the stop, one value per cell under 0.1 TΩ (P18) | 1.11 dose | cells from 1.03 to 1.18, sigma 0.05 | 8 |

The two noisy refresh runs of one port without mismatch (P14, P17) are one run each in the campaign. One run gives no interval. The complement repeats them.

