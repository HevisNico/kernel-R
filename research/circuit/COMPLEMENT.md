# Complement to the campaign

Run after the campaign by `complement.py` and read by `compare.py`. Nothing here is a prediction, and nothing here replaces a verdict.

## The runner without the new option

The option `rel` was added to `run.py` after the campaign. Runs without noise are run again without it. They must give the result of the campaign exactly: if they did not, something else than the noise would vary from one run to the next.

- `nom`: identical byte for byte to the result of the campaign.
- `pvt_tt_m40`: identical byte for byte to the result of the campaign.

## Runs replayed with the same seeds

Same netlist, same options, same seeds. The only change is that each time is printed from the start of its pulse.

- Runs compared: 24, 504 pulses.
- FIRE or silence differs on 5 of 504 pulses: mc_2062 pulse 13; mc_2062 pulse 14; mc_2063 pulse 4; mc_2064 pulse 3; mc_2064 pulse 5.
- The two stored voltages are identical on 0 of 504 pulses. Their difference between the campaign and the replay has an rms of 0.214 mV.
- FIRE latency, on the pulses that fire in both: largest difference 0.1614 unit.

**The replays do not reproduce the campaign.** With the same seed a run draws another noise sample: the stored voltages differ by an amount of the size of the read noise. The seed of a run does not set its noise.

The mismatch sample is another matter. The swing of the main capacitor at the first pulse of a port measures the start gain of that port. Over the 8 ports of the replayed mismatch runs it differs by at most 1.84 mV between the campaign and the replay. Between the 200 ports of the campaign it has a sigma of 13.38 mV.

Noise alone moves this swing: over the noise runs without mismatch it has a sigma of 1.40 mV. The mismatch sample of a run is therefore reproduced by its seed, within what the noise allows to see.

The four mismatch runs of this list (cells 2061 to 2064) are those that were being computed when the campaign was stopped by a time limit and resumed. They had written nothing when they were stopped, so the campaign holds one result for each, and the stop itself gives nothing to compare.

## The 20 noise runs, sample by sample

In the campaign a joint read is printed to 0.0005 unit, 10 ns. In the replays it is printed to 0.00001 unit or better. A replay draws another noise sample, so each set of replays is another sample of 20 runs, not the same sample read more finely.

P1 to P5 are judged again on each sample, as written. The verdicts of the campaign are those of `VERDICTS.md`; the others are shown next to them.

| Sample | Sigma of the joint read | Range of the joint read | Sigma of a port at rest | P1 | P2 | P3 | P4 | P5 |
|---|---|---|---|---|---|---|---|---|
| Campaign | 0.00128 | 0.26450 to 0.27000 | 0.071 mV | holds | fails | holds | holds | holds |
| Replay 1 | 0.00062 | 0.26645 to 0.26875 | 0.070 mV | holds | holds | holds | holds | holds |
| Replay 2 | 0.00106 | 0.26545 to 0.26960 | 0.070 mV | holds | holds | holds | holds | holds |
| Replay 3 | 0.00097 | 0.26555 to 0.26960 | 0.063 mV | holds | holds | holds | holds | holds |

- Of 4 samples: P1 holds on 4, P2 holds on 3, P3 holds on 4, P4 holds on 4, P5 holds on 4.
- Over the 4 samples the sigma of the joint read goes from 0.00062 to 0.00128, a ratio of 2.0.
- If the joint reads followed a normal law, a sigma measured on 20 runs would be uncertain by about 16%. Resampling the 20 runs of the campaign gives a wider interval: see the intervals in `VERDICTS.md`.
- The 60 joint reads of the replays together: sigma 0.00089, from 0.26545 to 0.26960.

### P2 on all the samples together

- 80 runs in 4 samples. Sigma inside a sample, the samples pooled: 0.00101.
- If every read follows one normal law: 95% interval from 0.00087 to 0.00120; one-sided 95% upper bound 0.00117, for a limit of 0.0012.
- With that sigma, a sample of 20 runs shows a sigma above 0.0012 about one time in 9.
- To know a sigma within 10% at 95%, about 190 runs are needed.
- Reserve: the variance of the largest sample is 4.2 times that of the smallest. Under one normal law, 4 samples of 20 differ that much with a probability of 1.4%. The interval above may therefore be too narrow.
- The verdict of the campaign on P2 stays as written: fails. The samples together put the sigma below the limit, with a small margin, under the reserve above.

## The two noisy refresh runs, repeated

The campaign has one run of each. They are run again four times each, with the same options. P14 and P17 are judged again on each run, as written.

### No leak, with noise, 150 pulses (P14: at most one relapse)

| Sample | Relapses | Distances between relapses | Band in doses | P14 |
|---|---|---|---|---|
| Campaign | 0 | — | 0.29 | holds |
| Repeat 1 | 0 | — | 0.22 | holds |
| Repeat 2 | 0 | — | 0.26 | holds |
| Repeat 3 | 0 | — | 0.29 | holds |
| Repeat 4 | 0 | — | 0.29 | holds |

Over 5 runs: 0 to 0 relapses, band from 0.22 to 0.29 dose.

### 0.1 TΩ, with noise, 150 pulses (P17: relapses 17 to 28 periods apart, never two silent pulses in a row, band within 1.6 dose)

| Sample | Relapses | Distances between relapses | Band in doses | P17 |
|---|---|---|---|---|
| Campaign | 7 | 23, 23, 22, 25, 21, 23 | 1.11 | holds |
| Repeat 1 | 7 | 22, 22, 23, 22, 22, 25 | 1.18 | holds |
| Repeat 2 | 7 | 24, 25, 22, 23, 23, 22 | 1.12 | holds |
| Repeat 3 | 7 | 22, 22, 24, 23, 21, 24 | 1.06 | holds |
| Repeat 4 | 7 | 22, 23, 23, 24, 21, 22 | 1.11 | holds |

Over 5 runs: 7 to 7 relapses, band from 1.06 to 1.18 dose, distances from 21 to 25 periods, mean 22.8.

## The charge received by the integrator

P10 checks the steering command. Here the current itself is measured: an ammeter of 0 V between the steering switch and the summing node of each integrator, integrated over each whole period (`gate_current.py`). A charge of 40.4 fC on the feedback capacitor of 30 pF is one dose, 1.3465 mV.

Charges in fC. For a pulse on both ports, both integrators are counted.

| Run | Silent pulses | Charge on a silent pulse | Firing pulses | Charge on a firing pulse: mean | largest in size | Periods at rest | Charge at rest: mean |
|---|---|---|---|---|---|---|---|
| `mc_2062` | 8 | 24.73 to 62.52 | 14 | 0.0393 | 0.2271 | 20 | -0.0036 |
| `mc_2064` | 9 | 32.53 to 43.79 | 13 | -0.0096 | 0.1766 | 20 | -0.0040 |
| `nom` | 8 | 39.83 to 40.87 | 14 | -0.0067 | 0.0295 | 20 | -0.0039 |
| `pvt_tt_125` | 14 | 40.08 to 41.00 | 8 | -0.0038 | 0.0149 | 20 | -0.0041 |
| `pvt_tt_m40` | 4 | 40.16 to 40.37 | 18 | -0.0064 | 0.0204 | 20 | -0.0044 |

- Largest charge received by an integrator on a firing pulse, runs without noise: 0.0295 fC, 0.07% of a dose, over 40 firing pulses.
- Largest charge received by an integrator on a firing pulse, runs with mismatch and noise: 0.2271 fC, 0.56% of a dose, over 27 firing pulses.
- The current of the ammeter alternates in sign from one time point to the next, an effect of trapezoidal integration. It limits this measure: the same effect spreads the charge of a silent pulse around one dose, and more so with noise.
- The stored voltage integrates the same current exactly. In these runs it is averaged from the time points, without the rounding to 1 µV of the campaign. The solver resolves a voltage to 0.1 µV.
- In the runs without noise, the mean change of the stored voltage over a period, toward a higher gain, is -0.22 µV on a firing pulse and -0.19 µV for a port at rest. A dose is 1346.5 µV.

## Do two runs of the campaign share a noise sample?

If two runs had the same noise sample, the changes of the stored voltage of their ports at rest would be the same. For every pair of noisy cell runs of the campaign, the correlation of these 20 changes is computed. This diagnostic can show a shared sample. It cannot prove that the samples are independent.

- 120 runs, 7140 pairs.
- Largest correlation: 0.76, between `mc_2045` and `mc_2059`. Pairs above 0.9: 0.
- For independent samples of 20 values the largest of 7140 correlations is expected near 0.71.
- No sign of a noise sample used twice in this diagnostic.
