# Complement to the campaign

Run after the campaign by `complement.py` and read by `compare.py`. Nothing here is a prediction, and nothing here replaces a verdict.

## The runner without the new option

The option `rel` was added to `run.py` after the campaign. Runs without noise are run again without it. They must give the result of the campaign exactly: if they did not, something else than the noise would vary from one run to the next.

- `nom`: identical byte for byte to the result of the campaign.

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

- Over the 2 samples the sigma of the joint read goes from 0.00062 to 0.00128, a ratio of 2.0.
- If the joint reads followed a normal law, a sigma measured on 20 runs would be uncertain by about 16%. Resampling the 20 runs of the campaign gives a wider interval: see the intervals in `VERDICTS.md`.
- The 20 joint reads of the replays together: sigma 0.00062, from 0.26645 to 0.26875.

## The two noisy refresh runs, repeated

The campaign has one run of each. They are run again four times each, with the same options. P14 and P17 are judged again on each run, as written.

### No leak, with noise, 150 pulses (P14: at most one relapse)

| Sample | Relapses | Distances between relapses | Band in doses | P14 |
|---|---|---|---|---|
| Campaign | 0 | — | 0.29 | holds |
| Repeat 1 | — | — | — | not evaluable: run missing |
| Repeat 2 | — | — | — | not evaluable: run missing |
| Repeat 3 | — | — | — | not evaluable: run missing |
| Repeat 4 | — | — | — | not evaluable: run missing |

### 0.1 TΩ, with noise, 150 pulses (P17: relapses 17 to 28 periods apart, never two silent pulses in a row, band within 1.6 dose)

| Sample | Relapses | Distances between relapses | Band in doses | P17 |
|---|---|---|---|---|
| Campaign | 7 | 23, 23, 22, 25, 21, 23 | 1.11 | holds |
| Repeat 1 | — | — | — | not evaluable: run missing |
| Repeat 2 | — | — | — | not evaluable: run missing |
| Repeat 3 | — | — | — | not evaluable: run missing |
| Repeat 4 | — | — | — | not evaluable: run missing |

## Independence of the noise samples of the campaign

If two runs had the same noise sample, the changes of the stored voltage of their ports at rest would be the same. For every pair of noisy cell runs of the campaign, the correlation of these 20 changes is computed.

- 120 runs, 7140 pairs.
- Largest correlation: 0.76, between `mc_2045` and `mc_2059`. Pairs above 0.9: 0.
- For independent samples of 20 values the largest of 7140 correlations is expected near 0.71.
