# Coincidence benchmark results

The longer discharge passed every tested box in which R passed across
the three time scales and fabrication radii. At the primary scale it
passed 27 of 36 ERROR × FIRE boxes per fabrication radius. R passed 16.
The capped constant-current comparator also passed all 36 in the narrow
box and 12 in the wide box at ±10% current error. These runs support
the benefit of writing from a decaying sensor for this task. They give
no timing advantage to terminating the write at R's lower ERROR threshold.
R uses a threshold to end the write without a clock. The experiment
does not measure repeated operation or rearm throughput.

The revision used 625 paired points per box, comprising the original
621 and four joint ERROR/FIRE corners. The duration and corner grid was
fixed in `a2a169a0f5b8130ca5516630e428714cbe4e85b0` before the rerun. The expected
16 passes and the duration at which the ablation matches duration 12
were not recorded as predictions in that commit. Treat these comparisons
as exploratory. The [first report](https://github.com/HevisNico/kernel-R/blob/890b3ac744b908d41f0e19a712e652345006df6d/research/recursive-learning/coincidence/RESULTS.md)
and its data remain available.

## Opposite ERROR and FIRE corners

Each new point sets ERROR entry high, ERROR exit low and FIRE low
in one cell, and reverses all three signs in the other. Both ports
and both cell orders are covered. At 100 µs per unit the revised
points changed the following pass decisions for R.

| Fabrication | First run | Revised run | Lost ERROR/FIRE pairs |
| ---: | ---: | ---: | --- |
| 0% | 17 | 16 | 3% / 0.3% |
| 0.3% | 17 | 16 | 3% / 0.3% |
| 10% | 17 | 16 | 3% / 0.3% |

With ERROR at 1% and FIRE at 2%, R still passed in the wide box.
Its minimum sampled margin was +0.038073 µs.

## Current mismatch frontier

Wide fabrication box, 100 µs per unit, with nominal ERROR and FIRE.
Entries give the smaller of positive and negative timing slack in µs.
Positive values pass. Dose 1 uses the shared duration 12 and is clipped
by the realized cap if needed. The archive contains all other slices.

| Current error radius | Nominal timer, dose 0.6 | Dose 1 | Wide cap |
| ---: | ---: | ---: | ---: |
| 0% | +4.999235 | +4.999639 | +0.166627 |
| 0.3% | +4.731433 | +4.808814 | +0.166627 |
| 1% | +4.106525 | +4.363541 | +0.166627 |
| 3% | +2.319610 | +3.090544 | +0.166627 |
| 5% | +0.527737 | +1.814808 | +0.166627 |
| 10% | -3.997659 | -1.399827 | +0.166627 |

At ±10% current error, the capped timer in the wide fabrication box
retains +0.004346 µs of slack at ±0.3% FIRE and has −0.374641 µs
at ±1% FIRE with ERROR nominal.

## Discharge duration

The table counts passing ERROR × FIRE boxes out of 36 in the wide
fabrication box at 100 µs per unit.

| Duration | Passing boxes |
| ---: | ---: |
| 0.15 | 8 |
| 0.2 | 17 |
| 0.25 | 19 |
| 0.3 | 25 |
| 0.35 | 26 |
| 0.4 | 27 |
| 0.45 | 27 |
| 0.5 | 27 |
| 0.55 | 27 |
| 0.6 | 27 |
| 0.65 | 27 |
| 0.7 | 27 |
| 0.8 | 27 |
| 1 | 27 |
| 1.5 | 27 |
| 2 | 27 |
| 4 | 27 |
| 8 | 27 |
| 12 | 27 |

The following is the first tested duration from which all later tested
durations have the same pass set as duration 12.

| Scale (µs/unit) | Nominal fabrication | ±0.3% | ±10% |
| ---: | ---: | ---: | ---: |
| 50 | 0.3 | 0.3 | 0.3 |
| 100 | 0.4 | 0.4 | 0.4 |
| 200 | 0.35 | 0.35 | 0.5 |

At the primary scale, 0.4 is 2.67 times R's nominal ERROR duration
of 0.15. This is a ratio of write durations in this experiment.

## Coverage

Each row counts passing ERROR × FIRE boxes. Timer results use ±10%
current error. The optimized timer is the best of the tested common
settings. The continuous optimization problem remains open.

| Scale (µs/unit) | Fabrication radius | R | Nominal timer | Cap candidate | Best tested timer | Discharge 12 |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 50 | 0% | 30 | 18 | 36 | 36 | 36 |
| 50 | 0.3% | 30 | 18 | 36 | 36 | 36 |
| 50 | 10% | 30 | 18 | 36 | 36 | 36 |
| 100 | 0% | 16 | 0 | 36 | 36 | 27 |
| 100 | 0.3% | 16 | 0 | 36 | 36 | 27 |
| 100 | 10% | 16 | 0 | 12 | 12 | 27 |
| 200 | 0% | 8 | 0 | 30 | 30 | 14 |
| 200 | 0.3% | 8 | 0 | 30 | 30 | 14 |
| 200 | 10% | 8 | 0 | 0 | 0 | 14 |

## Lower ERROR exit

The [registered fourth-comparator run](LOWER_EXIT_RESULTS.md) evaluates
exit 0.0025 under relative and inherited absolute threshold errors.

## ERROR exit tradeoff

The [registered absolute-error sweep](EXIT_TRADEOFF_RESULTS.md) plots the
timing score and levels below the gain cap at four exit thresholds.

## Evidence and scope

The reduced equations and constants are a Python transcription of the
pinned Lean source. There is no machine-checked correspondence between
the runner and the Lean semantics. The independent numerical
[DOP853 code](verify_ivp.py) and [its 24 outputs](results/ivp.csv) compare
first report latency and gain on selected trajectories.

The no-missing, no-extra, untrained-silence and training-silence results
follow from the runner's guards completing on the sampled inputs. The
first CSV encoded these conditions as literal zeros. The revised CSV
uses `report_guards_passed` to distinguish them from observed event counts.

The [revised sweep CSV](results/sweep.csv.xz) and the
[first sweep CSV](results/sweep-first.csv.xz) are compressed with xz.
The [manifest](results/manifest.json) records the hashes of the uncompressed
CSVs and the runner, protocol and model commits. The [runner guide](README.md)
gives the reproduction commands.
