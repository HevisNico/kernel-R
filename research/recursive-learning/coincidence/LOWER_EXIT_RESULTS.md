# Lower ERROR exit results

The modified R cell with nominal ERROR exit 0.0025 passed 26 of 36
boxes with relative threshold errors and 23 with the inherited
absolute tolerances at 100 µs per unit. The duration-12 ablation
passed 27. The 27-case equality hypothesis failed. The absolute
prediction of 23 held in all three fabrication radii.

The run used the [registered protocol](LOWER_EXIT_PREDICTION.md) at
`449d823eb273a9cf52910204d6950a75e53530af` and the subsequent runner at
`44dc8e09530fa55ad903cda383efacfb5774f3f9`. The 625 sample coordinates
are byte-identical to those used for the revised sweep.

| Scale (µs/unit) | Original R | Duration 12 | Lower exit, relative | Lower exit, absolute |
| ---: | ---: | ---: | ---: | ---: |
| 50 | 30 | 36 | 36 | 35 |
| 100 | 16 | 27 | 26 | 23 |
| 200 | 8 | 14 | 14 | 12 |

Counts and pass sets were identical across the three fabrication radii
at each scale. At 100 µs per unit, the relative pass set lacked only
ERROR ±5% with FIRE ±1% compared with duration 12. In the wide box
the margin on that case was −0.188791 µs for the modified R cell
and +0.119672 µs for duration 12. The absolute pass set lacked that
case and three more, ERROR ±2% with FIRE ±3%, ERROR ±3% with FIRE ±2%,
and ERROR ±5% with FIRE ±0.3%.

All registered training checks passed. The extrema include both
training ports and both cells at every sampled point.

| Check | Relative | Absolute |
| --- | ---: | ---: |
| Latest training ERROR exit | 1.680132 | 1.720957 |
| Largest sensor residual at earliest read | 0.0000150961 | 0.0000161147 |
| Smallest remaining log-gain headroom | 0.282128 | 0.274605 |

At the earliest read at 16.3, the sensor was READY and within
0.00002 of its rest charge in both conventions. No training write
touched the cap. The absolute convention uses the original exit
threshold 0.025 to scale error around the new exit 0.0025.

These are numerical results for the shared sample and the same
report guards as the original comparison. The solver is the
reduced Python transcription described in the [runner guide](README.md).

The [CSV](results/lower-exit.csv.xz) and [manifest](results/lower-exit-manifest.json)
record all margins and checks. Run from the repository root with the
pinned dependencies in the runner guide.

```sh
python research/recursive-learning/coincidence/compare_exit.py output/lower-exit \
  --protocol-commit 449d823eb273a9cf52910204d6950a75e53530af \
  --runner-commit 44dc8e09530fa55ad903cda383efacfb5774f3f9
```
