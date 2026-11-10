# Prediction for the lower ERROR exit

Add a fourth write rule to the coincidence comparison. It uses R's
threshold-triggered discharge with nominal ERROR exit 0.0025 in place
of 0.025. ERROR entry stays at 0.1 and the sensor's READY rest stays at
0.025. Keep the full state after training. Reuse the 625 paired points,
FIRE and ERROR grid, three fabrication radii, three time scales, offsets
and jitter endpoints from the revised sweep.

Test two error conventions using the same dimensionless samples in
[-1, 1] and the same radius ε on each box.

| Convention | Entry tolerance | Exit tolerance |
| --- | ---: | ---: |
| Relative to each new threshold | 0.1 ε | 0.0025 ε |
| Absolute tolerances inherited from the original thresholds | 0.1 ε | 0.025 ε |

Both conventions perturb the exit around 0.0025. At the largest
registered radius of 5%, the absolute exit error is ±0.00125. FIRE
variation stays independent and uses its original relative convention.

At 100 µs per unit the relative-error hypothesis is that the modified R
passes exactly the same 27 ERROR × FIRE boxes as the duration-12
discharge, for each fabrication radius. The absolute-error prediction
is 23 passes out of 36 for each radius. Both predictions refer to the
sampled decision contract.

The nominal dose is 8 × (0.1 − 0.0025) = 0.78. Opposing entry and exit
errors give a dose half-width of 0.82 ε in the relative convention and
1.0 ε in the absolute convention. Linearizing the read response at dose
0.78 gives latency coefficients of approximately 0.496 per dose unit
and 0.552 per FIRE unit. The available per-cell margin is 0.025 model
units. The linear screen estimates 26 relative passes and 23 absolute
passes. The registered relative hypothesis of 27 is stronger than this
screen. Compare the actual pass sets in addition to the counts.

The nominal ERROR duration rises to approximately 0.399 units at the
lower exit, using log(0.1 / 0.0025) divided by the nominal discharge rate.
The timed discharge results and the original R results provide the
reference for this modified write duration.

## Required checks before scoring

For each error convention and every tested cell and trained port, record
the latest training ERROR exit, the largest sensor residual at read,
and the smallest log-gain headroom. All three checks must hold.

1. Training ERROR ends before time 2. Use the latest exit from the
   actual sample, including the lowest perturbed exit threshold.
2. The sensor is in READY at read, with absolute distance at most
   0.00002 from its READY rest of 0.025. Evaluate the exponential
   relaxation from the exit threshold to the earliest registered
   arrival, 16.3 at 50 µs per unit. This bounds the residual at the
   nominal read at 17 and all registered later arrivals.
3. No training write contacts its gain cap. Check the full perturbed
   dose against log(cap / 1.2) at each point. The nominal dose is 0.78
   and the absolute error grid allows at most 0.83. The smallest
   allowed gain cap is 3.6, so the smallest nominal headroom before
   the write is log(3.6 / 1.2), approximately 1.09861.

Any failed check invalidates the comparison. The relative hypothesis
requires equality of the pass sets, even when both counts are 27.
Keep the prediction document at a commit preceding the runner revision
that enforces these checks. Record both commits in the output.

The new comparator uses the existing reduced numerical runner. Its
outputs describe the sampled cases under the same report guards and
carry the commit that registered these predictions.
