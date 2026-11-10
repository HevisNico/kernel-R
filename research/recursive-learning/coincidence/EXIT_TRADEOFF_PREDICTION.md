# Registered ERROR exit tradeoff

Evaluate R with nominal ERROR exit 0.025, 0.01, 0.005 and 0.0025 on
the same 625 paired points. Keep nominal ERROR entry at 0.1 and sensor
READY rest at 0.025. Use independent errors with absolute half-widths
0.1 ε at ERROR entry and 0.025 ε at ERROR exit for all four designs.
Use the original relative FIRE convention and the same fabrication
radii, time scales, offsets, jitter endpoints and report guards. Keep
the three training checks from the lower-exit protocol.

The primary score is the number of passing ERROR × FIRE boxes out of
36 at 100 µs per unit, reported separately for each fabrication radius.
At nominal log-gain dose d, the first-order screen uses a per-cell
timing budget of 0.025 units. At the nominal read crossing, the
absolute ERROR-box radius changes d by at most ε and FIRE changes
the crossing threshold by at most its own box radius. The linear
latency coefficients follow by implicit differentiation of the
READY response. The rows at 0.025 and 0.0025 already have measured
scores of 16 and 23. The two middle rows are prospective predictions.

| Nominal exit | Nominal dose | ERROR coefficient | FIRE coefficient | Predicted score | Nominal levels below cap | Guaranteed levels below cap |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0.025 | 0.60 | 0.769 | 0.854 | 16 | 3 | 2 |
| 0.01 | 0.72 | 0.566 | 0.629 | 22 | 2 | 2 |
| 0.005 | 0.76 | 0.518 | 0.576 | 22 | 2 | 2 |
| 0.0025 | 0.78 | 0.496 | 0.552 | 23 | 2 | 2 |

Count the initial gain 1.2 and each successive full dose whose gain
stays strictly below the cap. Keep the capped state separate. For a
fixed dose and cap, the count is ceil(log(cap / 1.2) / dose), including
the initial state. Use cap 4 for nominal capacity. Use cap 3.6 and
dose d + 0.05 for the guaranteed count over the widest fabrication
and absolute-error boxes. These counts describe memory increments.
The timing experiment applies one training pulse and does not measure
a sequence of writes or the distinguishability of levels across cells.

Plot the four measured scores alongside the predicted scores and
annotate both capacity counts. Use the wide fabrication box for the
primary plot and report all three fabrication radii in the results.
The prediction and capacity definitions are frozen before the runner
revision and the sweep.
