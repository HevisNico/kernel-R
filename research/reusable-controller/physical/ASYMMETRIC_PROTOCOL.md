# Directional cumulative budget: rule A1

This rule is published before its first campaign eligibility calculation.
It is a new retrospective analysis rule, not the original preregistration of
#107/#109 and not a new held-out experiment. No eligible-port total is predicted.
The original 37 status-3 entries and report remain unchanged alongside A1.

## Scalar theorem

For nonnegative nominal dose d0, use separate directional bounds:

- z(0) - centre <= aSilent; centre - z(0) <= aFire;
- z(k) - z(0) - k*d0 <= BSilent for k < m only;
- z(0) + m*d0 - z(m) <= BFire at m only.

The two sufficient conditions are

```text
aSilent + BSilent + (20/17)*ell + 1/8000 < d0/2
aFire   + BFire   + (20/17)*ell          <= d0/2.
```

The threshold floor is unchanged: level0 - ell >= 19/20. The silence
inequality is strict; FIRE permits equality. The FIRE condition needs no
largest-rest-charge allowance. Directional offsets may be signed in the
abstract theorem. Its infinite NeedAlong conclusion still requires gain at
later indices to stay above z(m); finite certificates instead use a constant
extension as an internal proof device, imposing no post-FIRE physical premise.
The old symmetric theorem is a special case, not replaced or weakened.

## Frozen retrospective projection

Source: #109 commit `7ded279f103dab5beb6c1c671f1acbdf4cff18c0`, using the
same 200-port snapshot and hash as campaign_check.py. Targets m, nominal level,
d0, kappa, the old initial budget a, measured eps3 and per-cell h3 are frozen.
No retuning of targets, offsets or tolerance constants is allowed after A1's
first calculation. A change requires a new published rule and separate report.

For each original noisy #107 train, take every read from 0 through predicted
index m, not merely through its observed first FIRE. Missing reads, a nonpositive
log argument, or a FIRE latency below 0.76 make this projection not evaluable;
no count or gain is imputed. The same scalar read formula is used as before:
full q_peak on silent reads, q_tc at 0.75 plus kappa on FIRE reads. Call its
reported log gain y(k); the fixed response normalization cancels in differences.

Freeze epsKappa as the largest absolute difference between full and corrected
early log gain over all silent port-1/port-2 reads of the original 100 noisy
trains, exactly as #107; do not substitute the calibration-cohort statistic.
With MZ = 0.0002, define

```text
dev(k) = y(k) - y(0) - k*d0
r(k) = MZ + (epsKappa if read k fired, otherwise 0)
baseBSilent = max({0} union {dev(k) + r(k) + r(0) : 0 <= k < m})
baseBFire = max(0, -dev(m) + r(m) + r(0))
aSilent = aFire = old_a + eps3
BSilent = baseBSilent + 2*eps3
BFire = baseBFire + 2*eps3
ell = h3 + max(noise_sup_V(k)/0.5 : 0 <= k <= m) + 0.0002.
```

The abstract theorem permits sharper signed initial errors; A1 deliberately
keeps the old initial bound. The final FIRE's upward drift does not enter the
silence budget, but every applicable kappa/readout allowance remains paid.
Both occurrences of the initial reading's error are included when appropriate.

Use exact published decimals for nominal level/dose and old_a/eps3/h3.
New computed upper bounds are serialized to 12 significant decimal digits.
Before the exact rational room tests, widen each of old_a, eps3, baseBSilent,
baseBFire and ell upward by 1e-10, preserving their separate roles. Python
logarithms are numerical reconstruction, not a proved integration error bound.

Require all prefix rest charges in [0.1,0.1001], at most one latch rise per
read, a write on the selected port exactly on silent reads, and no write on
the other port. Keep the #109 same-cell check and threshold-floor gate. Both
room conditions must pass. Observed count agreement is an outcome column,
not an eligibility gate: an eligible contradiction must be reported as such.
Publish all 200 rows, both rooms, reasons, old/new membership and every change.
Generate separate Lean entries only after the rule commit is remote. Never
rewrite CampaignData.lean or campaign-validation.json to hide an old failure.

## Interpretation

This changes the sufficient scalar budget, not the measured waveform or the
model-to-circuit correspondence. The fitted eps3 offsets, declared integration
margin, noisy-run transfer, final-quarter FIRE correction, resting state and
physical detection envelopes retain their existing scope. Applying eps3 as a
bound on each actual read remains explicit. A larger eligible set would not
establish a universal error bound or a physical adaptive closed loop.
