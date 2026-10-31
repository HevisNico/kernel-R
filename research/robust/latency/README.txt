NOISE-DEPENDENT LATENCY AND CHAIN PERIOD

Read THEOREM.md. This layer pins the robust birth certificate and bounds the
regular firing latency relative to the same cell's actual learned-gain reference.
The input-period condition is

  T >= 7.5 + 2 sum_{i=0}^{N-2}(sigma_i + delta_i).

sigma_i is a +/- link phase radius; delta_i is a +/- latency phase radius.
The final cell's radius affects root output jitter, but not a successor's input
spacing unless the chain is extended. The first firing's positive residual
becomes a nonnegative advance, absorbed by prefix removal; its delay is bounded.

Uniform certified radii (not claimed optimal):
  epsilon   nu       alpha    delta
  .003      0        0        0
  .003      .002     0        .00745
  .003      0        .09      .22240
  .003      .0015    .05      .11022
  .1        0        0        0
  .1        .002     0        .00748
  .1        0        .09      .22240
  .1        .0015    .05      .11088

For epsilon=.1,nu=.002,alpha=0, fixed wires and N=32, the minimum sufficient
period is 7.96376. Period 8 therefore satisfies the new bound, versus 23 under
the previous full-envelope bound. The symmetric radius is less sharp at the
largest amplitude deviation; the earlier sufficient condition remains available.

The conjectured uniform radius .003 is too small when arbitrary long silence
is allowed. A constant +.002 main disturbance can bring the starting excess
near .004. An integer-interval regression exhibits a learned reference root
above .653 and an admissible perturbed root below .650. A tighter theorem that
uses a bound on the preceding quiet interval could have a smaller radius.

From the package root:
  python -B latency/tests.py -v
  python -B latency/verify.py latency/certificates/eps0.1_nu0.002_alpha0.json
  python -B latency/chain.py latency/certificates/eps0.1_nu0.002_alpha0.json --n 32 --k 104 --period 8
  python -B latency/validate.py
  python -B latency/validate.py --verify-record

The numerical campaign starts every cell from birth, then runs at the tighter
periods. It checks local doses/modes/probes plus the reference-latency radius
and accumulated packet-phase bounds. Simulations corroborate the written proof;
integer interval replay checks the finite inequalities. Neither is full Lean
verification. No Lean work or GitHub write is part of this deliverable.

The phase-budget theorem is parametric in certified radii. Stored numerical
certificates cover the eight listed parameter points; no unchecked interpolation
between points is asserted. A new point requires a fresh birth and latency replay.
