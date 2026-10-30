# Continuous noise-dependent phase budget for robust chains from birth

## Reference and scope

Start with the pinned birth-entry certificate and its widened local continuation
section. The preparation from birth, routes, parameter boxes and waveform/noise
assumptions remain unchanged. In cell i, let g_i be its **actual gain after its
three port-2 ERROR doses**, including any noise contribution to those doses.
This gain is constant during every subsequent emitting input by the local gate
ordering. Define ell_i* as the first crossing of r+g_i h(t)=1 from exact rest.
This is not the latency at the nominal gain .3 exp(1.8).

Let delta_i bound the absolute deviation of a regular firing latency from ell_i*.
It is a phase radius, not a bound on the difference of two successive latencies;
that difference can be as large as 2 delta_i. The bounds below are uniform over
the whole certified learned-gain interval, not fitted to the sampled trajectories.

## 1. A uniform perturbation envelope

After a main guard return, q=r. With bounded noise during any subsequent silence,
|q-r|<=nu/kappa. This invariant applies before every regular emitting input.
The sum of the propagated initial error and further input-time charge noise is
bounded by nu/kappa, since

    (nu/kappa) exp(-kappa*t) + nu(1-exp(-kappa*t))/kappa = nu/kappa.

The two terms must not be added without their decay weights. A received multiplier
in [1-alpha,1+alpha] changes the convolution by at most alpha*g_i*h(t). Before the
first crossing, and before ERROR can start, the READY trajectory is therefore
between

    r + g_i h(t) +/- [nu/kappa + alpha*g_i*h(t)].

The first emitting input can have a larger positive residual after the three
silent inputs, so its early bound needs separate treatment. Its negative excess
is still at least -nu/kappa: after birth preparation a main return has occurred,
and nonnegative drives preserve this lower invariant through the silent inputs.
Thus the lower trajectory envelope remains valid for the first emission.

## 2. Checked radius around the reference root

The certificate encloses every ell_i* in [u-,u+] by checking the learned-gain
endpoints at u- and u+. It verifies h''<0 through the raw window, and h'>0 on the
needed interval. For a proposed d>0, with u--d>0 and u++d<.9, define

    S_late  = g_min [h(u++d)-h(u+)],
    S_early = g_min [h(u+)-h(u+-d)],
    E_late  = nu/kappa + alpha*g_max*h(u++d),
    E_early = nu/kappa + alpha*g_max*h(u+-d).

Concavity makes each fixed-width increment smallest at the latest reference
root u+. Monotonicity bounds the amplitude error at the same latest date.
The verifier requires S_late>E_late and S_early>E_early, with strict rational
interval separation. Hence the upper trajectory is below threshold at ell_i*-d,
and the lower trajectory exceeds threshold at ell_i*+d. The upper envelope is
increasing, so the early comparison excludes all earlier crossings as well.
Continuity then puts every regular first crossing within this radius. The .9
limit keeps the calculation before the earliest ERROR start in the local proof.

This finite-difference comparison is a checked version of the inverse-slope
perturbation argument; it avoids replacing a curved response by an unchecked
constant slope. A minimum-slope bound is also recorded. At nu=alpha=0 the exact
constant-latency argument gives d=0, with no artificial rounding floor.

## 3. The first firing and packet induction

The lower trajectory bound gives ell_first <= ell_i*+delta_i. Define

    a_i = max(ell_i*-ell_first,0),
    e_i,first = max(ell_first-ell_i*,0).

Then a_i>=0, e_i,first<=delta_i, and ell_first=ell_i*-a_i+e_i,first.
Every subsequent latency is ell_i*+e_i,k with |e_i,k|<=delta_i. Thus a cell maps
an input packet with one advanced first pulse and phase radius J to an output
packet with its own nonnegative first advance and radius J+delta_i. The first
three inputs are silent, so the incoming exceptional first pulse is discarded.
Adding a link with errors in [-sigma_i,sigma_i] increases J by sigma_i. No fixed
reference latency ell_i* contributes to phase spread; it only shifts the calendar.

At the input of cell j, the accumulated phase radius is

    J_j = sum_{i<j}(delta_i+sigma_i).

The first gap is at least T+a-2J_j and every later gap at least T-2J_j. Therefore
it suffices to require

    T >= 7.5 + 2 sum_{i=0}^{N-2}(delta_i+sigma_i).

The last cell's delta is absent from this input-spacing condition because it has
no successor; it is included in the root output packet's phase radius. If the
chain is extended, that cell's delta must enter the new input budget. Each link
uses a fixed delay center in [.3+sigma_i,.4-sigma_i], 0<=sigma_i<=.05.

Counts and memory/probe conclusions are unchanged: K>=3N+1 gives K-3N root
outputs, or eight with K=3N+8. All statements start at the declared birth state,
using the externally driven parallel warm-up of birth/THEOREM.md.

## Interpretation and limitations

When nu=alpha=0, delta=0 and the periodic wire-jitter result is recovered exactly.
For nonzero disturbances the depth penalty scales with the certified phase
radius rather than the entire local .4 latency hull. Fixed per-link jitter still
accumulates unless a global budget is imposed. A uniform nonzero delta also gives
a depth-dependent period; the result does not make arbitrary noisy chains free
of timing spread.

The radius covers arbitrarily long silent intervals. A conjectured value such
as .003 must be checked against that scope: under long positive-noise silence,
the initial charge offset can approach nu/kappa. A bound for period-8 trajectories
alone could be smaller but would be a different, more tightly coupled theorem.
The certificates give sufficient upper bounds, not optimal sensitivity constants.

As before, interval arithmetic is independently replayed but formulas are shared;
the hybrid first-crossing and packet arguments are written, not fully Lean
formalized. Numerical scenarios and refinement are corroborating evidence only.

The radius method is not guaranteed to improve every large-amplitude point.
The previous full-hull period bound remains available; one may choose the smaller
of the two independently certified sufficient periods. In particular the symmetric
radius about the unperturbed reference can be conservative for asymmetric large
amplitude effects.
