# Robust composition of an arbitrary finite prepared chain

This extends the **prepared, slow-input local theorem** in THEOREM_ROBUST.md.
It is not an extension of the repository's distinct fast-packet N-cell protocol.
No entry from birth, feedback, branching or settings transfer is asserted.

## Hypotheses

Let N >= 1 and K >= 3N+1 be integers. Index cells i=0,...,N-1 in signal order.
Each cell starts at time zero in the local prepared section, with its own admissible
initial coordinates. Its port 2 receives only the preceding cell's emissions;
cell 0 receives K source pulses at 0,T,...,(K-1)T. Each edge carries every emission
exactly once, without merging or duplication, with independently varying delay
in [0.3,0.4]. Received waveforms have unit support and the local amplitude bound.

Use one of the eight certified (epsilon,nu,alpha) points. All parameter, noise
and amplitude histories may differ across cells and ports, may be correlated,
and may be arbitrary measurable functions within their bounds. No rate bound,
probabilistic independence or repeatability of firing latency is assumed.
An outgoing canonical waveform is triggered by a firing independently of the
noisy FAST exit; this is an explicit model assumption, not a hardware derivation.

Require

    T >= 7.5 + 0.5(N-1).

The default T=max(8,7.5+0.5(N-1)) retains the original period 8 at N=1,2.
This is a sufficient, deliberately conservative schedule. Failure of this
inequality is refusal of this contract, not proof that a faster chain fails.

## Local input/output lemma

A prepared cell receiving L >= 4 pulses with successive gaps at least 7.5 emits
exactly L-3 times. The first three inputs are silent and each gives one full
ERROR dose; every subsequent input emits exactly once, with latency in (0.5,0.9].
Its active gain then stays fixed, b stays unchanged, and every auxiliary cycle
and main protected cycle finishes before the next input. Every dose belongs to
the local gain_log_dose interval. The local proof's Steps 1–6 depend only on the
minimum gap, not on L or the absolute calendar. After the last input the same
return bound applies and silence cannot create another emission.

Before the first input, no auxiliary reaches threshold and no actuation occurs.
The comparison solution gives |q-r| <= delta+nu/kappa and similarly for m-r_m.
The new obligation arbitrary_initial_silence_inside_section puts the positive
main excess below Q. Thus arbitrarily long waiting before the first input does
not assume preservation of the much smaller initial delta section.

## Induction and timing

Define d_i(k) as the delay on edge i for pulse k and ell_i(k) as the firing latency
of cell i for its corresponding input. The bounds are d_i(k) in [0.3,0.4] and
ell_i(k) in (0.5,0.9]. A downstream cell discards its first three input pulses.
Consequently the k-th output of cell i corresponds to source ordinal

    s = k + 3(i+1),      0 <= k < K-3(i+1).

For adjacent surviving source ordinals, each upstream latency can reduce the
arrival gap by at most 0.4, and each edge delay by at most 0.1. The input gap at
cell i is therefore at least T-0.5i >= 7.5. For i=0 this is immediate; after the
local lemma at cell i, routing its outputs establishes the bound for i+1.
Removing a prefix creates no smaller successive gap. This proves the local
lemma's premise at each stage without presupposing downstream firing.

Summing the latency and delay intervals gives the k-th output hull

    F_i(k) in [T(k+3(i+1)) + 0.8i + 0.5,
               T(k+3(i+1)) + 1.3i + 0.9].

The left endpoint is conservatively closed. Since K>=3N+1, every cell has at
least four inputs and the root has at least one output.

## Conclusions for every finite N

- Cell i receives K-3i pulses and emits K-3(i+1) pulses.
- The root emits K-3N pulses.
- Total traffic is N*K - 3*N*(N+1)/2.
- Every cell receives exactly three complete active-port ERROR doses before its
  first emission, and none afterwards. Its active log gain is the initial value
  plus these three (possibly different) doses; b is unchanged.
- Each isolated standardized-rest, plasticity-disabled copy changes from 0/8 to
  8/8 under period-20 probes, with its own admissible histories.
- If R is the local certified main_reopen_bound, every cell is READY, with no raw
  or outgoing current and no protected auxiliary, by

      (K-1)T + 1.3(N-1) + R.

Indeed the last input of cell i is no later than (K-1)T+1.3i. The local main
return is before R after that input; the auxiliary and outgoing waveforms finish
earlier by the local ordering inequalities. Subsequent silence preserves READY.
Nonzero charge noise does not imply exact return to the resting *charge* after
this instant; quiescence here means modes and currents, not noise-free charges.

Choosing K=3N+8 guarantees eight root emissions. The certificate remains local:
its 36 interval inequalities do not grow with N. chain.py checks concrete counts
and dates with exact rational arithmetic. This written induction provides the
universal-N bridge; numerical sampling of several N does not prove universality.

## What is checked and what is assumed

Integer arithmetic independently replays the local enclosures; its formulas
are shared with the Decimal producer. The local comparison argument and this
induction are written proofs, not a formal Lean verification. Floating-point
hybrid tests independently exercise the differential equations and event order,
including tolerance refinement, but do not enclose all admissible histories.
All conclusions are conditional on the prepared section, bounded disturbances,
canonical unit-support emissions and delivery assumptions above. In particular,
this does not prove robustness of the original period-4 fast-packet chain.
