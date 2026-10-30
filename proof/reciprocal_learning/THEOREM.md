# Local theorem: A learns from B on a real parameter box

## Statement and scope

Fix epsilon in {0.003, 0.1}. In each of two three-port R cells A and B, all five
original physical parameters (C, Lm, Ls, Le, M) of every port are independently
chosen in the relative box [1-epsilon, 1+epsilon] around their original nominal
values, and remain constant. This is a 30-parameter physical box. Constants a,
kappa, r, r_m, thresholds, phase endpoints, actuation factors and the energy law
are those of the unchanged R kernel.

Immediately before local time 0, both cells are in this **prepared section**:

- Main and all auxiliaries are READY; no raw or outgoing currents are active.
- q is in [0.09999,0.10001]; every auxiliary charge is in [0.02499,0.02501].
- The gain of port 2 is `0.3 * exp(eta)`, with eta in [-1e-5,1e-5].
- b is in [0.17999,0.18001]; E is in [50,100].
- Other gains are arbitrary positive values below their own caps.

B receives sixteen canonical pulses on port 2 at 0,8,...,120. Each emission of B
reaches A's port 2 with a delay independently in [0.3,0.4]. There are no other
inputs, no A->B route and no settings copies during this phase.

Then, for every admissible real parameter and section-state choice:

1. B emits exactly 13 pulses and A emits exactly 10.
2. A receives exactly three complete, uncapped ERROR doses while READY before its
   first emission. Its active log-gain increases by exactly 9/5, and is unchanged
   by every later input in the phase. Its b is unchanged.
3. Hence `g_A_final = g_A_initial * exp(9/5)`, enclosed by
   [1.8148760904722349957656331678657619638566,
    1.8149123883570220784068819983289122355248].
4. By local time 139.9, both cells are READY with no active currents or auxiliary
   protected phases. Their introduced states have never been reset.
5. An isolated standardized-rest copy of A, retaining its own physical parameters
   and b, with plasticity disabled, responds to 0 of 8 port-2 pulses spaced by 20
   before learning, and exactly once to each of the 8 afterwards.

This is a conditional theorem from the explicit prepared section. It does not
prove that every trajectory of the earlier full prototype reaches this section.
Local time 0 corresponds to prototype time 320, and 139.9 to 459.9. The section
is preserved by silence between prototype times 319.9 and 320.

## 1. Auxiliary first crossing and one cycle per input

Write a=ln(4), kappa=1/2, r_m=1/40, and

`h(t) = a/(a-kappa) * (exp(-kappa*t) - exp(-a*t))`.

Before its first threshold crossing under a canonical pulse, an auxiliary has

`m(t) = r_m + (m(0)-r_m)*exp(-kappa*t) + M*h(t)`.

The outward checks establish m(0.015)<1, m(0.03)>1, and a strictly positive
m'(t) for all t in [0,0.03]. Together with m(0)<1 this proves a unique first
crossing tau in (0.015,0.03), uniformly over the box.

The subsequent section endpoints are exact. Their dates lie in:

- MARK end: `tau + ln(5/4)/Lm`;
- ERROR start: `tau + ln(5/4)/Lm + ln(8)/Ls`;
- ERROR end: the previous expression plus `ln(4)/Le`.

The certificate proves that ERROR ends after raw-current end 1 and before the
next input, whose minimum possible gap is 7.5. Consequently the active auxiliary
executes one cycle per input and reaches exactly r_m after the raw current is off.
Other auxiliaries receive no input; they remain READY below threshold and their
charges relax within the initial small interval.

An entire ERROR section received with the main cell READY and no cap contact has

`Delta z = 8 * integral(Le*m dt) = 8*(1/10-1/40) = 3/5`.

This is an endpoint identity in the real dynamics. It does not assume that two
independent interval copies of Le cancel numerically.

## 2. A uniform input section for the main charge

At every active-port input, use the invariant charge enclosure

`q-r in [-1e-5, 0.03]`.

It contains the prepared section. After an emitting cycle q returns exactly to r.
After a silent cycle, the bound below returns q to this same section before the
next input. Lower invariance follows from the nonnegative drive and relaxation
towards r.

With a fixed gain g and while READY during the raw pulse,

`q_g(t) = r + (q(0)-r)*exp(-kappa*t) + g*h(t)`.

Multiplying its derivative by exp(a*t) gives

`exp(a*t)*q_g'(t) = g*a^2/(a-kappa)
  - kappa*(q(0)-r+g*a/(a-kappa))*exp((a-kappa)*t)`.

The certificate proves the coefficient of the last exponential is positive and
the whole expression at t=1 is positive. Therefore q_g is strictly increasing
on [0,1], for every state in the section and every gain used below.

## 3. The first three inputs cannot make the main cell fire

Let D=3/5 and `g_j = g_initial * exp(j*D)`, j=0,1,2. A complete ERROR can increase
g by at most `J_j=g_j*(exp(D)-1)` before any cap, regardless of the main gate.
Let e_- be the certified lower bound on ERROR start.

For any hypothetical READY trajectory up to a possible first main crossing,
variation of constants bounds the gain-current overlap by

`0 <= q(t)-q_gj(t)
   <= J_j * a*exp(-a*e_-) * max(0,1-e_-)`, for 0<=t<=1.

The leaky integrating factor is at most 1, the gain increment is at most J_j,
and the canonical current on the possible overlap is at most a*exp(-a*e_-).
Before e_- there is no gain actuation; after time 1 there is no raw drive.

The certificate proves that q_gj(1) plus this entire overlap bound is <1 for
each j. Since q_gj increases, this rules out a first crossing anywhere in [0,1].
After raw-current end, charge relaxes towards r<1, so it cannot fire later either.
This argument does not assume the conclusion that the main cell stays READY.
It uses a priori gain and current bounds up to a hypothetical first crossing.

At epsilon=0.1, e_- may be below 1. Thus both compatible orders of ERROR start
and raw-current end are covered by the same envelope. No floating-point event
priority is used. At epsilon=0.003, the overlap bound is zero.

With p_j the certified peak bound and minimum gap G=7.5,

`q_next-r <= (p_j-r)*exp(-kappa*(G-1)) < 0.03`.

The main charge section is therefore invariant across these silent inputs.
The entire ERROR is received while READY. Its energy gate is open (Section 6),
and even g_3 lies below the smallest cap in the box, so each dose is exactly D.
This proves the three successive gains g_1, g_2 and g_3, without cap contact.
MARK occurs while the main cell is READY, so b does not change.

## 4. Every subsequent input emits once and preserves gain and b

For g_3, the certificate proves q_g3(0.5)<1 and q_g3(0.9)>1, with strict increase
as above. ERROR cannot start before 0.9, so gain is constant throughout the
root bracket. Thus the first main firing latency is in (0.5,0.9).

The whole MARK ends before 0.5, so it precedes main firing and cannot change b.
ERROR starts after 0.9 and ends before 1.5. FAST starts at the actual firing and
lasts exactly 1; its end is later than 1.5. Hence the entire ERROR is protected
by FAST, and contributes zero gain dose. This ordering is strict over the box.

With b unchanged, the total return latency is bounded by

`0.9 + 1 + ln(5/2)/b_min < 6.990787 < 7.5`.

At return, the raw current and auxiliary cycle are over. The main charge is
exactly r, no further firing can occur without input, and the same section is
ready for the next pulse. This proves the stable one-response regime inductively.

## 5. Composition of the two cells

B receives 16 pulses with gap 8. Sections 1–4 imply exactly three silent inputs,
then 13 canonical emissions. Their date hulls are

`8*j + [0.5,0.9]`, j=3,...,15.

After the independent link delays, A's input date hulls are

`8*j + [0.8,1.3]`.

Consecutive hulls are separated by at least 7.5. In particular, pulse supports do
not overlap and Section 1's auxiliary separation holds. The positive delays
preserve causality. Independence of the delay jitter only enlarges this enclosure.
A has no input before the first such arrival, so silence preserves its prepared
charge enclosure. Applying Sections 1–4 to A gives three silent inputs, then ten
emissions and exactly three ERROR doses. No value is copied from B's settings.

A completes its third gain dose before local time 42.697. Its first emission is
in [49.3,50.2], and its last in [121.3,122.2]. Its last return is before
128.290787, earlier than 139.9. B returns earlier still. Protected auxiliary
phases finish before these main returns, so the claimed terminal quiescence follows.

Events in distinct cells either act independently or send a positively delayed
pulse. The only unresolved local order relevant here, raw end versus ERROR start
on a silent input, is handled by the overlap envelope. A->B is closed during this
phase; no global reciprocal-network commutation theorem is being assumed.

## 6. Energy and caps

Initial q and m are positive and below their thresholds. First-crossing semantics
keep them below 1 in READY and protected flows decrease their charges. Caps and
nonnegative actuation keep all gains below C and b below 1.1.

Use the inherited uniform bound, with upper box endpoints,

`W <= (3*C_max+3*M_max+1)*a + 1.1 + 4.5*Lm_max + 2.4*Le_max < 500`.

The auxiliary protected-drain terms are bounded by the included Lm contribution
at the stated nominal rate ratios. The certificate checks the resulting upper
bound (below 264.349 even at epsilon=0.1). At E=50 the pump supplies 500, and at
E=100 its derivative is nonpositive. Thus [50,100] is invariant, the E>0 gate
never closes, and the full-dose argument is valid.

## 7. Retained probes

The probes are independent standardized-rest copies, not resets of the live cells.
Before learning, the j=0 silent-flow bound and the larger gap 20 imply no response
to any of the eight pulses, with plasticity disabled. After learning, Section 4
applies with gap 20: one response per pulse, return before the next one, no extra
responses. The copies keep their own physical parameters and learned b/g.

## Computational evidence and trust boundary

`certify/reciprocal_learning/certify.py` evaluates 31 sufficient strict inequalities
using the unchanged A22 outward Decimal interval module at 128-digit precision.
All real initial-state and parameter choices are enclosed; no sampling is used.
Certificate endpoints are published rounded outwards to 40 decimal places.

`verify.py` restates the inequalities without importing the certifier and
reconstructs 103 enclosures with independent 70-place integer fixed-point
arithmetic. exp and ln use explicit Taylor/atanh remainder bounds. Every replayed
enclosure must fit inside the published interval, and every strict inequality is
checked. Metadata changes, omitted obligations, modified sources and -O execution
are refused. The sufficient-inequality formulas are shared mathematically; this
is arithmetic diversity, not an independently formalized proof of all semantics.

The theorem is a written hybrid-flow induction plus checked finite interval
obligations, under authentic-source execution and arithmetic/runtime assumptions.
It is not a complete Lean proof. It does not certify reachability of the prepared
section, the earlier training history, the fully open reciprocal phase, adaptive
pedagogy, arbitrary fabrication faults or real hardware.
