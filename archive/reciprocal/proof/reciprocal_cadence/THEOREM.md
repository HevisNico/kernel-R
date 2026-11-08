# C's faster cadence reaches A through B

## Statement

Fix epsilon in {0.003, 0.1}. Choose all five original physical parameters
(C, Lm, Ls, Le, M) of each of the three ports of each cell independently in
their nominal relative box [1-epsilon,1+epsilon], fixed in time. This is a
**45-parameter box**, with a separate choice for every device and port.
All other R constants, thresholds, actuation rules and energy laws are unchanged.

Use the READY birth family of the preceding composed theorem for A and B.
C is born at time 480 with the same family: main and auxiliaries READY,
q in [0.09999,0.10001], each m in [0.02499,0.02501], log-gains
ln(0.3,1.2,0.3) plus independent [-1e-5,1e-5], b in [0.07999,0.08001],
E in [50,100], and no active currents. Each wire delay may be chosen
**independently for every pulse** in [0.3,0.4].

The protocol is the original `impulsions` (pulses-only) prototype:

| Interval | Sources and routes |
|---|---|
| Through 459.9 | The pinned birth-to-feedback theorem, including A learning from B. |
| 459.9–480 | Silence. |
| 480–630 | B port 2 receives 480,488,...,600. Each B emission reaches C port 1. A has no input. |
| 640–780 | C port 0 receives 640,644,...,736. Each C emission reaches B port 2; each B emission reaches A port 2. |
| Through 789.9 | No further sources; wait for physical quiescence. |

Route windows are gates on **emission times**, not delivery times. All certified
emissions lie strictly inside their stated gates. No other routes, settings
copies, state resets or teacher removal occur in this prefix.

Then every real trajectory in this family has the following properties:

1. The teaching block gives 16 B emissions and 14 C emissions. At 639.9 all
   cells are quiescent, with `b_before = b_birth + 0.1`. A/B port-2 gains are
   their own birth gains times exp(1.8); C port-0 gain is still its birth gain.
2. The fast block gives exactly **20 C emissions, 18 B emissions and 16 A
   emissions**. The parents' only inputs in this block are their children's
   delayed emissions; A has no direct source from the world or from C.
3. Each cell receives exactly two additional full protected MARK doses.
   Its recovery parameter satisfies the **exact real identity**
   `b_after = b_birth + 0.3 = b_before + 0.2`, hence lies in [0.37999,0.38001].
4. Each active gain ends at its own birth value times exp(2.4), without
   cap contact. The active ports are C port 0 and B/A port 2. This gain lies
   in the common interval published as `gain_after_four_doses`.
5. At 789.9, main and auxiliary modes are READY, currents are off and q is
   exactly 0.1. All cells remain alive and have evolved without state reset.
6. Independent standardized-rest copies, retaining their device parameters
   and learned b/g, with learning disabled and peers disconnected, give:

| Eight inputs at period 4 | A port 2 | B port 2 | C port 0 |
|---|---:|---:|---:|
| Settings at 639.9 | 4/8 | 4/8 | 0/8 |
| Settings at 789.9 | 8/8 | 8/8 | 8/8 |

C's 0/8 baseline is specific to pulses only: its port 0 has not inherited a
gain copy. The full settings-copy recording has a different C baseline.

If C->B is cut throughout the fast block, neither parent receives an input;
their gains and b remain at the pre-fast values. If only B->A is cut, A
receives no input and retains those values. In either case A's retained probe
remains 4/8. This is a causal result about the declared route intervention,
not a claim of general pedagogy or an independently chosen curriculum.

## 1. Preceding theorem and C's teaching block

Before doing new arithmetic, the new checker authenticates the exact published
entry certificate and its six source files, then invokes its integer checker.
That checker in turn authenticates and replays the local A-learns-from-B
certificate. The new result therefore does not replace reachability by a
nominal snapshot at 639.9.

The preceding induction gives A and B q=r=0.1, b=b_birth+0.1, and three full
ERROR gain doses on port 2 at 459.9. In particular the old local proof's
Sections 3–5 give B's three doses as well as A's. Its active auxiliary has
returned to r_m=0.025. Silence preserves this section through 480.

B's new period-8 inputs therefore all fire. Their delayed outputs reach C's
initially weaker port 1. The pulse induction below proves one initial silent
gain dose, one missed protected input supplying a full MARK, and 14 emissions
from the 16 deliveries. C's b becomes b_birth+0.1. All returns precede 639.9.
C port 0 has received nothing; its auxiliary remains within the birth charge
interval, and its gain remains unchanged. C's main charge, however, is exactly
r after its physical final return, rather than being reinitialized to r.

## 2. Auxiliary cycles and energy

Write a=ln(4), k=1/2, r=1/10, r_m=1/40 and

`h(u) = a/(a-k) * (exp(-k*u)-exp(-a*u))`.

For the first input on any active port, its resting auxiliary charge differs
from r_m by at most 1e-5. The checked first-crossing signs and derivative give
a unique threshold latency tau in (0.015,0.03), over both physical boxes.
The exact subsequent endpoints give the interval hulls

`m_end = tau + ln(5/4)/Lm`,
`e_start = m_end + ln(8)/Ls`,
`e_end = e_start + ln(4)/Le`.

For every actual consecutive pair of inputs, the certificate checks
`e_end < next_arrival - arrival`. It also checks `e_end > 1`.
Thus one full auxiliary cycle completes after its raw current ends, reaches
exactly r_m and cannot overlap the next cycle. This is an induction through
every actual delivered pulse, including missed main-cell responses.

The inherited global work bound is checked below 500 using the upper physical
box endpoints. Hence the pump makes [50,100] invariant in each cell; the energy
gate never closes. All attained gains lie below every allowed port cap, and
b remains below 1.1. The full-dose endpoint identities are consequently valid:

`Delta z = 8*(0.1-0.025) = 0.6`,
`Delta b = 0.5*(1-0.8) = 0.1`.

These identities integrate actual phase endpoints and do not cancel two
independently rounded interval variables.

## 3. Pulse induction for the main cell

The program records the case and all sufficient strict inequalities for every
input, starting with B's teaching block and C's birth. There are three cases.
Any ambiguous guard ordering or failed strict inequality is refused.

### READY, no firing

If x=q(0)-r at an input, the frozen-gain READY flow is

`q_g(u)=r+x*exp(-k*u)+g*h(u)`.

The derivative test is the same first-crossing test as in the earlier proof:
with c=k*(x+g*a/(a-k)) positive,

`exp(a*u)*q_g'(u) = g*a^2/(a-k)-c*exp((a-k)*u)`.

Its minimum on [0,1] is checked positive at u=1. For weak inputs the upper
bound on the entire possible ERROR/raw overlap is

`g*(exp(0.6)-1)*a*exp(-a*e_min)*max(0,1-e_min)`.

Adding it to q_g(1) gives a peak strictly below 1. This rules out a first
firing without assuming in advance that the main gate stays READY. After
raw-current end, q relaxes towards r and cannot fire. One full ERROR dose is
therefore gained. Its endpoint excess is enclosed and analytically decayed
to the next actual input. The C period-4 weak-input charge carry is included;
the older period-8 input section is not incorrectly reused.

### READY, one firing

An outward dyadic latency bracket [l,u] is found for q_g=1. The verifier does
not trust the root search: it independently checks q_g(l)<1<q_g(u), the
positive derivative on the whole raw-pulse interval, MARK end before l,
and u before ERROR start. Thus gain and b are fixed up to the actual firing.

FAST has exactly duration 1. The SLOW integral to q=r is L=ln(5/2), so with
constant b the physical return is `firing + 1 + L/b`. The whole ERROR is
checked protected before this return. No gain or MARK dose occurs in this
case; raw current has ended before return, and q is exactly r afterwards.
There cannot be an additional firing without another input.

### Input during SLOW

The strict input inequalities put the entire arrival hull after FAST and
before the former return. Let D be elapsed SLOW time from the previous FAST
end to this input and b_pre the recovery value at input. The checker also
requires the preceding input on that cell to be a strong firing, so no earlier
protected MARK has changed b within this SLOW phase. Integrate the actual
exponential MARK, rather than replacing it by an instantaneous jump. For u
after MARK end, the SLOW decay integral since that input is

`(b_pre+0.1)*u - J`,

`J = 0.1*tau + (0.1-0.4*ln(5/4))/Lm`.

Consequently the relative return time is enclosed by

`u_return = (L - b_pre*D + J)/(b_pre+0.1)`.

The checker proves u_return strictly after MARK end. The increasing decay
integral then justifies that this formula is the actual first SLOW return,
and the full 0.1 MARK dose has occurred. For every such pulse it proves one
of two separated cases: ERROR ends before return, giving no gain dose; or
return precedes ERROR start, giving a full 0.6 gain dose. No partial-ERROR
event ordering is silently discarded.

If return precedes raw-current end, q is r at return but can be charged by
the remaining input. For a lower return bound v<1, the remaining frozen-gain
charge at time 1 is at most

`g*a/(a-k) * (exp(-k)*exp(-(a-k)*v)-exp(-a))`.

The same bounded ERROR/raw overlap is added when relevant. The resulting
frozen-gain tail increases up to raw end: h is increasing on [0,1], as follows
from the already checked rest-flow derivative (for example B's first teaching
input). Thus this endpoint value plus the uniform overlap bound encloses the
charge at every earlier raw-tail time as well. The resulting excess is checked
too small to cause another firing and then decays to the
next input. If return is after raw end, excess is exactly zero. Thus no live
state is reset and no raw tail is lost at a protected-to-READY transition.

## 4. Time dependencies and route composition

Dates are affine sums of exact source times, root-latency symbols and wire
delay symbols. Each wire pulse gets a fresh [0.3,0.4] symbol. A cell firing
from **exactly q=r with the same fixed gain on the same port** has exactly
the same latency at every such input, even if b has changed: b acts only
after firing. That same latency symbol may therefore cancel in a difference
of two dates. Non-rest firings use distinct symbols. All remaining dependency
is over-enclosed; no equality between independent devices or wire delays is
assumed. The integer checker reconstructs these affine dates independently.

During the fast block the route graph is acyclic, C->B->A. Induct over C's
25 source pulses. An actual C firing creates one delayed B input, and an
actual B firing creates one delayed A input. The separation and main-mode
tests validate every generated input in chronological order for each cell.
Positive delays and disjoint active routes remove any need for an assumed
simultaneous-event priority between cells.

The per-input trace proves one MARK-only missed input and one MARK-plus-ERROR
missed input in each cell's fast block. C also has three initial weak inputs
on its previously unused port 0. It follows that each cell gains two full
MARK doses, while A/B gain one extra ERROR dose and C gains four. Counts are
20,18,16 for C,B,A. The last emissions precede 780 and all physical returns
precede 789.9. The teaching and prefix counts give totals through 789.9 of
A=54, B=61, C=34.

## 5. Retained competence and cuts

Probes use independent copies at standard rest, not interventions on the live
network. Both learning actuators are disabled. Before the fast block, A/B
have g=0.3*exp(eta+1.8), b=b_birth+0.1. Their firing latency lies in (0.65,0.66).
The checked return is after time 5 and before time 8: the second input at
4 is entirely protected, including its raw support ending at 5; the third
at 8 sees exact rest. Induction gives [1,0,1,0,1,0,1,0]. C port 0 still has
gain 0.3*exp(eta). A geometric-series carry bound for even an infinite
period-4 train proves its peak below threshold, so its eight responses are zero.

After learning, each active gain is 0.3*exp(eta+2.4), b=b_birth+0.3. The firing
latency is in (0.24,0.25) and return is before time 4. Every next input
therefore sees exact rest, giving eight responses. There is no peer pulse
or ongoing adaptation during these probes.

For a cut C->B, B has no source after 600 and no remaining incoming route in
the fast interval. It remains at rest and emits nothing. A therefore also
receives nothing. For a cut B->A alone, A directly receives nothing. With no
input and all auxiliaries READY, z and b are constant by the R equations.
The already checked pre-fast probe consequently remains 4/8 for A. This
proves necessity of both links for this protocol, without a sampled ablation
being substituted for an all-parameter argument.

## Computational and scientific boundary

The Decimal producer uses the unchanged outward interval core. The checker
uses the unchanged integer fixed-point core with explicit exp/ln series-tail
bounds and imports no Decimal producer. It authenticates the pinned prefix,
checks the statement, source identities, pulse cases, root signs, all published
enclosures and all sufficient inequalities. Root brackets are witnesses, not
trusted floating-point roots. The separate code restates the same analytic
recipe; arithmetic diversity does not establish independent mathematical review.

This is a computer-assisted written hybrid-flow proof with arithmetic replay,
not full Lean formalization. It covers the pulses-only prefix through 789.9,
the stated fixed physical boxes and jitter. It does not cover settings-copy
ordering, the open reciprocal phase starting at 800, arbitrary schedules,
learning a teaching method, semantic knowledge, fabrication processes beyond
this parameter model, or chip energy/area benefits.
