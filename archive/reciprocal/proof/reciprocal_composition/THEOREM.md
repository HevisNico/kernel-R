# Compositional cadence learning on every finite chain

## What changes from the three-cell proof

The earlier theorem enumerates a particular three-cell prefix. Here a finite
set of **N-independent local inequalities** establishes a signal contract that
closes under another relay. A written induction then covers every finite chain.
Running selected N values is supplementary evidence, not that induction.

Two resources must scale or be budgeted: the source must be long enough, and
wire jitter must have a bounded sum along the path. The physical parameter
boxes themselves do not shrink as N grows. This is a directed-chain theorem,
not a theorem for arbitrary N-node graphs or feedback cycles.

## 1. Global statement

Let N be any finite positive integer. Index cells j=0,...,N-1 from the leaf
to the root, and fix epsilon in {0.003,0.1}. In each cell choose all 15 per-port
physical parameters (C,Lm,Ls,Le,M) independently in the nominal relative box
[1-epsilon,1+epsilon], fixed in time. All other R constants and laws are unchanged.
There is no assumption that devices have equal parameter values.

Each cell is born at time 0 with main and auxiliaries READY, no currents,
q in [0.09999,0.10001], each m in [0.02499,0.02501], log-gains equal to
ln(0.3,1.2,0.3) plus independent [-1e-5,1e-5], b in [0.07999,0.08001], and
E in [50,100]. Cells remain alive throughout.

### Preparation and training protocol

All routes are closed during preparation. Each relay j>=1 receives 16 direct
port-2 pulses at 0,8,...,120. The leaf receives those pulses on port 1 instead.
Wait until 160. Then enable the directed chain j -> j+1 and send K canonical
port-0 inputs to the leaf at 160+4*k, k=0,...,K-1, where

`K >= 4*N+12`.

Every relay receives only its child's emissions on port 2 in this fast phase.
There is no other fast-phase source, settings copy, state reset or teacher
removal. This is a new scalable preparation schedule, not the literal old
0/160/480 birth schedule stretched without modification.

Each wire sends exactly one canonical pulse per emission, without loss,
attenuation or waveform deformation. Its delay on pulse k is d_i+e_i,k, where

`0 <= sigma_i <= 0.05`,

`d_i is fixed in [0.3+sigma_i,0.4-sigma_i]`,

`|e_i,k| <= sigma_i`, and `sum_i sigma_i <= 0.15`.

All per-pulse errors may be adversarial and correlated with history; no
probability or cancellation assumption is used. Each total delay is in [0.3,0.4].

### Conclusions

For every such device choice and wire-error sequence:

1. All cells are prepared by 159.9. Each has b=b_birth+0.1 and q exactly 0.1.
   Each relay's port-2 gain is its own birth gain times exp(1.8). The leaf's
   port-0 gain is still its birth gain. No prepared state is imposed by reset.
2. In the fast phase, cell j emits exactly `K-5-2*j` pulses. In particular
   the root emits `K-2*N-3`.
3. Each cell acquires exactly two complete MARK doses during that phase:
   `b_after = b_before_fast+0.2 = b_birth+0.3`, in [0.37999,0.38001].
   Its active gain ends at its own active birth gain times exp(2.4), below cap.
4. The root's output has a final regular tail of length `K-4*N-4 >= 8`, in
   the packet class defined below. A cell adds no new phase-error amplitude
   to that class; only the wires add their stated budgets.
5. Isolated standardized-rest copies with learned settings, peers disconnected
   and both learning actuators disabled, respond 8/8 to eight period-4 probes.
   Before the fast phase the leaf gives 0/8 and every relay gives 4/8 on its
   active port. These probes do not intervene on live cells.
6. Cut any one chain link during the fast phase. All ancestors above the cut
   receive nothing, keep their prepared gain and b, and retain 4/8 probes.
7. All cells are READY with q=0.1 and no active currents by

   `160 + 4*(K-1) + (11/10)*(N-1) + 8`.

The fast-phase total number of emissions is `N*(K-N-4)`. At the minimum K it
is `3*N*N+8*N`: source length and time are linear in N, but total traffic in
this construction is quadratic. This is not a claim of cheap unlimited scaling.

## 2. The packet class

A packet P(m,L,J) has an **existential ideal-date decomposition**:

- An ideal prefix of m>=1 dates u_0,...,u_(m-1), whose successive gaps lie in
  [7.4,8.3].
- L>=1 following ideal dates `u_(m-1)+d+4*k`, k=0,...,L-1, for one d in [4,4.1].
- Each actual arrival equals its own ideal date plus an arbitrary error in
  [-J,J]. No independence between the ideal decomposition and those errors
  is required. The decomposition is a proof witness, not an implemented clock
  or a retiming operation.

When J<=0.15 all actual gaps are at least 3.7, and slow-prefix gaps are at
least 7.1. Width-1 raw pulses cannot overlap. The certified auxiliary cycle
also finishes before the next input.

The local relay theorem is:

`P(m,L,J) -> P(m+2,L-4,J)`, for `L>=5`, `J<=0.15`.

Its initial section is exact main rest, all auxiliaries READY within the small
rest interval, no currents, E in [50,100], b=b_birth+0.1 and active gain
g=0.3*exp(eta+1.8), |eta|<=1e-5. Other ports receive no input. The first
arrival must follow this section. The relay learns two MARK doses and one
ERROR dose. The leaf uses a separate base lemma on its untrained port.

## 3. Preparation is reachable

The checker first authenticates the published entry theorem's exact certificate
and six source files, then replays its integer verification, including its
authenticated earlier local theorem.

The entry proof's period-8 A block establishes the needed single-cell result
from birth for an active gain 0.3: three weak ERROR doses, 12 emissions from
16 inputs, and exactly one full protected MARK. Port permutation 0<->2 maps
that block to the new relay preparation. Nominal rows and R equations are
identical across ports, the birth gains on ports 0 and 2 match, and the freely
chosen independent parameter rows and gain perturbations are permuted with
their ports. This preserves the entire quantified family, not just a nominal cell.

For the leaf, the old B preparation argument covers active gain 1.2 on port 1:
one weak ERROR dose, 14 emissions and one protected MARK. Its proved input-gap
family [7.5,8.5] includes direct gap 8; its first-root and birth-charge bounds
also include an immediate input at birth. It needs no actual A teacher to
realize this input family. In both cases the last return precedes 159.9,
which is also checked numerically by the new sufficient bound.

Silence preserves q=r after a physical SLOW return. Unused auxiliaries relax
within the small birth interval. Thus the leaf's unused port 0 remains weak,
while its main cell has b=b_birth+0.1. Preparation can happen in parallel in
all N cells because routes are closed and their energy reserves are separate.

## 4. Uniform auxiliary, energy and root bounds

Use a=ln(4), k=1/2, r=1/10, r_m=1/40, and

`h(t)=a/(a-k)*(exp(-k*t)-exp(-a*t))`.

The auxiliary first crossing is in (0.015,0.03), with a strictly positive
derivative. MARK end, ERROR start and cycle finish are enclosed using the
actual rates Lm,Ls,Le. Cycle finish lies after raw end 1 and before the
smallest possible next gap 3.7. Each later auxiliary cycle therefore starts
at exactly r_m. Its endpoint doses, when the main gate admits them, are

`Delta z=8*(0.1-0.025)=0.6`, `Delta b=0.5*(1-0.8)=0.1`.

The inherited work bound is below 500 throughout the physical box, so
[50,100] is invariant under the reserve pump in each cell. These bounds are
local and time-uniform; increasing N or the train length does not close the
energy gate. It does increase aggregate traffic and required supplied power.
All attained gains and b stay strictly below their own caps.

For READY charge excess x=q-r, before a possible first firing,

`q_g(t)=r+x*exp(-k*t)+g*h(t)`.

The usual derivative test proves strict increase through the raw interval.
Both endpoint signs are checked for each bracket. The uniform brackets are:

| Main firing | Latency bracket |
|---|---|
| Relay, g_low=0.3*exp(eta+1.8), exact rest | [0.65,0.66] |
| High gain g_high=0.3*exp(eta+2.4), exact rest | [0.24,0.25] |
| First high-gain firing after a residual raw tail | [0.20,0.25] |
| Leaf's first firing after its three weak inputs | [0.4,0.66] |

Each bracket lies after complete MARK and before ERROR start. The checker
also proves the whole ERROR protected by FAST/SLOW for each required b value,
including the second low-gain firing at b=b_birth+0.2. Raw input is over when
an ordinary firing returns. Thus a later sufficiently separated input starts
from **exactly** q=r, not a rounded or artificially reset section.

A fixed-gain rest latency is identical on repeated inputs to the same physical
port, because b does not act in READY. Fixed fabrication differences change
that cell's latency but do not create fresh per-pulse phase noise. This is
the physical reason the learned regular tail does not amplify its input jitter.

## 5. Relay transformation

Let t0 be the last actual prefix input. Its firing latency is the fixed
low-gain rest latency l0. Earlier prefix inputs are separated by at least
7.1, greater than the low-gain return bound, so each fires once from rest
and changes neither b nor gain. Denote the subsequent short-tail inputs by
t1,t2,t3,t4,t5,... . Their ideal positions relative to the last ideal prefix
date p0 are d,d+4,d+8,d+12,d+16,... . Actual phase errors are retained below.

### t1: one full MARK, no ERROR dose

The gap t1-t0 lies in [4,4.1]+[-2J,2J]. t1 is after FAST but before the old
SLOW return. With L=ln(5/2), and SLOW duration D=t1-(t0+l0+1), integrate
the actual exponential MARK. After MARK end, the additional decay integral is

`(b_pre+0.1)*u - A_M`,

`A_M=0.1*tau+(0.1-0.4*ln(5/4))/Lm`.

Hence the return after t1 is

`u=(L-b_pre*D+A_M)/(b_pre+0.1)`.

For all the admitted gaps and devices the new certificate encloses u in
[1.5129,1.9758], a coarse display of the exact published bounds. It checks
u after complete ERROR and before t2. The formula is justified by the
strict guard ordering and increasing SLOW integral. One full MARK raises
b to b_birth+0.2; no gain dose occurs. Since raw current has ended before
return, t2 sees exact rest.

### t2: low-gain firing

t2 emits at t2+l0. MARK completes while READY, and ERROR remains protected
throughout its cycle at the new b. Thus gain and b remain unchanged. Since
the previous input is a strong firing, b is constant from its FAST end
until t3 begins its MARK; no earlier protected dose is omitted from D.

### t3: the second full MARK and a full ERROR

Its gap from t2 is in 4+[-2J,2J]. The same exact integration gives a return
after MARK end but before ERROR starts, enclosed by [0.4648,0.9190]. This
supplies a second 0.1 MARK, bringing b to b_birth+0.3, then a complete 0.6
ERROR gain dose while READY.

The raw pulse can still be active when the cell returns. Its remaining
frozen-gain contribution at raw end is bounded by

`g_low*a/(a-k)*(exp(-k)*exp(-(a-k)*u_min)-exp(-a))`.

The possible ERROR/raw overlap adds at most

`(g_high-g_low)*a*exp(-a*e_min)*max(0,1-e_min)`.

h increases on [0,1], so this end value plus the uniform overlap bound
covers every earlier raw-tail time too. The resulting peak is below threshold:
no hidden tail refiring interrupts the full ERROR. By the earliest t4, the
charge excess is in [0,0.11210], using the precise published enclosure.

### t4 and the entire remaining tail

t4 fires with high gain and excess at least zero; its latency l1 lies in
[0.20,0.25]. The same device's exact-rest high-gain latency l2 lies in
[0.24,0.25]. Scalar READY-flow comparison, with the **same actual gain** in
both flows, proves l1<=l2. This ordering is an analytic comparison, not an
invalid comparison of two independent root-interval endpoints.

The latest return from either high-gain bracket is below 3.7. Every next
short-tail gap is at least 3.7. Thus t5 and all subsequent inputs start at
exact rest, fire with exactly l2, preserve gain and b, and do not add phase
noise. The energy argument is time-uniform, so this induction covers every
finite remaining train length.

### Closing the output packet

Retain each emitted input's actual phase error. Its first m output ideal
dates are the old ideal prefix dates plus l0. Append the ideal dates

`p0+d+4+l0` and `p0+d+12+l1`.

Their new ideal gaps are d+4 in [8,8.1] and 8+l1-l0 in [7.54,7.60], both
inside [7.4,8.3]. The remaining output starts with ideal date p0+d+16+l2,
whose settling gap from that new last prefix is

`d' = 4+l2-l1`, in [4,4.05], hence in [4,4.1].

The remaining ideal dates are period 4. Each corresponding actual date retains
its own input error in [-J,J]. l1 may depend on the realized input errors;
that is permitted by the existential packet definition. No retiming operation
is performed. Exactly t1 and t3 fail to emit, proving

`P(m,L,J) -> P(m+2,L-4,J)` with m+L-2 emissions.

## 6. The leaf base case

After preparation, the leaf's active port 0 still has birth gain near 0.3,
but b=b_birth+0.1 and q=r. Its first three period-4 inputs do not fire.
For each, the checked frozen flow plus the complete possible gain/current
overlap stays below threshold. Between them the actual charge carry is
bounded by its raw-end excess times exp(-3*k). Each supplies one full
ERROR dose, with no MARK recovery dose. This is not a period-8 approximation.

The fourth input at local time 12 fires with latency l_init in [0.4,0.66].
The next input at 16 is a full MARK-only miss. The next at 20 fires from
rest with l0. The next at 24 is the MARK-plus-ERROR miss. The one at 28
fires with l1, and those from 32 onwards fire from rest with l2. The same
relay inequalities cover these latter cases at a larger allowed jitter.

The three initial output ideal dates are 12+l_init,20+l0,28+l1. The first
gap is inside [7.99,8.26] and the second inside [7.54,7.60]. The next gap
is 4+l2-l1 in [4,4.05]. These are exact actual dates, with no source jitter.
Therefore any K>=9 exact source pulses generate

`P(3,K-8,0)`, with K-5 emissions.

## 7. Wire rule and induction over arbitrary N

A wire adds the same fixed d_i to all ideal dates and adds e_i,k to each
actual phase error. The triangle inequality gives

`P(m,L,J) -> P(m,L,J+sigma_i)`.

It changes neither prefix nor tail length. Combining this rule with the local
relay rule, induction from the leaf gives at cell j:

`m_j=3+2*j`, `L_j=K-8-4*j`, `J_j=sum_(i<j) sigma_i`.

Write K=4N+12+R with integer R>=0. Then

`L_j=8+4*(N-1-j)+R`.

At each relay step before the root, this tail has at least 12 inputs, more
than the five required by the local rule. The root tail has 8+R. All
J_j<=0.15 by the path budget; there is no unproved accumulation cancellation.
Each step therefore satisfies every assumption of the next step. This is a
mathematical induction for **every finite N**, not a loop checked only up to
a selected maximum N. Twelve polynomial identities in the certificate check
the exact length, count and traffic algebra.

The same induction allows nonuniform sigma_i with sum at most 0.15. The CLI
provides a uniform-budget specialization without enumerating cells:

`sigma = min(0.05, 0.15/(N-1))` for N>=2, and 0 for N=1.

Fixed per-link delays (sigma_i=0) allow arbitrary N while each fixed d_i
remains free in [0.3,0.4]. The original full per-pulse jitter ±0.05 on every
link satisfies this sufficient budget through N=4. At larger N that unchanged
per-link allowance is outside this theorem. This is a guarantee limit of the
chosen contract, not a proof that a deeper physical network cannot learn.

## 8. Retained response, cuts and terminal time

Before the fast phase, a relay's low-gain frozen probe has a return after
time 5 and before time 8. The input at 4 is wholly protected, including raw
end at 5. Thus alternate pulses fire, yielding 4/8. The leaf's unused port
has an infinite period-4 geometric-series peak below threshold, yielding 0/8.
After learning, high-gain return is before time 4, giving 8/8 in every cell.
These probe inequalities are checked independently of live intercell traffic.

A cut leaves every upstream ancestor without a fast-phase source. It starts
at rest with auxiliaries READY. With no incoming pulse, R emits nothing and
changes neither gain nor b; induction along that remaining ancestor segment
establishes the causal cut conclusion. No ablation sample is used instead
of this all-device argument.

Each emitted pulse occurs within 0.66 of an admitted input; each wire delay
is at most 0.4. A conservative hop allowance is 1.1. After the last input,
the final main return and all auxiliaries finish within a conservative 8.
The stated global quiescence bound follows by induction on the remaining
N-1 links. No route cycle exists to generate an unbounded echo.

## 9. Verification and trust boundary

The N-independent certificate has 81 strict local inequalities and 176
enclosures for each physical box, plus 12 exact polynomial identities. The
producer uses outward Decimal intervals; the separate checker restates those
bounds using integer fixed-point intervals with exp/ln tail bounds. It imports
no Decimal producer. Both authenticate the previous preparation theorem.

The polynomial normalizer is a small shared exact-integer component. It
checks algebraic identities, not the hybrid-flow semantics or the induction
rule itself. The latter are the written proof above. The existing nominal
and sampled-chain numerical checks are supplementary and are not proof of
universal N or parameter robustness.

This is a computer-assisted written proof, not a full Lean formalization or
independent mathematical peer review. It assumes an exact source cadence,
canonical channel pulses, the stated jitter budget, fixed device parameters,
and the supplied preparation schedule. It does not cover arbitrary graphs,
cycles, time-varying fabrication parameters, repeated lessons after saturation,
general learned pedagogy, or chip energy/area benefits.
