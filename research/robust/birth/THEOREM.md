# Robust birth entry and continuation into a finite chain

## Statement and protocol

Use any of the eight previously certified (epsilon,nu,alpha) points. Every cell
starts at time zero in the READY birth family: q=.1+/-1e-5; each m=.025+/-1e-5;
log gains ln(.3,1.2,.3)+independent +/-1e-5; b=.08+/-1e-5; E in [50,100]; no currents.
This is the stipulated untrained birth state, not literal zero charge/gain and
not a family with residual ERROR modes. Per-port C,Lm,Ls,Le,M may drift measurably
inside the relative boxes. Charge disturbances and amplitude multipliers are
bounded as in the robust local theorem and may be independently adversarial.

Keep all intercell routes closed. Give **each cell sixteen port-0 pulses** at
0,8,...,120; wait until 160. This parallel external preparation is not the old
A-teaches-B calendar of reciprocal_entry. It uses no state reset, settings copy
or measured-state-dependent input adjustment. Port 2 receives no preparation.

At 159.9 every cell is READY, all auxiliaries READY, all currents off, and:

- q is in r+[-rho,rho] and each m in r_m+[-rho,rho], rho=delta+nu/kappa;
- its port-2 log gain is exactly its birth value;
- b is in b_birth + [.1-.5*nu*T_M, .1+.5*nu*T_M], where T_M is the maximum
  full MARK duration; b never reaches its cap;
- E remains in [50,100]; the warm-up emits exactly 12 pulses per cell;
- port 0 has received three full ERROR doses and exactly one full protected MARK.

These widened bands, not the old delta-wide section, are the entry target under
noise. In particular silence cannot remove a persistent charge disturbance.

At 160 open the feed-forward chain on port 2, with no further port-0 inputs.
With K>=3N+1 and T>=7.5+.5(N-1), the general robust-chain conclusions hold from
birth: K-3N root emissions, exactly three new port-2 ERROR doses per cell, unchanged
post-preparation b, and frozen port-2 probes 0/8 to 8/8. When nu=alpha=0, the
stronger packet proof applies: T>=7.5 for fixed wires, or T>=7.5+2 sum sigma_i.
For K=3N+8 the root emits eight pulses. The first source date is now 160, so add
160 to the previously stated chain time bounds. Warm-up outputs are not routed.

## 1. Noise-aware actuation and target section

A full phase with m'=-L(t)m+w and actuator c L(t)m has total actuation
c(m_start-m_end+integral w). Thus ERROR doses remain in the local interval
.6+[-8 nu T_E,8 nu T_E]. A complete protected MARK now gives

    D_b = .1 + .5 integral w_m,
    |D_b-.1| <= .5 nu T_M.

The standard drifting-decay comparison gives T_M. Its upper value is

    ln((1-nu/Lm_min)/(.8-nu/Lm_min))/Lm_min.

Write b0=[.07999,.08001] and b1=b0+the MARK dose interval. local_bounds.py is the
previous local enclosure derivation with **b1 substituted for the old b band**.
All its 36 inequalities are re-evaluated, rather than applying an old certificate
to a larger section. The main input excess bounds and auxiliary rest-deviation
bounds already allow delta+nu/kappa; their validity is explained below.

## 2. Three silent inputs and the first firing

The silent-input bounds use the READY equation and do not depend on b. Thus
inputs 0,8,16 are silent and provide three full port-0 ERROR doses, without MARK
actuation. No gain cap or reserve gate intervenes. On input 24, the learned
port-0 gain produces one firing with latency f in (.5,.9]. The auxiliary MARK
ends before f and its ERROR is entirely within FAST by the local ordering bound.
This first firing leaves b at b0 and gives no extra gain dose. Its FAST duration
is in the rechecked interval [T_F-,T_F+], independent of b.

## 3. The fifth input is protected through its entire auxiliary cycle

Consider input 32, eight units after the first emitting input. It is strictly
after FAST. Before it, SLOW has b=b0 and q starts from .25 at the FAST guard.
For the scalar comparison solution define

    Phi(x,b,w,t) = x exp(-bt) + (w/b)(1-exp(-bt)).

Let U+ be the maximum complete auxiliary cycle after the new input. Even before
proving that MARK is fully protected, its actuation can be at most the full
positive MARK integral: D_b<=.1+.5 nu T_M. Therefore b<=b1_max throughout it.
The fastest possible main decay is bounded below, through the entire cycle, by

    q_arrival_lower = Phi(.25,b0_max,-nu,8-.5-T_F-),
    q_cycle_lower = Phi(q_arrival_lower,b1_max,-nu,U+).

The certificate proves q_cycle_lower>r. Also nu<b0_min*r, so all these comparison
flows decrease while above r. This proves the cell remains SLOW at arrival and
through the entire MARK and ERROR; it is not a circular assumption about the
MARK gate. The complete MARK therefore adds a dose in the b1 band. ERROR adds
no gain dose and the fifth input emits no pulse.

At epsilon=.1,nu=.002,alpha=0, the lower bound is above .10505; r=.1.

## 4. Reopening and stable warm-up continuation

Let M+ be the latest MARK end, measured from input 32. Before that date b>=b0_min;
after it b>=b1_min. The slowest possible main decay is bounded above by

    q_mark_upper = Phi(.25,b0_min,+nu,8-.9-T_F+ + M+),
    q_deadline_upper = Phi(q_mark_upper,b1_min,+nu,3.5-M+).

The certificate proves q_deadline_upper<r. If SLOW had persisted until this
deadline the comparison would contradict q>r, so reopening occurs before 35.5.
Section 3 puts this return after the whole protected auxiliary cycle and raw
support, and 3.5<8 puts it before input 40. Reopening assigns exactly q=r by the
physical guard; no artificial reset is applied.

Every later warm-up input starts in the local section with b in b1. The rechecked
local firing/recovery bounds give one response per input, no more MARK actuation
and no more gain actuation. The input pattern is therefore

    silent, silent, silent, fire, protected, fire,...,fire,

with 12 emissions, three full ERRORs and one full protected MARK over 16 inputs.
The last return is before 120+R, with R the rechecked local main_reopen_bound,
strictly before 159.9. The auxiliary/outgoing supports finish earlier.

## 5. Section inclusion under persistent noise

After a main guard return, absence of drive gives |q-r|<=nu/kappa. From birth or
a prior auxiliary return, the same comparison bounds unused/ready auxiliaries by
|m-r_m|<=delta+nu/kappa. This band is invariant under further silence: its radius
is at least nu/kappa, so the solution is a convex combination of its initial
excess and the bounded forcing integral. One must **not add nu/kappa again** at
every waiting period. Its upper endpoint is below threshold, so untouched port-2
auxiliaries never enter a protected phase and their gains remain unchanged.

The widened q band is inside the local input section [-rho,Q], Q=.03. The local
proof already uses -rho for its lower forcing envelope and Q for its silent-input
upper envelope. It uses rho for auxiliary initial deviation. Hence these bounds
apply to the widened section without enlarging rho a second time. b belongs to
the rechecked b1 interval, and the same W<500 reserve comparison holds throughout
birth preparation and continuation. The unused port-1 birth gain remains below
all possible caps. All local section requirements are thus discharged.

## 6. N cells and constant-period special case

Warm-ups are independent because all routes are closed, so the same enclosure
holds for every cell in any finite collection at 159.9 and at chain opening 160.
The general chain induction uses only this local contract and minimum input gaps.
Its counting and accumulated latency bounds are unchanged, with the new b1 and
new R. This proves the noisy finite-chain statement from the declared birth family.

When nu=0, D_b=.1 exactly even with parameter drift, so b1 is the original band.
A main guard return gives exact rest, and subsequent silence preserves it. With
alpha=0 as well, the identical-waveform, constant-latency argument applies.
The checked inequality delta<g_initial_min*h(1) guarantees a nonnegative residual
for the first emitting input after the three silent port-2 inputs. Its first-fire
advance is absorbed by prefix removal, as in ../periodic/THEOREM.md. Thus the
constant-period theorem now also starts from birth under the specified warm-up.

## Evidence and limits

Each of the eight points has 48 strict inequalities: the 36 rechecked local
conditions and 12 entry/bridge conditions. Outward Decimal generation is replayed
with independent integer interval arithmetic, using the same formula derivation.
The source/metadata/obligation schemas are exact and source hashes are required.
This is a written continuous comparison and induction proof, not full Lean
semantics. Floating-point end-to-end tests retain every physical state from birth,
include a checkpoint at 159.9, and do not replace universal quantification.

The preparation uses an external 16-pulse drive per cell and closed contacts.
It does not prove entry using only one network source, the original A-teaches-B
calendar, feedback/open recurrence, or the earlier fast period-4 protocol. The
READY birth family excludes initial residual ERROR phases. These distinctions
are part of the theorem, not failures silently excused by the tests.
