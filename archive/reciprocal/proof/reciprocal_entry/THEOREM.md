# Birth-to-section theorem and composed feedback learning

## 1. Statement

Take epsilon=0.003 or epsilon=0.1. In A and B, all five original physical
parameters of each of three ports are independently chosen in the fixed relative
box around their original nominal values: 30 real physical parameters. Other
kernel constants, thresholds and physical phase endpoints remain unchanged.

This theorem concerns the prototype's **pulses-only** configuration (`impulsions`).
A starts at time 0. B is introduced at time 160 with its stipulated birth state,
as in the original prototype. At each cell's birth:

- Main and all auxiliaries are READY, with no active incoming or outgoing currents.
- q is in [0.09999,0.10001]; each m is in [0.02499,0.02501].
- The three log-gains are independently within 1e-5 of ln(0.3), ln(1.2), ln(0.3).
- b is in [0.07999,0.08001]; E is in [50,100].

There is no reset after birth and no settings copy anywhere in this prefix.
These are a small READY-state enlargement of the prototype's nominal initial
states, not the larger initial-mode family of every historical A22 theorem.

The source and contact schedule is:

| Interval | Inputs and contacts |
|---|---|
| 0–160 | A port 0 receives sources 0,8,...,120. B is not yet introduced. |
| 160–320 | A port 0 receives sources 160,168,...,280. A emissions reach B port 1 through the firing gate [160,310). B->A is closed. |
| 320–459.9 | B port 2 receives sources 320,328,...,440. B emissions reach A port 2 through the firing gate [320,470). A->B is closed. |

Each routed pulse has the unchanged canonical shape, with its own delay in
[0.3,0.4]. The original constant delay 0.35 is included. C is not introduced until
480 and has no role in this prefix.

**Entry conclusion.** At 319.9, both A and B satisfy the complete prepared section
of the previously certified local feedback theorem: READY modes, no active
currents, q exactly 0.1, auxiliaries within 1e-5 of rest, port-2 log-gain unchanged
within 1e-5 of ln(0.3), b in [0.17999,0.18001], and E in [50,100].

**Composed conclusion.** From the stated birth family, for every real point of
the physical and initial-state boxes, the subsequent B->A phase gives exactly
three full ERROR doses to A's feedback gain:

`g_A,2(459.9) = g_A,2(birth) * exp(1.8)`.

The prior 0/8-to-8/8 retained-probe conclusion therefore holds without assuming
section entry. The gain interval is [1.8148760904722349957656331678657619638566,
1.8149123883570220784068819983289122355248]. Total emissions through 459.9 are
38 from A and 27 from B. This is not a theorem about the settings-copy variant,
the fully open later reciprocal phase, adaptive pedagogy or real hardware.

## 2. Shared local bounds, without assuming high initial recovery

The original READY flows and exact endpoint identities are used, not a numerical
ODE trajectory. With a=ln4, kappa=1/2, and h as defined in the earlier theorem,

`q_g(t)=r+(q(0)-r)*exp(-kappa*t)+g*h(t)`.

The main input section is q-r in [-1e-5,0.03]. The auxiliary first crossing is
uniformly in (0.015,0.03); MARK end, ERROR start and ERROR end are obtained by
adding the exact exponential section durations.

The prior written flow argument applies to a generic weak gain g. If J is an
upper bound on its one-cycle gain increment and e_- is the earliest ERROR start,
then a hypothetical READY first crossing is ruled out by

`q(t) <= q_g(1) + J*a*exp(-a*e_-)*max(0,1-e_-) < 1`, for 0<=t<=1.

After raw-current end, the main charge cannot cross upwards without drive. The
certificate checks the derivative sign needed to bound q_g by q_g(1), including
the gain-current overlap possible at epsilon=0.1. It also checks return to the
charge section before a next input gap of at least 7.5.

For A, the three weak gains are initial g0 multiplied by exp(0), exp(0.6), and
exp(1.2). For B's port 1, initial gain 1.2*exp(eta) is weak for one input. At the
largest checked box, B's first-input peak is below 0.788495 and the charge excess
at its next arrival is below 0.026696, safely inside the section.

The entire ERROR is received while READY. It adds exactly

`D=8*(0.1-0.025)=0.6`.

No cap is reached: even the resulting B port-1 gain, about 2.18654, is below the
smallest cap 3.6 at epsilon=0.1. MARK occurs while the main cell is READY, so these
weak inputs do not change b. Consequently A needs exactly three weak inputs and
B exactly one before a strong-input regime is available.

These silent-input arguments do not depend on a high value of b: the main cell
never leaves READY during those inputs. Thus no entry assumption is used to prove
its own bootstrap.

## 3. First strong input at low recovery

For either resulting strong gain, the certificate proves a first upward main
crossing with latency f in (0.3,0.9). It checks strict increase of the READY flow,
its value below 1 at 0.3 and above 1 at 0.9. For A's strong gain it also proves
latency greater than 0.5, used in the downstream arrival hulls.

MARK finishes before 0.3 and ERROR starts after 0.9. MARK therefore precedes the
main firing. The first ERROR is fully protected: before another input arrives,
b is still b0 and the earliest possible main return is

`0.3 + 1 + ln(2.5)/b0_max`,

well after the first auxiliary cycle. This establishes that the first strong
input emits exactly once while retaining both the strong gain and low recovery.

## 4. Exactly one protected MARK raises b by 0.1

Consider the input immediately after that first strong firing. Measure time from
the previous input. Its gap G lies in [7.5,8.5]. FAST ended at f+1, so the main
cell has accumulated a SLOW integral b0*(G-1-f) before the next input.

SLOW reopens exactly when the integral of b reaches

`L=ln((1/4)/(1/10))=ln(2.5)`.

Let b0 in [0.07999,0.08001], b1=b0+0.1, M_+ the latest MARK end after the new
input, and U_+ the latest ERROR end. Even before knowing whether the full MARK
is protected, monotonicity and its endpoint dose imply b(t)<=b1_max: no other
auxiliary receives an input and one MARK can add at most 0.1.

An upper bound on the integral through the whole new ERROR is

`b0_max*(G_max-1-f_min) + b1_max*U_+`.

At epsilon=0.1 the certified upper bound is 0.827485966667, strictly below
L>0.916290731874. The analogous bound before the input is also below L.
Therefore the main cell is still SLOW at arrival and remains protected through
both MARK and ERROR. This is an a priori upper-bound argument; it does not assume
that the MARK gate stays open in order to establish it.

The complete MARK now receives its protection and positive-reserve gates, and
its cap cannot bind. By the physical endpoint identity,

`Delta b = (1/2)*integral(Lm*m dt) = (1/2)*(1-0.8)=0.1`.

ERROR is entirely protected and contributes no gain dose. This input emits no
new pulse. By the actual MARK end, b is exactly b1.

A lower bound on the SLOW integral three time units after the protected input,
if it had not yet reopened, is

`b0_min*(G_min-1-f_max) + b1_min*(3-M_+)`.

The certificate gives a lower bound above 0.978514522222, strictly exceeding
L<0.916290731875. Thus reopening occurs before three time units, after the whole
protected auxiliary cycle and before the following input. The raw current is
already off; q returns exactly to r and remains there in the ensuing silence.

## 5. Stable high-recovery regime

After that single protected input, each later input starts READY. Its whole
MARK ends before the first main firing, and its ERROR is protected throughout
FAST/SLOW. For the two strong gains the certificate verifies:

- main firing latency in (0.3,0.9);
- ERROR ends before the earliest protected return;
- latest main return is below `0.9+1+ln(2.5)/b1_min < 6.990787 < 7.5`.

So gain and b remain unchanged, each input emits once, and the main cell is READY
again before the next input. There can be no second firing for a single input:
FAST lasts one unit after its firing, beyond raw end 1, and reopening occurs
with no drive remaining. Thus no other protected MARK can increase b later.

Each cell receives exactly one full protected MARK in its whole warm-up. In
particular b at entry is its birth value plus 0.1, not a value inferred from a
nominal simulation or externally copied from another cell.

## 6. Protocol induction to time 319.9

### A learns its own source, 0–160

The sixteen inputs on port 0 have gap 8. The first three are silent and acquire
3D. The fourth emits. The fifth is protected, raises b by 0.1 and emits nothing.
Inputs six through sixteen emit once. Hence A emits 12 times, has gained exactly
1.8 in its port-0 log-gain, and has reached b0_A+0.1.

Its last main return is before 126.990787, earlier than 159.9. Auxiliary cycles
and outgoing currents have ended before that return. No other port has received
input. Silence keeps the resting main charge exact and the unused auxiliaries
within their original small rest intervals.

### A teaches B, 160–320

A's next sixteen port-0 inputs start at 160, retaining the same cell and settings.
Section 5 applies to all sixteen, so A emits exactly once per input with latency
in (0.5,0.9). All emissions lie inside [160,310); the last is before 280.9.

Adding the allowed wire delay gives B arrival hulls

`160+8*j+[0.8,1.3]`, j=0,...,15.

Consecutive arrivals therefore have gaps in [7.5,8.5], which is precisely the
range used in the warm-up proof. The earliest arrival is after 160.8, strictly
after B's birth. Birth and A's simultaneous source start at 160 involve different
cells; no numerical event priority is needed. There is no settings-copy action.

B starts with weak port-1 gain 1.2*exp(eta). Its first input is silent and acquires
one dose D. The second emits. The third is protected and adds exactly 0.1 to b.
The remaining thirteen emit once, for 14 B emissions in this block.

The last B input is no later than 281.3, its last emission is before 282.2, and
its last main return is before 288.290787. All these precede the reverse gate at
320 and the prepared cut at 319.9. B cannot feed back during this teaching block.
A itself returns from its last own input before 286.990787. Hence both are
quiescent well before the cut, without resetting or replacing either cell.

Port 2 in each cell has received no current and no copied value. Its auxiliary
remains READY, its charge relaxes within 1e-5 of rest, and its log-gain remains
within 1e-5 of ln(0.3). Other gains stay below their own caps. The exact b1 interval
and resting main charge satisfy the old section inclusions, including equality
at b's endpoints. Reserve stays in [50,100] by the shared W<500 invariant bound.

## 7. Composition with the existing local theorem

Silence from 319.9 to 320 preserves the prepared section. From 320 onward, the
source and routes are exactly those of the previous local theorem: sixteen
B port-2 inputs spaced by 8, B->A on port 2, positive bounded delays, A->B closed,
no copies and no other input through 459.9. Thus the local theorem applies to
every endpoint reached by the whole birth family, not just to the nominal one.

Its B13/A10 emissions add to the established prefix counts: A12+A16+A10=38 and
B14+B13=27. It yields the exact three-dose feedback-gain identity and the isolated
0/8-to-8/8 probes. This closes the previously conditional section-entry assumption
for the pulses-only protocol.

The dependency certificates and their complete code identities are pinned by
SHA-256 and independently reverified during both certification and replay.
Substitution of a different parameter box, section, protocol, source or checker
is refused. The earlier local theorem is not edited to make the composition fit.

## 8. Computational status and limits

For each box, there are 59 new obligations: 55 strict inequalities and four closed
section inclusions. A separate integer implementation reconstructs 170 interval
enclosures. It also rechecks the pinned local theorem's 31 strict obligations
and 103 enclosures. Arithmetic uses the unchanged outward Decimal core and the
separate integer fixed-point implementation with explicit exp/ln series tails.
Sixteen new tests cover positive composition, metadata tampering, dependency
replacement, changed code and optimized execution refusal.

The result is a written hybrid-flow induction with checked finite interval
obligations under authentic-source/runtime assumptions. It is not a complete Lean
formalization. It certifies the real model, not the floating-point ODE simulator.
It covers the stated READY birth family and pulses-only prefix, not initial
residual ERROR modes, settings-copy ordering at 160, later open recurrence,
learned pedagogy, arbitrary fabrication defects or silicon behavior.
