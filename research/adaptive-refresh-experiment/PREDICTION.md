# Adaptive refresh v2 — deterministic preregistration

Publish this file alone and open the draft PR before implementing or running
v2. Then freeze implementation, run synthetic checks, execute one comparison
containing three trajectories once, and publish its report unchanged. Never
rerun v1, change its files, tune v2 from a pilot, or hide failed predictions.
A failed/interrupted v2 execution is evidence and must be retained, not retried.

## Frozen basis and question

V1 is PR #112 at `ebaac53a49f2f904b9feb07e071c3b5af18746fa`, including its
published protocol and raw data. Formal ingredients remain #111 at
`ba978af1edaf51572aa0af9d1bfc83e309438d3d`. Neither PR is modified or merged.

Can a supervisor with no supplied absolute leakage ceiling construct valid
finite-horizon ceilings from noisy measurements and an explicit variation
law, and maintain service for less cost than probing every period? What is
the cost relative to v1's known-ceiling supervisor (1247 model units)?

This is deterministic envelope estimation, not learning an unconditional
all-time upper bound. Finite past observations cannot rule out an arbitrary
future jump. There is no statistical confidence claim in v2.

## Exact inherited plant and observation protocol

Keep v1's 1320 scored periods, initial reserve 440, floor S=100, capacity 660,
dose 220, one-period write latency, maximum wait 40, jump at t=661 from loss
10 to 20, and integer arithmetic with signed reserve. The jump time and true
rates remain plant-only data, absent from controller inputs.

A probe costs 1 and a commanded write costs 10. Each paid probe includes both
channels: reserve error ((7*t+1) mod 5)-2 with radius 2, and rate error
((5*t+2) mod 3)-1 with radius 1. The initial probe at t=0 is paid. Deterministic
noise is not a probability distribution. The rate channel remains an assumed
sensor, not a reconstruction from R FIRE bits.

Use exactly the v1 chronology: leakage, optional paid measurement, conservative
alarm detection using raw measured reserve minus 2, then delivery of the dose
commanded at t-1. A command at t never delivers at t. Delivery propagates the
measured lower by min(660, lower+220). No floor clipping, free terminal sample,
or command after t=1320. All completion probes are paid. Score unsafe exposure
before the dose as well as after it. The alarm remains latched until an observed
or dose-propagated lower certifies S. No probe is not a success observation.

D/nominal-loss = 220/10 = 22 periods retains the nominal R refresh calibration.
It is not a certified R state map, noise bound, dose bound or energy model.

## New physical hypothesis: variation, not an absolute ceiling

All three controllers are told B=10 and H=41, and the sensor error bounds.
They are **not** told an absolute leakage ceiling, initial true rate, maximum
true rate, future rate values or the jump instant. In particular, neither 22
nor the old baseline threshold 144 may be a hidden policy constant.

The supplied physical hypothesis is, for every time t and 0<=k<=41:

    lambda(t+k) <= lambda(t) + 10.

It bounds upward excursion within each horizon; decreases are allowed. The
registered jump from 10 to 20 satisfies it. It is an assumed property of the
environment, not inferred from success or estimated by v2. It does not promise
that arbitrary unknown jumps will be detected before they cause damage.

From a current report y with radius 1, set the renewable ceiling

    U_t = y + 1 + B.

Then lambda(t+k) <= U_t for k<=41. The 41 periods cover a maximum wait of 40
plus a subsequent one-period write. Every decision refreshes U_t; anchor memory
does not freeze safety. For two probes d<=40 apart, honest observations imply
U_next <= U_t + B + 2 = U_t + 12. This is the handoff allowance below.

Initial readiness, positive net repair (U_t<220), and sufficient capacity are
checked, not assumed to follow merely from having a sensor. A contract refusal
stops further scheduling and is recorded; it does not invoke a hidden fallback.
This experiment does not establish perpetual repair in an unbounded environment.

## Three controller definitions

All baselines now use the measured U_t as well: remove v1's fixed threshold.
They use only the current measured/dose-propagated reserve lower L.

- **Naive:** preferred spacing is 1 if the raw pre-delivery measured lower is
  below S, otherwise 40. Command a write if L < S+2*U_t; otherwise wait for the
  preferred spacing. A write always schedules the next paid probe in 1 period.
- **Prudent:** probe at every period; command a write iff L < S+2*U_t.
- **Adaptive contract:** uses the construction below, executed in Lean using
  #111's exact `Scheduler.plan`, interval review and repair primitives.

For the adaptive controller, carry the previous decision's certified endpoint:
after a wait d it is L_old-U_old*d; after a write it is
min(660, L_old+220-U_old). At the next probe use the maximum of this carried
lower and the fresh measured/dose-propagated lower. Both are sound under the
active contract; this avoids losing a repair buffer solely through new sensor
noise. At initialization there is no carried bound.

First validate 0<=L<=660, U_t<220, S+2*U_t<=660 and L>=S+U_t.
If invalid, refuse. Otherwise use the largest c in 1..40 satisfying

    U_t*c + S + U_t + 12 <= L.

Call `Scheduler.plan` for exactly this inequality. If no positive wait fits,
command one delayed write. This is proactive repair with an extra handoff
buffer; it is **not** unchanged `ClosedLoop.choose`. Its one-step wait/repair
contracts and ceiling derivation will be stated explicitly, without relabeling
the wrapper as a previously proved end-to-end `OfferFactory` instance.

For memory, use the same radius-1 rate intervals and `Renewal.review` with
granularity 5. Initialize the anchor at the first probe. A separated interval
starts one new anchor epoch. Ordinary expiry/renewal is not an anchor reopening.

At each later adaptive probe, also compare its interval with the previous
ceiling, whose horizon must cover the probe:

- If its lower endpoint exceeds the previous ceiling, this is a **demonstrated
  contract violation**: discard the carried lower, record invalidation and
  refuse. There is no claim of safety retrospectively through a false contract.
- If only its upper endpoint exceeds the previous ceiling, record an
  **ambiguous exceedance** and refresh/reopen the operational lease. It is not
  a proof of physical violation. Do not charge this event to the variation
  bound for anchor reopenings. Count it separately, even if simultaneous with
  an anchor change.
- Otherwise renew normally. A new local ceiling never erases an old violation.

The model's valid physical law continues to support carried bounds in the
ambiguous case. Separating these event types avoids pretending that sensor
noise is measured physical variation.

## Evidence and numerical predictions

Log the same per-period data as v1, plus each measured U_t, carried/effective
lower, active lease endpoint, ambiguous exceedance and demonstrated invalidation.
Report probes, commands/deliveries and their separate costs; pre/post unsafe
periods, undetected unsafe periods and longest interval; anchor reopenings,
ambiguous exceedances, invalidations, refusals, final reserve and the ceiling
before/after the jump. No outcome or failed numerical prediction is discarded.

| ID | Prediction fixed before implementation |
|---|---|
| A1 | Prudent: exactly 1321 probes, 88–94 writes, zero pre/post unsafe and undetected unsafe periods |
| A2 | Adaptive: zero refusals, zero demonstrated invalidations, zero pre/post unsafe and undetected unsafe periods |
| A3 | Adaptive: 200–800 probes, 88–94 writes, total cost <= 80% of this run's prudent cost |
| A4 | Adaptive cost >= 1247 and <= 1.5*1247; learning a renewable envelope may cost more than v1's supplied tight ceiling |
| A5 | Adaptive: exactly one anchor reopening at the first post-jump probe, within 40 periods of t=661; 5*reopenings <= sampled true variation (=10); ambiguous exceedances 0 or 1 |
| A6 | Every adaptive pre-jump ceiling is in [20,22], every post-jump ceiling in [30,32]; every actual loss in an authorized action is <= its issued ceiling |
| A7 | Naive: at least 100 undetected unsafe periods, a longest such interval >=10, and total cost below adaptive cost |
| A8 | Every recorded adaptive decision matches the declared Lean policy; all sensor, chronology, carried-lower, handoff and repair-time inequalities pass the trace audit |

Ranges are analytical expectations, not pilot measurements. Total loss remains
19800 units and dose 220. The comparison with 1247 uses the published v1 result;
v1 is not rerun. V2 changes the information contract and baseline repair rules,
so its difference from v1 is not a pure estimate of sensor cost or a universal
price of learning. No optimality is claimed.

## Publication and execution discipline

Publish this protocol first. Next implement and test on synthetic inputs only.
Publish the exact implementation before one `--run-once` invocation; record
protocol/dependency/code commits, hashes, tool versions and clean source state.
Use an exclusive new `run-v2` directory. Preserve partial evidence and errors
if anything fails; do not retry the registered comparison. Generate and publish
the report unchanged with all A1–A8 verdicts. Rechecking stored traces or proving
local formulas is not another experimental trajectory.

Later R work requires actual waveform-based dose/loss bounds, a justified state
map and sensor correspondence. A transistor-level hidden-jump trial requires
its own calibration and preregistration; none is asserted by v2.
