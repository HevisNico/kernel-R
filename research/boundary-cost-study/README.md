# Exploratory price of a fixed safety boundary

**Decision study, not a preregistered v5 result.** The user explicitly requested
this calculation before deciding whether and how to preregister v5. The known
v3 scenario has now been explored for policy design; a later run of this exact
scenario is a replication, not an unseen confirmatory test. No old experiment
runner is called, no historical evidence is replaced, and no v5 campaign is
started. This study is based on main `767f6ccece9cd2383d582fd884cc73afdf2f47f4`.

## Result and recommendation

On the same 10-to-140 jump, an observation-only fixed-boundary policy maintains
service for **5,671 units with H=150**, versus **5,821** for a safe every-period
baseline: a 150-unit saving (2.58%). It uses 1,171 probes and 450 writes. It
needs no runtime external authorization. These are exploratory discrete counts,
not transistor energy measurements or a new Lean end-to-end theorem.

The most important negative result: adding the optimistic variation-10 law and
its measured refutation to the maximum-safe-wait policy produces **exactly the
same physical actions** as the fixed-H policy, for both tested H values. The
law is correctly rejected once at 661, but adds no scheduling gain on this
scenario. An adaptive-performance claim is therefore not supported here.

The recommendation is to pursue a v5 safety/availability result if that is the
goal, while separating it from a claim that learning improves cost. Developing
a better economic policy inside the fixed guard can be a distinct milestone.
The decision to preregister v5 has not been made by this study.

## Matched scenario and cost

Horizon 0..1320; initial reserve 440; service floor 100; capacity 660; dose 220;
one-period delivery latency; loss 10 before 661 and 140 thereafter. Reserve
error is `(7*t+1)%5-2`, rate error `(5*t+2)%3-1`, with radii 2 and 1. Both sensor
channels are included in each paid probe. Probe price 1, write price 10. Every
comparison pays its initial and terminal probes, completes any terminal dose,
and issues no command at 1320. All simulated policies below end at reserve 440.
The prior hard-bound justification has no assigned acquisition price; runtime
external authorizations are zero. CPU and policy-revision costs are not priced.

| H | Policy | Probes | Writes | Total cost | Unsafe pre/post periods |
|---|---|---:|---:|---:|---:|
| 140 | Safe every-period baseline | 1321 | 450 | 5821 | 0 / 0 |
| 140 | Maximum safe wait | 1207 | 450 | 5707 | 0 / 0 |
| 140 | Optimistic variation law + fixed guard | 1207 | 450 | 5707 | 0 / 0 |
| 140 | Early safe refill | 1117 | 450 | 5617 | 0 / 0 |
| 150 | Safe every-period baseline | 1321 | 450 | 5821 | 0 / 0 |
| 150 | Maximum safe wait | 1225 | 450 | 5725 | 0 / 0 |
| 150 | Optimistic variation law + fixed guard | 1225 | 450 | 5725 | 0 / 0 |
| 150 | Early safe refill | 1171 | 450 | 5671 | 0 / 0 |

The old v2 prudent policy, imported unchanged and evaluated on this plant, also
costs 5,821 but has **three unsafe pre-delivery periods: 661, 662, 663**. Probing
every tick alone does not protect the reserve against the jump. The fair safe
baseline uses H in its action guard, not merely the old policy's probe cadence.

The archived 1,325 and 2,211 costs come from v2's **10-to-20** jump, not this
10-to-140 case. Here total loss is 99,000. Conservation and final service alone
require at least `ceil((99000+100-440)/220)=449` delivered writes, costing at
least 4,490 before any probes. This universal conservation bound does not
assert that 449 writes suffice under the selected guard and calendar.

For context, archived v4 cost 5,421 including 83 root/token fees (5,338 for
probes/writes) and had six unsafe pre-instants. Early refill with H=150 costs
250 more than that full v4 total, or 333 more on the probe/write-only ledger.
This is a matched accounting comparison of different guarantees, not an
attribution of all cost differences to learning or to a universal safety tax.

## Fixed guard and policy definitions

The guard uses the hard H at all times. At a probe, combine the fresh
post-delivery lower bound with the carried lower bound derived **only from H**:

- readiness: `100 + H <= L <= 660`;
- wait d: require `L - H*d >= 100 + H`, with `1 <= d <= 40`;
- write: deliver at the next tick; carried endpoint `min(660, L-H+220)`;
- next observation: take `max(fresh_lower, carried_lower)`.

Thus a wait endpoint still funds one complete worst-case repair latency.
A write's pre-delivery reserve is at least `L-H >= 100`; its endpoint is ready
again because `220 >= H` and capacity covers the guard. Under the hard loss,
sensor and exact-dose assumptions, these inequalities inductively preserve
service and readiness. They are an arithmetic justification checked by the
study; they are **not new Lean proofs**. Availability.lean provides related
fixed-fallback results but does not automatically prove this Python adapter.

Keeping the valid carried bound avoids losing four units to a fresh sensor
error on each renewal. This carry is legitimate only because H is a fixed
physical hypothesis. The optimistic law is never used to propagate this bound.
The ideal full-capacity wait limit is 3 at H=140 and 2 at H=150; all observed
policies here actually wait at most 2 periods. H=140 reaches the service floor
exactly; the H=150 early-refill path has minimum pre-delivery reserve 160.

The safe every-period baseline writes if no one-period certified wait exists;
otherwise it waits one tick. Maximum-safe-wait takes the longest certified
wait, otherwise writes. Early safe refill instead writes early when the fresh
upper post-delivery reserve plus 220 is at most 660; otherwise it takes the
maximum safe wait. This refill condition avoids saturation without assuming
any positive minimum future leakage.

The optimistic policy proposes the v2-style wait using an observed rate plus
11 and its 12-unit handoff margin, clipped by H. Its wait is shortened by the
fixed guard; if no safe wait exists, it writes. A measured rate lower bound
above the preceding candidate ceiling permanently discards the variation law.
The single rejection is `139 > 22` at 661. There are 547/565 clipping events
for H=140/150. The policy uses the hard law thereafter. Reports and request
state are its inputs; true loss, jump time and future noise are not.

A rate exceeding H is refused only when its measured **lower bound** exceeds H.
Small violations can be hidden by sensor error, and between-probe violations
can escape observation. This study does not promise one-period detection for
arbitrary excursions outside H, nor safety after the physical premise fails.

## How much optimization remains in this action family?

An offline dynamic program explores every certified wait and early write,
using the known future plant and deterministic noise. It obtains:

| H | Hindsight optimum | Probes | Writes | Saturation loss | Final reserve |
|---|---:|---:|---:|---:|---:|
| 140 | 5454 | 944 | 451 | 420 | 240 |
| 150 | 5516 | 1016 | 450 | 110 | 330 |

A separate forward shortest-path implementation confirms both backward-DP
optima. This is an exact computational optimum **within the implemented
one-command / certified-ready-at-next-probe action family**, with only final
service required and no terminal inventory value. It is not a deployable
policy, an optimum across all physical controllers, or a proof that autonomous
learning can achieve it. The optimum may deliberately trade dose saturation
for fewer probes; neither saturation nor terminal reserve differences are
hidden. In particular, it is not an equal-final-reserve comparison.

For H=150 this optimistic comparator saves only 305/5821 = 5.24% relative to
the safe every-period baseline. The simple early-refill policy is 155 units
above it. Larger relative savings need different assumptions, hardware, cost
weights, or an action family beyond this one; the current numbers do not
support a dramatic learning gain.

## Reproduction and checks

```sh
python3 -B -m unittest discover -s research/boundary-cost-study -v
python3 -B research/boundary-cost-study/study.py
```

The second command regenerates [RESULTS.json](RESULTS.json); this is deliberately
repeatable exploratory computation. Eight tests check the guard for both H
values and all admissible integer one-tick losses, sensor enclosure including
saturation, sound rejection, irreversible candidate revision, policy safety,
and agreement of the two optimizers on short and full horizons. Three direct
mutations must fail: omitting repair-latency reserve, carrying the optimistic
20 instead of H, and dropping the sensor-error subtraction. Policy trace
hashes allow deterministic reproduction without presenting this computation
as a new single-shot experiment. CI reruns only this exploratory study.

Before a confirmatory v5, freeze the selected policy, H, cost model and precise
outside-boundary claim. New scenario seeds should be preregistered before any
inspection. The already explored v3 scenario must remain labelled as such.
