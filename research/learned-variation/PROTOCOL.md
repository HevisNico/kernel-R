# R2: learn a refutable sampled-variation envelope

Preparation dependent on R1 (#117). Do not declare the next milestone reached
until every workflow and latest-attempt job of R1's exact reviewed head has
succeeded. R1's sources and evidence remain unchanged. No campaign is run by
this milestone: its numerical examples are deterministic unit fixtures.

## What is learned

Use the v2 upward-excursion form, not an unidentified derivative: for a fixed
integer horizon H, the candidate rule is `rate(t+k) <= rate(t)+B`, `0<=k<=H`.
The learner starts B=0 and chooses an integer B in [0, cap] from observations.
The cap is a resource limit on candidate search, **not** a physical ceiling.
H, cap, validation length W and the total observation budget are fixed before
observation; require H>0 and W>=H. Production defaults are H=41, W=41.

For each new rate interval [lo,hi], compare every retained earlier interval
[oldLo,oldHi] with `0 < newTime-oldTime <= H`:

- The conservative sampled requirement is `max(0, hi-oldLo)`.
- A demonstrated refutation of old B requires `lo > oldHi+B`.
- A larger conservative requirement without this separation is an ambiguous
  enlargement, not proof that the physical law failed.

Choose the maximum of the previous B and all these requirements. Retain the
whole finite observation history in this first implementation, bounded by the
predeclared total sample budget; do not introduce a rolling-memory proof gap.
Do not shrink B or forget earlier requirements after a new epoch. If the
required value exceeds cap, exhaust learning; never clamp to cap and call it
fitted. Missing, stale or wrongly scheduled observations fail closed.

This learns a conservative envelope of **sampled interval pairs**. It does
not identify the true smallest B: a constant true rate 10 with radius-one
reports 9 then 11 already requires B=4 by the robust rule, without a physical
refutation. Unsampled interior excursions and future behavior remain unknown.

## Fixed prospective validation

Every strict widening starts a new epoch and freezes its candidate. Its
triggering sample is the training anchor, not a successful validation step.
Require W subsequent consecutive one-period transitions with no enlargement.
A widening restarts at the larger candidate; a missing/stale tick faults.
Once validated, ordinary renewal cannot reset the same candidate's window.
Only strict widening can create a new validation window. W transitions mean
W+1 samples including the anchor, and W>=H includes a complete H-span.

A passed window permits only an explicitly `provisional-unguaranteed` policy.
It must never be converted automatically into R1's external authorization.
The physical service theorem still requires the future rule, honest sensors,
state flow and delivered dose as premises. In particular, no learned window
asserts unconditional uninterrupted service.

## Refutation and accounting

Record each widening with old/new B, the triggering interval evidence, and
the affected previously monitored interval. Keep demonstrated and ambiguous
events separate. Append revocation annotations without changing previously
emitted claims or deleting unsafe exposure. No new policy may skip the next
scheduled observation or stop charging probes while it searches for a rule.

Strict widening decreases the finite potential `cap-B`; with B initially 0
there are at most cap widenings. There is at most one prospective window per
candidate. At most `(cap+1)*W` successful validation transitions and cap
widening witnesses are learning-related; ordinary provisional monitoring
and the initial anchor are charged separately. A shared observation is paid
once even if used by the plant supervisor, monitor and validator. A separate
finite total observation/action budget bounds the complete execution and
ends explicitly unguaranteed if exhausted. No cost credit is replenished.

## First deliverable and exclusions

First deliver the checked envelope learner and its prospective-window state
machine, with an executable observation-only interface, whole-prefix sampled
soundness, strict-widening and budget theorems, honest labels, and adversarial
unit fixtures/mutations. A proposal is not yet a physical authorization or a
new performance result. Keep the R1 recovery adapter intact.

The provisional plant-policy composition and a randomized multi-scenario
comparison require a subsequent registered protocol before any trajectory
execution. The two-level learning tower and transistor-level R bridge remain
later work. No statistical confidence level is claimed for this deterministic
bounded-error learner.
