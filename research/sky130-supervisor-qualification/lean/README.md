# Conditional deterministic supervisor contract

This module generalizes the discrete safety part of v5 for variable maintenance
doses and a capacity constrained by both analog operation and other read
semantics. It does **not** certify the SKY130 netlist, fill an envelope from
observed extrema, or establish a hard Gaussian-noise bound. The circuit runner
is not connected to this kernel in phase 1.

## Proved control contract

All reserve quantities are integers in a physical scale to be fixed later;
measurements must be rounded outwards. Let

- `C = min(linearCapacity, semanticCapacity)`;
- `0 <= loss <= H` for the **whole service period**;
- `Dmin <= delivered dose <= Dmax`, with `Dmin >= H`;
- observation error be in `[-epsilon,epsilon]`;
- `C >= S + 2*H + 2*epsilon + Dmax`.

The last condition is a sufficient robust room condition for this particular
one-period wait/refill policy, not a necessary physical feasibility criterion.
A small semantic capacity can make it fail even if the integrator is linear.
That outcome must be reported; the theorem cannot manufacture room.

The invariant is `carry >= S+H`, `carry <= actual reserve <= C`. The executable
kernel encloses reserve with `lower = max(report-epsilon, carry)` and
`upper = min(report+epsilon,C)`. It requests clock-only maintenance only if
`upper+Dmax <= C`; otherwise it waits only if `lower >= S+2H`. Under the
conditions above the bounded interval width forces one of these choices to
be available, so there is no refusal inside the enclosed domain.

`segment_safe` proves the current mandatory service's reserve floor and the
next invariant from an actual bounded loss and dose. `run_invariant` proves
preservation by induction for the canonical execution, and
`every_service_safe` proves the service floor at every period, for any finite
or infinite enclosed trajectory. No premise assumes that the sequence is
already safe. The lower carry uses **Dmin** and the overflow guard uses
**Dmax**. There is no saturation/clipping operator concealing an overfill. The world's
`dose` is the dose available when maintenance is requested; its value is unused
on wait periods and does not charge or deliver an imaginary wait-period write.
`every_boundary_respects_semantic_capacity` also proves that every boundary
reserve stays below the separate semantic cap.

H refers to the total cumulative loss in one 440 us period. It is not charged
twice merely because service and maintenance have 220 us slot spacing. The
conservative service floor is `reserve-H`, before the possible write. A bound
for a 220 us segment may be summed into a whole-period bound; a whole-period
bound may not be divided by two without a separately justified cumulative
rate envelope. The physical bridge must cover the service, maintenance write
window (about 35–41 us after its clock), later drift and next observation.

## Physical obligations remain explicit

`Enclosed` is a deterministic premise for every period, not a statistical
summary of the sampled corners, mismatch seeds or temperatures. It includes
nonnegative effective loss. If deterministic transients admit beneficial
reserve motion, that has to be enclosed separately and the upper guard
strengthened; noisy negative voltage differences are not silently discarded.

`PhysicalRefinement` exposes two obligations rather than pretending to prove
them: recovery/timing readiness at every service, and the implication from
the certified reserve range to a correct physical FIRE. This implication must
include the new stimulus schedule, main-charge residual, observer/state map,
and other-read compatibility of the chosen semantic capacity. These are not
provided by this file. `refined_zero_failed_services` transfers the discrete
result only when this refinement is supplied.

In particular, no numerical semantic capacity, count-preservation theorem,
transistor reachability enclosure, Gaussian-noise guarantee or unconditional
first-probe detection guarantee is claimed. `measured_loss_violation_sound`
only says that a lower-error-adjusted loss exceeding H proves an actual
violation. `monitoredChoice` refuses such an observation and agrees with the
safe kernel inside H when the loss report is sound. This optional monitor is
not wired to a physical observer here; it does not say every arbitrarily small
violation is detected.

## Charged preparation and entry

`EntryCertificate` requires a fresh observation whose lower bound is at least
S+H and whose upper bound fits C, with a sound sensor error premise. Starting
the service execution requires this certificate. It also carries an explicit
list of preparation maintenance/observation events and an indexed
`PreparationTrace` linking the initial reserve to the certified entry reserve.
Each observation preserves state; every maintenance requires a sound upper
reading, bounded loss/dose, and `report+epsilon+Dmax <= C`.
`guarded_preparation_step` proves both the minimum gain and no overflow;
`preparation_trace_respects_capacity` inductively bounds the completed trace.
The ledger is therefore linked to the same discrete preparation transitions,
not an arbitrary counter. This does not prove that the transistor startup
realizes those transitions; that correspondence remains an audit/refinement
obligation. Preparation has no service
label; a preparation silence cannot count as a failed or successful guaranteed
service (`preparation_silence_is_not_a_service`). The runtime trace audit must
establish the physical correspondence of these records and the service-start
boundary; the type alone does not authenticate a simulator log.

`preparation_cost_exact` charges every recorded preparation event.
`preparation_budget` bounds that cost under an explicit event-count limit.
`preparation_progress` bounds the gain of a valid maintenance but does not
promise that preparation always succeeds or that a physical setup reaches
entry. If entry cannot be certified within its budget, service must not begin.

The canonical execution issues at most one maintenance per service period,
proved by `maintenance_count_bounded`. With N services and N+1 observations,
`actual_run_cost_bounded` gives

```
preparation cost + N*maintenance price + (N+1)*observation price + N*service price.
```

These are declared accounting weights, not energy. The theorem explicitly
retains preparation cost, and no terminal-stock economic saving is claimed.

## Verification

From this directory, with Lean4.35.0 on PATH:

```sh
lake build
python3 -B check_negative.py
```

There are 31 explicitly named theorems. The audit covers 361 declarations,
including 142 theorem declarations with generated ones included.
`Audit.lean` checks all declarations in `Sky130Supervisor`, rejects unexpected
axioms (only `propext`, `Classical.choice`, `Quot.sound` allowed), and requires
the central named theorems. The nine direct mutations must fail Lean proofs:
removing Dmax from the maintenance guard, substituting Dmin there, using Dmax
for the lower carry, replacing the minimum capacity by a maximum, doubling
service loss without changing its guard, dropping charged preparation, and
counting a training silence as a guaranteed-service failure, and suppressing
the observed-loss refusal, and removing Dmax headroom during preparation.
