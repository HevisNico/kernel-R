# Obligations for a reusable native round

This is a specification and source review, **not a proved native controller bridge**.
The reference is Kernel R commit `518852d237dd4d45eda2c2b85aaad2e592bfdf89`.
The [read-to-rest checkpoint](NATIVE_RETURN.md) and
[finite re-preparation proof](NATIVE_REPREPARE.md) were necessary sub-obligations,
not a closure of reuse. The [recurrent construction](NATIVE_ROUNDS.md) now
proves a preserved boundary, fixed calendar, arbitrary finite iteration and
universal complete-run behavior. It remains distinct from a native realization
of M1 and from an unbounded autonomous scheduler.

## Why the existing cycle cannot simply be iterated

1. [`SelectorReadRun`](../recursive-learning/native/Teaching/SelectorRead.lean)
   preserves the gains and empties the queue, but its `mainClock` places the
   terminal main unit in FAST or SLOW. The start of `SelectorReadPrepared`
   requires READY with charge between `13/20` and `39/50`, plus an admitted
   read pulse. The endpoint is not another prepared read.
2. [`cappedCycleRouter`](../recursive-learning/native/Teaching/TeacherCappedCycle.lean)
   only routes the initial ignition when `fire < origin + 1`. The later read
   intentionally does not retrigger it. A second cycle needs a persistent
   routing design; rebasing `origin` separately for each fragment would change
   the router and would not establish one execution of a fixed network.
3. [`capped_dispatch_arrives`](../recursive-learning/native/Teaching/CappedDispatch.lean)
   ends when the output reaches the learner, before the controller's FAST
   phase ends. It establishes delivery, not the readiness of a second round.
4. The existing [capped controller](../recursive-learning/native/Teaching/README.md)
   assumes recovery at cap, a prepared ignition gain and a saturated work
   port. Credit memories belong to another cell. Connecting them and preparing
   the controller remain obligations, not consequences of this discrete model.

## Proposed round boundary

Define a native boundary invariant over the actual snapshot and a decode of
the retained lesson and the two blocked bits. It must expose:

- the main and auxiliary modes and the charge bands required by the next round;
- absence of expired raw pulses and a precise pending-delivery discipline;
- reserve and recovery bounds, including any recovery changes caused by MARK;
- persistent lesson and blocked-bit memories, with physical bounds/headroom;
- the fresh validation resource or a separately proved learner-reset mechanism;
- the fixed parameter family and the one router used throughout the run.

Do not set charge, gain or time back to an initial value by definition. Return
to the boundary must be an actual native flow/jump continuation. Starting
with prepared resources is acceptable for a first theorem if stated explicitly.
Preparation from birth would be a separate theorem.

## Next proof targets

| Target | Required evidence |
|---|---|
| Read-to-rest continuation | Constructed for both values with positive recovery, quiet sensors and an empty queue; see [the checked scope](NATIVE_RETURN.md). Initial preparation and physical invariants remain explicit |
| Re-preparation | Constructed for either selector value with one initially queued ignition and two routed inputs; exactly three new deliveries; see [scope and assumptions](NATIVE_REPREPARE.md) |
| Fixed-router selector reuse | Constructed for every finite count under one periodic router, preserving the actual future queue; see [M2](NATIVE_ROUNDS.md). Physical validation feedback is not connected |
| Acceptance and rejection | Actual learner reports decide whether the candidate is committed; rejection keeps the accepted lesson and permits the other coordinate |
| Decode refinement | The decoded native endpoints implement `round`, with an explicit map for unavailable decrements and halting |
| Cost refinement | Bound native proposals, validation, reports, memory writes and reset in the units chosen for `work`; identify fresh-resource costs |
| Selector iteration | Constructed with `3*n` deliveries, or `3*n+1` with the actual initial read arrival; complete native/crossing witnesses and universal endpoint/FIRE guarantees |
| Controller iteration | Connect selector cycles, validation, acceptance and retained lesson updates under one router; this does not follow from selector iteration alone |

The discrete convergence theorem does not discharge any row of this table.
The native return, re-preparation and recurrence proofs discharge their
selector rows under the explicit prepared-resource and finite-calendar premises.
Finite complete witnesses must precede a universal comparison claim; comparing
only complete runs is not an existence or progress argument. Threshold-contact
and geometric-crossing hypotheses must be retained when using that semantics.

## Design constraints established by this milestone

The discrete search needs only one-way blocked bits. It first exhausts
preparation reductions, then practice reductions. It does not require a
selector bit to alternate indefinitely, which would silently require erasure
or another encoding in a monotone-gain implementation.

The two-block separability matters: once a coordinate reduction is rejected,
changing the other coordinate cannot make that rejected reduction valid.
Remembering the rejection is sound for this learner. For a coupled task the
blocked-bit invariant and optimality proof must be reconsidered.

The [bounded adaptive milestone](ADAPTIVE.md) now selects a search policy from
a finite family using inexact evaluation, with immutable rules, preserved
invariants and explicit costs. It does not claim an unbounded number of strict
improvements, recurrent-network learning or transistor-level correspondence.
Its benchmark and error bounds are fixed; ambiguous probes cannot justify
permanent blocks. It remains separate from the native obligations above.
All four selector-reuse obligations are covered by [M2](NATIVE_ROUNDS.md).

The [physical-certificate checkpoint](physical/README.md) derives exact finite
counts and a zero-error margin evaluator under explicit scalar observation
premises. Its pulse-accounting theorem and recorded-data replay do not supply
the native feedback/refinement, fresh-resource/reset or physical cost rows
above. The six-cell calibration-transfer limitation also remains explicit.
