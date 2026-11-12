# Obligations for a reusable native round

This is a specification and source review, **not a proved native bridge**.
The reference is Kernel R commit `518852d237dd4d45eda2c2b85aaad2e592bfdf89`.

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
| Read-to-rest continuation | Extend both high and low read outcomes through FAST/SLOW, retaining memories and accounting for every sensor phase and pending event |
| Re-preparation | Reach the next read/precharge bands from the resulting state, using real input tokens and counting their costs |
| Fixed-router reuse | Distinguish ignition, work, read and feedback events for multiple rounds without replacing the router or predetermining the validation outcomes |
| Acceptance and rejection | Actual learner reports decide whether the candidate is committed; rejection keeps the accepted lesson and permits the other coordinate |
| Decode refinement | The decoded native endpoints implement `round`, with an explicit map for unavailable decrements and halting |
| Cost refinement | Bound native proposals, validation, reports, memory writes and reset in the units chosen for `work`; identify fresh-resource costs |
| Iteration | Compose the native rounds under the same router, with an explicit resource budget and complete witnesses |

The discrete convergence theorem does not discharge any row of this table.
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

No claim is made here about an unbounded number of strict improvements,
learned search strategies, recurrent-network learning, or transistor-level
correspondence. The next milestone is the physical read-to-rest and
re-preparation continuation, with its preparation assumptions explicit.
