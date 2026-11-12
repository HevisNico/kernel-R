# M2: reusable native rounds on a fixed calendar

The earlier finite re-preparation checkpoint chose its ignition date from a
constructed return. That did not close reuse. M2 now requires all four items
below; the adaptive-search milestone cannot substitute for any of them.

| Obligation | Native result |
|---|---|
| A preserved recurrent boundary | `RoundReady`, `ScheduledRoundReady`, `calendar_round_exists` and the carried-round contract |
| A calendar fixed before execution | `roundDate origin k = origin + 32*k`, `roundIgnition`, `roundRouter`; the construction quantifies every admissible supplied delay |
| An actual finite recurrence | `calendar_rounds_exists`: every natural `n`, one router, exactly `3*n` deliveries; `delivered_calendar_program_exists` includes the first read and costs `3*n+1` |
| Guaranteed complete-run behavior | `CalendarRound.every_complete`, `CalendarRounds.every_complete`, `DeliveredCalendarProgram.every_complete`; geometric-crossing counterparts are also proved |

Implementation: [SelectorRound.lean](../recursive-learning/native/Teaching/SelectorRound.lean),
[SelectorRounds.lean](../recursive-learning/native/Teaching/SelectorRounds.lean),
[SelectorRoundBootstrap.lean](../recursive-learning/native/Teaching/SelectorRoundBootstrap.lean)
and [SelectorRoundUniversal.lean](../recursive-learning/native/Teaching/SelectorRoundUniversal.lean).

## The boundary is quiet, not an already active read

`SelectorReadPrepared` requires an active port-2 RAW and charge at least
`13/20`. It cannot also mean "no RAW". `RoundReady` instead describes the
quiet READY boundary from which the three inputs construct another prepared
read. Its fields retain:

- the native physical invariant, including energy reserve;
- main READY in the existing resting charge band, and every sensor READY in
  `RestBand`;
- no active RAW and, for an isolated round, no pending token;
- recovery exactly `11/10`;
- ignition gain in `[9/5,11/5]`, work log-gain exactly `log(cap 0)`, and the
  same selector log-gain, either `0` or `3/5`.

The return reaches charge `1/10`; the actual quiet wait relaxes toward
`1/10`, without resetting coordinates. Every gain and recovery are preserved.
No extra pulse is needed to restore their bands in this capped case. Energy
continues under the native ODE; its initial value is not restored.

The intermediate state of an `n`-round execution still carries future
ignitions. `ScheduledRoundReady` makes that distinction explicit: its queue
has exactly the remaining calendar tokens, up to permutation, while its
non-queue state satisfies the same physical boundary invariant. The carried
round preserves this invariant. Clearing the queue in the predicate is only
a way to state the non-queue fields; the actual execution carries the queue
through every flow and jump.

## One clock and router for all rounds and admissible delays

Let the calendar origin be `O`. Round `k` starts at `O+32*k`, and its external
ignition token is due at `O+32*k+1`. The router emits work/read tokens only
when a FIRE lies in `[O+32*k+1, O+32*k+2)` for some natural `k`. This router
does not depend on the requested number of rounds and is never replaced.

The proof uses the existing physical parameter box, and an arbitrary supplied
work-delay function satisfying the certified interval at every FIRE, with
jitter at most `73/40000`. The same period and ignition dates work throughout
that box. They are not selected from an execution's eventual return time.
The read token retains the existing fixed offset `7/5` after the work token;
no additional independent read-wire jitter is introduced by this theorem.

For a round starting at `t`:

1. The prescribed input at `t+1` produces ignition FIRE in `(t+1.3,t+1.9)`.
2. That FIRE routes the actual work and read pulses. Read admission occurs
   before `t+6`; the later read FIRE falls outside every ignition window.
3. The read and native FAST/SLOW return finish before `t+18`, uniformly.
4. A real silent flow extends the returned state to `t+32`. Future ignition
   tokens remain strictly later, so none is delivered during this wait.

Period 32 is deliberately conservative. It is a proved sufficient period,
not an optimal period or a measured hardware clock specification. The
return bound uses the explicit exponential return date exported by
`QuietMainReturn`; no eventual execution is assumed to obtain that bound.

## Finite recurrence and complete input accounting

`calendar_rounds_exists` performs induction on `n`. Each step consumes the
current ignition token, routes the work/read pair and passes the actual
terminal state into the next construction. All later ignition tokens are
lifted through the whole preceding execution with `withFuture`. None is
inserted at a boundary. The queue list is presented in reverse chronological
order; the existing operational semantics delivers due tokens without
assuming list order is chronological.

From a quiet boundary, the exact totals are `3*n` deliveries and `2*n` FIREs.
The initially prepared-read version also constructs the first input
admission as a native arrival. Its actual initial state has no active RAW;
the initial queue contains that read token and all `n` future ignition
tokens. The first read returns and waits until `O = initialTime + 32`.
The complete programme ends at `initialTime + 32*(n+1)`, with exactly
`3*n+1` deliveries and `2*n+1` FIREs, including the `n=0` case.

`prepared_delivered_calendar_program_exists` instantiates every finite `n`
and both selector values with explicit physical initial resources and a
constant admissible work delay. It proves existence without supplying future
traces, resets or successful outcomes as hypotheses.

## Every complete execution

The uniqueness theorems compare the constructed witness with any other
complete native execution from the same initial snapshot, parameter family,
router and supplied delay function, through the same declared horizon.
No chosen interleaving, input ledger or transverse-contact certificate is
required from the competing native trace.

`observational_unique` supplies matching physical coordinates, modes, RAW
and FIRE observations. Queue conservation gives equal delivery multiplicities
and cost. The final queue is empty, so observational equality becomes literal
equality of the final snapshot. The same guarantees are transferred to
complete geometric-crossing executions, with constructed crossing witnesses.

These are guarantees for each fixed admissible parameter/delay choice.
They do not assert that different admissible choices produce identical FIRE
dates. They share the fixed calendar and proved bounds, while their internal
FIRE dates may vary.

## Validation and remaining scope

With Lean 4.35.0 and the native dependencies:

```sh
cd research/recursive-learning/native
lake build
cd ../../reusable-controller
python3 verify_native_rounds.py --report native-rounds-validation.json
```

The eight-module focused audit includes every declaration in the relevant
return, re-preparation and recurrence modules, including unused/private/
generated declarations. It follows axiom dependencies and permits only
`propext`, `Classical.choice` and `Quot.sound`. The full native audit imports
it. Eight controls test weakened recovery, overlapping periods, a shifted
ignition, omitted first-read cost, an occupied initial read port, comparison
without completeness, an unused axiom and an admitted return-clock proof.
Parser/import failures do not count. The [validation record](native-rounds-validation.json)
contains source hashes; CI rebuilds the complete package and repeats these
controls alongside the preceding twelve native controls.

This is reusable operation for any **prescribed finite count**, with prepared
resources and a fixed external ignition calendar. It does not prove an
unbounded autonomous oscillator, preparation from birth, implementation of
the clock/router in transistors, physical execution of M1's search or adaptive
policy changes. Pulse count is not energy or complete search cost. Those
remaining integration obligations are tracked in [NATIVE_HANDOFF.md](NATIVE_HANDOFF.md).
