# Progress and non-Zeno extension

## Statement and scope

These results use the first-contact operational definitions in `Hybrid.lean`.
The [threshold correspondence](../../docs/MODEL_LEAN_CORRESPONDENCE.md#threshold-contacts-and-upward-crossings)
records the proved correspondence with geometric upward crossings for the
constructed protocol. [HybridCrossingProgress](KernelR/HybridCrossingProgress.lean)
refines every finite weak/model prefix to native moves at any finite date
and extends every crossing prefix to any later finite horizon while preserving
its history. The infinite maximal-run results below retain their explicit
native `InfiniteExecution` interface.

For the existing constructed finite-chain protocol, strengthen the interface
from observations of already-complete competing executions to continuation
of **every finite competing execution**. Keep the original initial state,
parameters, physical equations, source queue and fixed router.

For every such finite execution `initialRun : Execution theta route born u` and
every real `H >= u.time`, the theorem proves

```lean
exists v, exists tail : Execution theta route u v,
  CompleteThrough (initialRun.append tail) H
```

No completeness premise is imposed on `initialRun`. The source queue is not
replaced, physical coordinates are not reset, and no event priority is added.
These statements concern the same finite network and finite source protocol;
they do not cover arbitrary new cyclic routers or infinitely many new sources.

## Existing ingredients

- `HybridUniversalExecution.lean`: physical flow uniqueness and cancellation
  of any enabled initial jump from a complete witness.
- `HybridObservationalTransport.lean`: re-present a continuation from the
  same physical snapshot with a permuted pending list, preserving move count.
- `HybridFlowCuts.lean`: prefixes and suffixes of actual integral flows.
- `HybridEventBudget.lean`: one natural number bounds actual physical jumps
  of every finite prefix ending by a fixed horizon, given birth, a physical
  parameter box and a uniform fanout bound.
- `HybridQuietFlowExistence.lean`: actual source-free quiet continuation.
- `HybridUniversalBirthCadenceChain.lean`: complete finite physical witness
  and its terminal READY state, absent RAW currents and empty pending queue.

## Finite continuation argument

[HybridFiniteProgress](KernelR/HybridFiniteProgress.lean) compares a competing finite execution with a
complete witness from the same source snapshot. Strong induction uses the
sum of their move counts, not elapsed time.

1. If the competing execution is empty, the witness is its continuation.
2. If its head is a jump, strip that enabled jump from the complete witness
   using the existing confluence theorem; continue with both residual traces.
3. If its head is a positive flow, a witness head which is a jump is impossible
   by urgency. Compare the two positive flow endpoints.
4. Cut the longer flow at the shorter endpoint. Flow uniqueness gives equal
   physical snapshots, up to pending-list permutation. Transport the residual
   witness to that actual snapshot and recurse. At least one move disappears.

The existing physical invariant is propagated after each actual move or flow
prefix. No future trajectory is assumed for the competing execution.

`RightMaximalThrough` means that the current state is at or before H and no
legal next move ends at or before H. If the continuation constructed above
were nonempty, its first move would contradict this maximality. Its empty
case establishes the endpoint date and saturation. Thus completeness is a
conclusion for a finite maximal trace, rather than its caller premise.

## Application to the finite-chain witness

[HybridChainProgress](KernelR/HybridChainProgress.lean) obtains a complete reference at every horizon
after birth:

- Before the original terminal T, use an existing saturated prefix of the
  constructed witness.
- At T, use that witness itself.
- After T, append the actual quiet flow from the terminal READY state.

Finite continuation then applies to every reachable finite endpoint, including
one already later than T. In particular it admits continuation by one model
time unit. Time can keep progressing after source exhaustion; this does not
assert unending activity, repeated FIREs or an additional clock source.

## Physical-event non-Zeno argument

[HybridNonZeno](KernelR/HybridNonZeno.lean) represents a countable sequence of actual moves and its
finite prefixes. For any fixed real horizon H, the pre-existing event-budget
theorem bounds the jump counts of every prefix whose endpoint is at or before H.
Therefore unbounded physical-jump counts imply unbounded physical time.

The condition `InfinitelyManyJumps` speaks only about counts, not dates. It is
not a disguised assumption of time divergence. It excludes the all-flow case
because splitting a flow is not a physical jump.

## Why a blanket infinite-run claim would be false

The current semantics permit arbitrary positive flow subdivisions. Even a
quiet cell can be presented at dates `t_k = 1 - 2^(-k)` with no physical jumps.
This is an infinite list of legal moves bounded by time 1, although the
underlying quiet trajectory extends beyond 1. For a flow from time 0 to 1,
the required subdivisions are restrictions of that same actual flow path.

Consequently, do not assert that every infinite move list has divergent time.
Do not count flow subdivisions as Zeno physical activity. Fairness for jumps
alone does not remove this example: there is no enabled jump to postpone.

## Semantic extension at a finite flow limit

`InfiniteExecution` is a countable move presentation. A bounded presentation
has a suffix consisting only of flows by the physical-event budget. Its
late finite prefixes are complete at their dates, as shown in
[HybridBoundedRun](KernelR/HybridBoundedRun.lean).

`InfiniteExecution.FlowLimitExtension` retains an actual finite prefix at an
anchor and replaces the remaining subdivisions by one legal incoming flow.
For each original tail interval the new flow agrees pointwise on full
snapshots, including coordinates, modes, RAW state and the queue. Its endpoint
is the limit of the dates and its coordinates are the limits of the original
coordinates. From this endpoint an actual finite continuation reaches a
strictly later date.

Given a complete reference past the bounded dates, the proof chooses its
incoming flow at the supremum of those dates and cuts that flow at a late
anchor. Uniqueness at the complete anchor relates the reference to the actual
run. Rebase the reference flow onto the actual anchor queue, and use flow
uniqueness on each original subdivision to obtain exact agreement. At a
limit that coincides with a jump, the incoming endpoint is the pre-jump
state. The finite continuation theorem then uses R's existing jump rules,
including simultaneous enabled events.

`InfiniteExecution.SemanticallyMaximal` means there is no such extension
through the final flow limit. Under birth, a physical parameter box, bounded
routed fanout and complete witnesses at all horizons, this is equivalent to
unbounded dates. Monotonicity then makes the dates eventually exceed every
finite horizon. `ConstructedBirthCadenceChain.maximal_run_progress` supplies
the fanout bound and all complete witnesses from the constructed finite-source
chain, under the physical parameter box. No divergent sequence is supplied as
a premise.

[HybridInfiniteExtension](KernelR/HybridInfiniteExtension.lean) gives a separate existence construction
from every supplied finite history. It joins coherent finite execution
segments at unit-spaced horizons by actual `Execution.append` and derives
their divergent dates. The unit is a choice of continuation horizons. The
construction makes no identification of this segment type with the
countable-move interface used in the maximality theorem.

## Validation gate

The complete `lake build` includes the proof modules and `Audit`. The
semantic audit checks imported and owned project theorem declarations,
including private declarations, and permits only `propext`,
`Classical.choice`, and `Quot.sound`.

The three paired semantic controls first compile the valid claims and then
reject the false alternatives with Lean diagnostics. Audit controls also test
public/private and current/imported declarations in `KernelR` and `A22`,
including unused private proofs and isolated added assumptions. Run these
commands from `proof/lean`.

```sh
lake update
lake exe cache get
python -B scripts/check_sources.py
lake build
lake build Audit
python -B scripts/check_audit_negative.py
python -B scripts/check_progress_negative.py
```

Check the printed assumptions for the new entry points. The finite-continuation
proof handles simultaneous jumps and both orders of unequal flow cuts.
[HybridProgressControls](KernelR/HybridProgressControls.lean) proves that the actual one-cell bounded subdivision has a semantic
extension through its flow limit.

## Physical rate limits and terminal saturation

The separate [recovery-limited rate theorem](../../docs/RESET_RATE_SATURATION.md)
uses physical protection to bound the number of firings in existing executions.
This physical saturation differs from terminal jump saturation in
`CompleteThrough`. A firing-rate bound alone does not prove continuation for
an arbitrary queue/router and does not replace any progress hypothesis here.
