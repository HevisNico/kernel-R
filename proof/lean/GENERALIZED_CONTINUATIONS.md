# Generalized post-training continuations

This extension concerns irregular future inputs and universal observations of
finite complete executions. The global README is maintained separately.

## Two distinct learned regimes

The existing `learnedPulseContract` serves arbitrary `FutureSchedule (15/2)`
inputs in the isolated learned domain, with active gain in `[1.8,1.9]` and
recovery in `[0.17,0.2]`. Inputs need not be periodic and silences have no upper
bound. Each cycle starts from the actual state left by its predecessor.

The common-birth finite-chain endpoint has different memories: each active
log-gain is its own birth value plus `12/5`, and recovery is its own birth
value plus `3/10`. Its active gain lies in `[3.2,3.5]` and recovery in
`[0.37999,0.38001]`. Its earlier response cannot be inserted into the slower
learned-domain proofs by widening a bound: the physical phase ordering differs.
The continuation therefore uses the existing high-gain cadence constructors.

## New interfaces

`LearnedUniversal.lean` transfers the physically instantiated repeatable
regime to every complete finite execution of the same source program:

- `PulseContract.every_complete_prefix` proves the exact ordered per-cell
  response dates and the retained `LearnedDomain` at every settled prefix.
  The interface is generic in network size but still requires its physical
  `PulseContract`; the concrete instance supplied here is one cell.
- `PulseContract.complete_at_every_horizon_universal` supplies a complete
  witness at every finite horizon, includes every source due by that horizon,
  and compares all complete executions from the same finite source queue.
  It does not compare arbitrary different queue restrictions or assert a
  closed response formula for a horizon inside an unfinished cycle.
- `learned_every_complete_prefix` and
  `learned_complete_at_every_horizon_universal` instantiate those results with
  the existing physical one-cell law, rather than assuming a new cell law.

`HybridTerminalHighContinuation.lean` supplies the distinct higher-gain bridge:

- `ConstructedBirthCadenceChain.terminal_high_rest` derives the isolated high
  section from each actual finite-chain endpoint. `autonomousView` retains
  the destination-filtered queue; its emptiness follows from the proved
  global endpoint, rather than from deleting traffic.
- `terminal_high_continuation_exists` accepts a new first input strictly
  after the actual endpoint, arbitrary later input dates separated by at least
  `37/10`, and a terminal at least `37/10` after the last input. There is no
  upper bound on quiet gaps. The train must contain at least its first input.
- `terminal_high_continuation_of_complete_execution_exists` derives the same
  interface from any complete original-chain execution's actual endpoint,
  without an extra assumed endpoint or prepared-state premise.
- `IsolatedHighContinuation.every_complete_execution` gives the same physical
  endpoint and exact response calendar for every complete execution of that
  isolated input program. Latency is derived from the retained active gain.
- `every_complete_high_rest` preserves the reusable high section for every
  complete execution. `next_exists` starts another finite train from the
  actual constructed final state, including its evolved sensors and reserve.
  The actual delivery ledger contains exactly the declared new input tokens.

Schedules are arbitrary supplied data under the spacing condition. Their
finite source restrictions are explicit initial queues; these results do not
add an online source-injection operation or learned waveform generation.
The continuation preserves the acquired memories. It establishes reusable
learned responsiveness, rather than further learning during these new trains.

## Connected finite two-cell continuation

`HybridTwoCellHighContinuation.lean` connects two high learned cells with a
fixed positive delay. For external input dates `t`, leaf output dates are
`t + leafLatency`; root output dates are
`t + leafLatency + wireDelay + rootLatency`, with each latency derived from
that cell's own retained gain. Fixed shifts preserve irregular input gaps.

Only the leaf inputs occur in the external queue. Receiver analysis inputs
are derived from the leaf's actual FIRE ledger, and the causal weaver issues
their wire tokens at those FIREs. The terminal budget includes leaf latency,
wire delay and the final root settling interval.

`connected_two_cell_high_from_birth_exists` frames the new future leaf tokens
through the original birth execution and appends the connected continuation.
One fixed `extendTwoCellRouter` agrees with the earlier router through its
terminal clock and stays connected afterward. The combined ledger is exactly
the original ledger plus the new connected response ledger. This supplies a
finite connected case; it does not establish indefinite network progress.

The standalone `TwoCellHighContinuation.every_complete_execution` compares
complete continuations under `twoCellHighRouter`. The composed birth wrapper
uses `extendTwoCellRouter`; universal comparison there uses the generic
`Execution.observational_unique` with that same extended router.

## Scope boundaries

- Universal comparison fixes the initial state, source queue, parameters,
  router and horizon. It concerns finite executions complete through that
  horizon; it does not turn an incomplete or infinite run into a complete one.
- A one-cell coordinate projection is an isolated continuation, not an
  execution of the original connected network. At the finite-chain endpoint
  the global queue is already empty, so projection does not erase outstanding
  traffic. New future inputs are explicit source tokens.
- The original finite-chain router closes at `T+1`. The two-cell module
  explicitly supplies a routing extension and finite causal composition.
  Indefinite connected operation and arbitrary-depth continuation remain
  separate obligations.
- Fabrication parameters remain fixed; pulses retain the canonical shape.
  Operational noise, amplitude histories, drift and more general topologies
  remain separate proof obligations.

## Validation

All three modules are imported by `KernelR.lean` and included in the ordinary
project-wide axiom audit. From `proof/lean`, reproduce with:

```sh
lake build
lake build Audit
python scripts/check_sources.py
python scripts/generate_evidence.py --check
python scripts/robust_evidence.py --check
python scripts/check_generalized_continuations.py
```

The paired controls accept the stated conclusions and reject altered response
dates, recovery/gain changes, sensor resets, horizon changes and hidden
terminal traffic. The CI workflow runs this suite after the existing controls.
