# Repeatable physical one-cell learned cycles

`learnedPulseContract` constructs an actual one-cell cycle with empty routing
and settling duration `7.5`. Each input produces exactly one emission, preserves
all gain/recovery memory and returns to the same learned domain. Reserve stays
in `[50,100]`; sensor charges and energy evolve through their actual ODEs.

The resulting guarantee is constructive existence of compatible responding
continuations. It does not assert birth/training reachability, finite-chain
routing or universal refinement of every admissible execution.

## Main results

| Result | Statement |
|---|---|
| `learned_return_exists` | Actual raw-end, ERROR, FAST and SLOW completion returns to the learned domain before `7.5`, with one emission and unchanged memory |
| `settled_learned_cycle_exists` | The physical idle flow completes the cycle at the uniform deadline `7.5` |
| `learnedPulseContract` | A physical `PulseContract` for every state in the declared one-cell learned domain; latency is fixed by reference memory |
| `learned_unbounded_responding_prefixes` | Compatible executions reach unbounded times with exactly the scheduled firing list |
| `learned_complete_at_every_horizon` | A complete execution exists at each finite horizon, with every input due by that horizon included in its finite initial queue |

The last two results require input spacing at least `7.5`. Parameters are fixed
in either declared fabrication box; amplitudes are canonical. Operational
drift/noise/amplitude histories are not instantiated.

## Entry assumptions and relation to the physical foundation

`LearnedRest` requires all modes READY, no raw current or pending tokens, exact
main charge `q=0.1`, auxiliary charges within `1e-5` of `0.025`, reserve in
`[50,100]`, selected gain in `[1.8,1.9]`, recovery in `[0.17,0.2]`, and all
log-gains below their physical caps. `LearnedDomain` additionally fixes every
log-gain and recovery coordinate to a reference snapshot. Sensor charges and
reserve may differ between rounds and are never reset.

The physical foundation's `PreparedSection` allows residual main charge and a
narrower recovery band. Its `Execution.learned_pulse` analyses a supplied,
birth-reachable isolated-input execution. The main branch also constructs the
birth-to-teaching prefix and first reverse FIRE described in the
[physical checkpoint](HYBRID_EXECUTION.md#constructed-protocol-checkpoint).
This extension constructs repeatable executions from `LearnedRest`; a formal
bridge from those birth/training endpoints to this exact domain is still needed. Fixed reference latency here uses exact main
rest; it does not extend to the positive residuals covered by
`first_firing_le_rest_reference` in the physical foundation.

## Proof map

| Modules | Role |
|---|---|
| `HybridFrozen` | Fixed-mode charge solutions and a reserve solving the forced ODE with actual work; modes must suppress plasticity |
| `LearnedResponse`, `LearnedCycleBounds`, `LearnedCycle` | Real crossing, phase-duration and chronology bounds |
| `LearnedCycleStart`, `LearnedDriven`, `LearnedFiring` | Actual source arrival, MARK, SILENT and first main firing; the raw origin and passive sensor bounds survive flow cuts |
| `LearnedProtected`, `LearnedRecovery` | Protected FAST spans and actual raw-end cuts, followed by auxiliary return to READY |
| `LearnedReturn`, `LearnedSingleCell` | Actual FAST/SLOW exits, learned-domain closure, settling and the one-cell contract |
| `HybridFuture`, `Indefinite` | Physical waiting, future-queue extension, compatible prefixes and complete horizon extraction |
| `FutureControls`, `LearnedCycleControls` | Nonempty physical witnesses, periodic finite-horizon executions and counterexamples to overstrong assumptions |

Every flow checks strict guards, raw support and pending-token urgency. The
auxiliary finishes ERROR after raw end and before FAST exit, keeping the
plasticity gates off. FAST and SLOW reach their actual exit charges `1/4` and
`1/10`; legal jumps restore READY. Passive sensors contract toward rest.

Raw end may precede or follow ERROR entry. `FastProtectedProfile.advance`
constructs both cases and handles equality without a positive-duration flow.
`error_raw_end_commute` constructs both zero-time orders to the same snapshot.

## Future inputs

The general `PulseContract` interface remains parameterized in `Indefinite`;
`LearnedSingleCell` supplies its physical instance. Latency is selected once
from the reference log-gain, and every constructed firing has that same first
crossing because memory is preserved.

For input dates satisfying `input(k)+7.5 <= input(k+1)`, the firing list of prefix
`k` is exactly `[input(0)+latency, ..., input(k-1)+latency]`. Each cycle starts
from the actual state left by its predecessor. Future tokens can be added to
an earlier initial queue without changing that earlier physical ledger.

Horizon extraction processes enabled zero-time events at the cut and includes
all sources dated at or before it. No infinite pending list or additional
source-injection jump is assumed, including at exact cycle-boundary inputs.

## Remaining work

- Connect the existing birth/training constructions to this exact learned domain.
- Finite-chain routing, wire delays and a sufficient network settling duration.
- Universal refinement across all admissible complete executions.
- Operational drift, noise and amplitude histories.

## Validation

`lake build` includes all modules and the global `Audit` target. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed. Controls instantiate the full
return, the contract and complete periodic executions at every finite horizon.
Existing physical/audit negative controls, Python tests, source identities and
all 16 robust certificate replays remain part of validation.
