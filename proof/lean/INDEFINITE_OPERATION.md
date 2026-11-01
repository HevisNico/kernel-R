# Repeatable physical one-cell learned cycles

`learnedPulseContract` constructs an actual one-cell cycle with empty routing
and settling duration `7.5`. Each input produces exactly one emission, preserves
all gain/recovery memory and returns to the same learned domain. Reserve stays
in `[50,100]`; sensor charges and energy evolve through their actual ODEs.

The resulting guarantee is constructive existence of compatible responding
continuations. A separate bridge now derives this domain for Aport2/Bport2
coordinate projections of the constructed639.9 state. Finite-chain routing and
universal refinement of every admissible execution remain open.

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
birth-reachable isolated-input execution. The original READY-birth construction
now reaches [C's protected MARK return at660](HYBRID_EXECUTION.md#constructed-protocol-checkpoint)
after the fully prepared639.9 endpoint and first C→B→A wave. C is READY at
q=0.1 with fresh RAW660 and19 future C sources; A/B retain their actual cuts.
This network prefix is separate from an isolated learned-domain return of
all three cells.

[HybridBirthLearnedRest](KernelR/HybridBirthLearnedRest.lean) proves
`ConstructedCTeaching.a_learned_rest` and `b_learned_rest` for the Aport2/Bport2
coordinate projections at639.9. The actual prepared coordinates supply exact
charge rest, READY modes, RAW absence, sensor bands, reserve/caps and recovery.
Each own birth port2 log-gain+1.8 yields active gain in[1.8,1.9]. The resulting
`a_pulse_contract`/`b_pulse_contract` and finite-horizon wrappers construct
isolated one-cell futures from these projected states. No additional newborn
or desired output trace is assumed.

The projections' empty analysis queues are not physical operations on the
global state: its25 C640..736 tokens remain. Each isolated continuation uses a
new future source queue and empty routing. Cport1's learned gain near2.18 is
outside the imported domain, so this bridge does not cover that port. Broader
birth families, network routing and universal refinement remain open. Fixed
reference latency uses exact main rest; it does not extend to the positive
residuals covered by `first_firing_le_rest_reference`.

The constructed global C660 extension has a different recovery state:
C's protected C656 MARK derives its own newborn recovery+0.2, near0.28.
It retains A/B's actual paths and consumes C660, leaving19 later C sources.
This does not change the bridge above, which concerns the actual639.9
Aport2/Bport2 projections and imported recovery domain[0.17,0.2]. C660's
recovery is outside that domain.

The separate `ConstructedCadenceLocalC` now gives an actual finite C-only
execution639.9→789.9. `c.local_c_full_exists hb` projects C's actual global
prefix through660, retaining its source queue and physical observations, then
appends the constructed local tail. It consumes all 25 sources640..736 and
emits 20 cadence signals (cumulative C34 including teaching). At789.9 C is
READY/q=0.1 with no RAW or pending tokens, own newborn port0 log-gain+2.4 and
recovery+0.3; other gains retain their teaching values. Its real ledger derives
P(3,17,0), and bounded delays sampled at FIRE give P(3,17,1/20) token labels.
These labels do not construct global arrivals or advance A/B beyond660.

This finite cadence construction does not instantiate `LearnedRest` for its
higher gain/recovery endpoint or provide indefinite contracts for every C
state. The isolated learned-domain theorem above and the global network
continuation remain separate results.

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
| `HybridBirthCadenceLocalC` / `HybridConstructedCadenceLeafPacket` | Separate finite autonomous C639.9→789.9 execution and real-ledger leaf packet; no learned-domain or global indefinite-network conclusion |
| `HybridBirthLearnedRest` | Exact learned-domain membership of Aport2/Bport2 projections at639.9, isolated pulse contracts and complete finite-horizon futures |

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

- Extend the projected Aport2/Bport2 bridge beyond the declared READY-birth
  subfamily and establish physically routed network continuations.
- Finite-chain routing, wire delays and a sufficient network settling duration.
- Universal refinement across all admissible complete executions.
- Operational drift, noise and amplitude histories.

## Validation

`lake build` includes all modules and the global `Audit` target. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed. Controls instantiate the full
return, the contract and complete periodic executions at every finite horizon.
The autonomous-C/leaf-packet checkpoint passed the complete pinned build
(9,458 jobs) and global audit (25,538 project theorems). Source identities
cover405 Lean files and five unchanged upstream modules. Generated evidence,
all16 robust certificates and12 project tests pass. Its53 additional paired
controls pass:25 local-C-tail,20 constructed-leaf/projection and8 new actual
high-return-prefix checks. The complete high suite now has32 passing pairs.
Each valid conclusion compiles and every altered conclusion is rejected with
a Lean diagnostic. Earlier C660/first-wire/first-wave controls passed at their
checkpoints. CI configures877 paired controls; this inventory does not assert
a local rerun of every suite. Fresh CI status is reported on the PR.

These isolated future contracts remain distinct from the actual C→B→A network
construction and do not establish network routing or universal refinement.
