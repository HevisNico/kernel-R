# Finite-chain proof construction

This continues the completed three-cell result in [PR #14](https://github.com/HevisNico/kernel-R/pull/14).
The existential every-N construction was reviewed in
[PR #15](https://github.com/HevisNico/kernel-R/pull/15), at head
`46c5672e0a5909d153c8130102cff5f25f276487`, and merged into `main`.
The universal-complete extension was reviewed in
[PR #17](https://github.com/HevisNico/kernel-R/pull/17), then merged into
`proof/physical-finite-chain`. This checkout integrates those universal proof
modules with the `main` README from PR #18. The proof sources retain the
published `f032e7f4dd07485945459236bd89e72748d6aec7` checkpoint; integration
CI and release publication are recorded separately.
The original staged A/B/C protocol remains a separate completed result:
A54/B61/C34 at789.9, with B/C born at160/480. The scalable protocol below
uses independently chosen cells all born at0; its source program and traffic
counts belong to that different construction.

The checkpoint identifiers in this introduction describe the historical
universal proof integration. The later geometric correspondence and its local
validation are recorded below; they do not change those published identities.

## Geometric crossings and finite-prefix progress

[CrossingChainHeadline](../proof/lean/KernelR/CrossingChainHeadline.lean) now exports
`every_finite_chain_every_crossing_execution` for the same birth, physical-box,
source, delay and prescribed-error budgets. It constructs a complete crossing
witness and transfers the endpoint, ordered per-cell FIRE lists, counts and
errors to every geometrically complete competing model execution.

`WeakFlow` allows READY charge ≤1. Model FIRE/MARK require both an actual
strictly-below left interval in the recorded history and a full-cell incoming-mode
ODE germ strictly above one on the right. Terminal completion excludes exactly
jumps meeting both conditions, without assuming native saturation or a positive
slope in the crossing definition. The transverse witness and strictly delayed
router are derived from the protocol. Every model completion refines to a complete
native history with exactly the same paths and jumps; the reverse direction gives
an observationally equal crossing representative with the same ordered FIRE lists.
See the [precise correspondence](MODEL_LEAN_CORRESPONDENCE.md#threshold-contacts-and-upward-crossings).

[HybridCrossingProgress](../proof/lean/KernelR/HybridCrossingProgress.lean) proves exact native
refinement of **every finite weak prefix**, at any finite date, and extends every
finite crossing history to any horizon at or after its endpoint while retaining
the original history. Maximal/infinite-run and non-Zeno statements retain the
native `InfiniteExecution` interface. This does not supply indefinitely repeatable
responding network operation.

## Every complete finite execution of the fixed program

[UniversalChainHeadline](../proof/lean/KernelR/UniversalChainHeadline.lean) now exports
`every_finite_chain_every_complete_execution`, `terminal_state_and_counts`
and `prescribed_errors_on_every_complete_execution`. The exact indexed order is

> For every admissible positive finite N, K, independent fixed fabrication and
> birth data, and bounded prescribed error family, there exist fixed native
> delay functions and a constructed complete witness, such that **every finite
> execution from the same initial state under that fixed router, complete at
> the declared T**, has the claimed physical endpoint, memories, counts and
> prescribed errors at its own actual fast-phase sending FIREs.

Existence is retained, so the universal class is nonempty. `CompleteThrough e T`
requires terminal date T, no enabled terminal jump and no token due by T still
pending. It is a condition on a supplied finite operational execution, not a
proof that a stopped prefix must progress, a maximal infinite run reaches T,
or Zeno behavior is impossible.

The generic [physical uniqueness theorem](../proof/lean/KernelR/HybridUniversalExecution.lean)
proves this observational comparison for any fixed finite network, parameter
family and router, with `PhysicalBox` and initial `PhysicalInvariant`:
complete executions through the same T have equal time, physical coordinates,
main/auxiliary modes and RAW state, pending queues related by permutation, and
**exactly equal ordered per-cell FIRE-date lists**. The global emission list is
compared up to permutation, allowing legal simultaneous interleavings. Neither
flow subdivision nor the syntactic order of independent instantaneous moves
is made unique. No event-priority, target calendar or determinism premise is
added to the protocol theorem.

[HybridUniversalBirthCadenceChain](../proof/lean/KernelR/HybridUniversalBirthCadenceChain.lean)
transfers these observations to the already constructed common-birth program.
For every competing complete trace, fast dates are its own full per-cell FIRE
list after `drop (finiteChainPreparationCount n i)`: **14 preparation FIREs at
the leaf, 12 at a relay**. The error index is zero-based on this suffix; wire j
still leaves physical cell `n-j`. The same chosen fixed native functions
realize the prescribed errors on every such trace. This does not move the
native-function choice outside the prescribed-error quantifier or assert
that every arbitrary router realizes a specified error sequence.

The three public headline axiom profiles contain only `propext`,
`Classical.choice` and `Quot.sound`. The [validation ledger](VALIDATION_LEDGER.md)
records the successful complete frozen-source build and global audit.
The reviewed universal proof modules are included in this checkout. The
[historical release checklist](RELEASE_UNIVERSAL_FINITE_CHAIN.md)
records the v0.2.0 integration and publication scope; later local validation is
recorded in the [current ledger](VALIDATION_LEDGER.md#validation-and-checkpoint-discipline).

## Constructed family and exact quantifiers

[IndexedChainHeadline](../proof/lean/KernelR/IndexedChainHeadline.lean) exposes
`every_finite_chain_exists`, backed by `indexed_birth_cadence_chain_exists` in
[HybridIndexedBirthCadenceChain](../proof/lean/KernelR/HybridIndexedBirthCadenceChain.lean).
It returns `ConstructedIndexedBirthCadenceChain` for every positive finite N. Lean uses `n=N-1`, cells `Fin (n+1)`, physical root0
and leaf `Fin.last n`. There is no tested maximum N.

Caller inputs are independent `BirthState`s with all auxiliaries initially
READY, independent fixed `PhysicalBox` parameters in either declared
fabrication family (±0.3% or ±10%), canonical pulse amplitudes, and exact
source queues. Each cell receives16 period-eight preparation inputs from0:
the leaf on port1 and all relays on port2. The leaf's K period-four port0
inputs, starting at160, are already in the global birth queue; `K ≥ 4*N+12`.
Preparation reaches159.9. The fixed contacts are closed before160 and open
on `[160,T+1)` for the fast phase, with

`T = 160 + 4*(K-1) + 1.1*(N-1) + 8`.

For each link j<N-1, a fixed centre d_j and nonnegative budget σ_j satisfy
`0.3+σ_j ≤ d_j ≤ 0.4-σ_j`. The caller prescribes an arbitrary error sequence
`error : ℕ → ℕ → ℝ`, with `-σ_j ≤ error j k ≤ σ_j` for every k and every
actual link j. The cumulative budget is `sum_{j<N-1} σ_j ≤ 0.15`; no
probabilistic independence is assumed.

The factory constructs fixed native delay functions δ_j(t), globally bounded
by `-σ_j ≤ δ_j(t)-d_j ≤ σ_j` at every time t, and the actual whole-chain
execution using those functions. For every kth fast-phase FIRE on wire j,
it proves `δ_j(F_jk)=d_j+error j k` on the **final global fast execution's**
ordered sender ledger. Wire j leaves physical cell `n-j`, represented by
`indexedCadenceSender n j`; its error index starts at0 in `chain.fastExecution`.
Preparation FIREs are excluded from this index, so the12 relay/14 leaf
preparation counts do not shift it. Every delay lies in[0.3,0.4].

The native universal factory `universal_birth_cadence_chain_exists` returns a
complete witness together with its `AllComplete` guarantee for every admissible
caller-supplied native delay family. The earlier
`birth_cadence_chain_exists` native-function API remains available:
it takes δ_j(t) with the same global bounds as caller inputs. The indexed
factory now closes the prescribed-sequence realization obligation by building
the chosen physical stage successively and preserving each actual sender
ledger through subsequent weaves. It retains that same chosen stage in the
birth wrapper. That existential construction itself does not invoke uniqueness;
the new universal layer subsequently compares every complete trace to its
already constructed witness.

The returned witness constructs the physical preparation and fast executions
under **one fixed gated router**, retaining their concatenated ledgers,
delivered occurrences and actual energy paths. No prepared state, reaching
execution, received calendar, desired output count or local `CellLaw` is a
factory premise. Receiver analysis queues are matched to real FIRE issuance
and arrivals; future wire tokens are not external birth sources.

## Derived conclusions

At T every cell is READY with q=0.1, no RAW and an empty pending queue; the
execution is `CompleteThrough T`, with the physical reserve/cap invariant and
raw validity. The active log-gain (leaf port0, relay port2) is its **own** birth
value+2.4 and recovery is its own birth value+0.3. Other gains retain the
values established by the actual preparation.

At leaf-to-root depth j=0,...,N-1, fast traffic is `K-5-2*j`, totaling
`N*(K-N-4)`. Preparation emits14 at the leaf and12 at each relay, totaling
`12*N+2`. The actual concatenated ledger therefore contains
`N*(K-N+8)+2` emissions. Physical root-first indices reverse the depth index:
cell i has depth `N-1-i`.

## Proof ledger

| Obligation | Constructed result | Boundary |
|---|---|---|
| Independent birth preparation | `HybridFiniteChainRelayPreparation`, `HybridFiniteChainLeafPreparation`, `HybridFiniteChainFamilyPreparation` | Declared common-time READY births and exact16-input queues |
| Variable-K physical leaf | `HybridBirthCadenceLeafK`, `HybridConstructedCadenceLeafK` | Actual weak/strong/MARK/mixed/high phases and exact ledger packet |
| Full cumulative jitter0.15 | `HybridLocalCadenceBudgetReceiver` and `HybridCadencePacketRelay` | High latencies[0.16,0.26] and first≤rest are directly proved; the older narrower `Chain.Refinement.RelayLaw` is not supplied |
| Finite causal assembly | `HybridPreparedCadenceChainConstruction`, `HybridFiniteCausalChain` | Each new receiver is physically constructed and causally woven; no local-law premise |
| Common router from birth | `HybridBirthCadenceChain` | Preparation retargeting preserves ledgers/deliveries because contacts are closed at its actual FIREs |
| Terminal state and counts | `HybridCadenceChainEnvelope`, `HybridCadenceChainCounts`, `ConstructedBirthCadenceChain` | Actual finite horizon, own memories, per-cell and cumulative traffic |
| Indexed per-emission errors | `HybridIndexedPreparedCadenceChain`, `HybridIndexedBirthCadenceChain`, `IndexedChainHeadline` | Arbitrary bounded prescribed sequences; generated fixed native functions realize every error on the final fast sender ledger; whole birth-to-terminal invariants retained |
| Probes, cuts and settings copies | Written results and finite evidence | Retained physical semantics and proofs remain open |
| Every complete finite execution | `HybridFlowUniqueness`, `HybridJumpLocalDiamond`, `HybridJumpStripping`, `HybridExecutionUniqueness`, `HybridUniversalExecution`, `HybridUniversalBirthCadenceChain`, `UniversalChainHeadline` | Physical endpoint and exact per-cell FIRE lists at fixed T under the same router; no imposed jump priority |
| Geometric model correspondence | `HybridCrossingExecution`, `HybridCellOrbitExistence`, `HybridWeakNativeRefinement`, `HybridCrossingCorrespondence`, `CrossingChainHeadline` | Exact model-to-native completion, unchanged physical inputs; native-to-model converse preserves observations and ordered FIRE lists |
| Finite weak/model progress | [HybridCrossingProgress](../proof/lean/KernelR/HybridCrossingProgress.lean) | Exact native refinement for every finite weak prefix and history-preserving crossing extension to every later finite horizon |
| Universal preparation extraction | `HybridUniversalChainPreparation` | Actual arbitrary-network prefixes through128 yield each relay/leaf preparation from source queues, with other-cell interleavings retained |
| Finite continuation | [HybridChainProgress](../proof/lean/KernelR/HybridChainProgress.lean) | Every legal finite prefix of the fixed finite-source program extends to a complete execution at any horizon at or after its endpoint |
| Physical-event non-Zeno | [HybridNonZeno](../proof/lean/KernelR/HybridNonZeno.lean) | Under the birth, physical-box and bounded-fanout hypotheses, infinitely many physical jumps force time divergence. The constructed chain supplies the fanout bound. |
| Maximal infinite-run progress | [HybridMaximalProgress](../proof/lean/KernelR/HybridMaximalProgress.lean) and [proof guide](../proof/lean/PROGRESS.md#semantic-extension-at-a-finite-flow-limit) | Infinite presentations maximal under extension at a flow limit progress beyond every finite horizon of the fixed finite-source program. Time can advance by quiet flow after source exhaustion. |
| Operational perturbations | Separate obligations | Drift, noise and amplitude histories remain open |

This closes constructive physical existence for the new common-birth family;
it does not establish all six conclusions of the written finite-chain theorem.
Broader introductions, ports or source programs retain their own obligations.
The [coverage guide](../proof/lean/N_CELL_COVERAGE.md) separates the older conditional API
from the new construction.

See the [validation ledger](VALIDATION_LEDGER.md) for checked revisions and reproduction records.
