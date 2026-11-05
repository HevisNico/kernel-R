# Universal finite-chain result and verification

[Repository overview](../README.md) · [Experiments and reproduction](EXPERIMENTS_AND_REPRODUCTION.md)

## Result: every finite chain, with explicit scope

All N cells are born at time 0 in independently chosen READY states. Routes
are closed during 16 direct period-eight preparation inputs per cell: the
leaf receives them on port 1, each relay on port 2. The leaf then receives
K period-four port 0 sources from 160, with **K≥4N+12**. These future sources
are present in the global queue from birth. Each source and wire is consumed
by an actual arrival; each routed token is issued by an actual FIRE.
Preparation and cadence share **one fixed gated router**, opening at 160.
Each non-root FIRE in the contact window [160,T+1) issues exactly one token
to its parent on port 2, due at F+δ_j(F); the root has no outgoing link.
The topology, destination, port and contact window are fixed by the protocol.
The [contact definition](../proof/lean/KernelR/HybridFiniteCadenceContact.lean)
and [chain assembly](../proof/lean/KernelR/HybridFiniteChainPreparedData.lean)
make these restrictions explicit.

| Derived quantity | Result |
|---|---|
| Terminal time T | `160 + 4*(K-1) + (11/10)*(N-1) + 8` |
| Fast emissions at depth j, leaf j=0 | `K-5-2*j` |
| Root fast emissions | `K-2*N-3` |
| Root regular tail | `K-4*N-4 >= 8` pulses; ideal period 4, phase-error amplitude at most the cumulative budget J |
| Total fast emissions | `N*(K-N-4)` |
| Total preparation emissions | `12*N+2` |
| Entire birth-to-T emission ledger | `N*(K-N+8)+2` |
| Each active log-gain, leaf port 0 / relays port 2 | Own birth value +2.4; four full exposed ERROR sections on that port of the constructed witness |
| Each recovery | Own birth value +0.3; three protected MARK sections summed over that cell's ports of the constructed witness |
| Endpoint | All READY/q=0.1, RAW absent, empty global queue |

[`ConstructedBirthCadenceChain.exact_section_counts`](../proof/lean/KernelR/HybridFiniteChainDoseCounting.lean)
constructs the witness's whole-execution covers under the original physical
hypotheses. Four is the ERROR count on the active port: the leaf has one
additional preparation ERROR on port1. Its three MARK sections split as one
on preparation port1 and two on active port0. The universal comparison of
complete traces transfers memories and FIRE dates; cover existence for
competing complete traces is not part of this count theorem.

For the regular tail, actual dates have the form `t_k = τ + 4*k + η_k`,
with `|η_k| <= J` and `J <= 0.15`. Successive intervals therefore lie in
`[4-2*J, 4+2*J]`; variable wire jitter is retained. A relay preserves the
phase budget, while wires add their declared budgets. The
[packet witness and calendar](../proof/lean/KernelR/HybridConstructedCadenceChainStage.lean)
identify this packet with actual root FIREs. Equality of the per-cell FIRE
lists transfers the same packet to every complete execution.

Other gains retain their physical preparation memories. The energy ODE,
reserve/cap invariants and actual raw-current origins are retained throughout.
Physical cell indices run root-first in Lean; the depth index in the table
runs leaf-first.

The 15 fabrication parameters per cell are chosen independently in either the
±0.3% or ±10% box and are **fixed in time**. Births have q=0.1±10⁻⁵,
b=0.08±10⁻⁵, energy in [50,100], each auxiliary READY with m=0.025±10⁻⁵,
no RAW, and log-gains within 10⁻⁵ of log(0.3), log(1.2), log(0.3) on ports 0/1/2.
Pulses have the declared canonical width-one exponential shape. Sources,
ports and contact windows are supplied protocol data.

For each link, a fixed centre d and budget σ satisfy
`0≤σ≤0.05` and `0.3+σ≤d≤0.4-σ`; the path sum is at most 0.15.
The native-delay theorem accepts any fixed functions δ_j(t) satisfying
`|δ_j(t)-d_j|≤σ_j` at **every real time**. They are inputs to the theorem;
no sending FIRE dates or output calendar are supplied.

As a separate indexed-error corollary, for every prescribed sequence e_j(k)
in [-σ_j,σ_j], the construction supplies
native functions δ_j(t) bounded at **every real time**, and proves
`δ_j(F_j,k)=d_j+e_j(k)` on the actual kth fast-phase sender FIRE in the final
global execution. Wire j leaves physical cell N−1−j. Indices are zero-based
and exclude the 12/14 preparation FIREs. Every wire delay lies in [0.3,0.4].
The [indexed delay definition](../proof/lean/KernelR/HybridIndexedWireDelay.lean)
uses the already constructed sender's actual FIRE list to realize these values.
The resulting function is fixed for the whole execution and bounded at all
real times. Its values away from actual FIREs need not be unique.
The indexed corollary does not take a native delay function, reaching execution
or output calendar as input. Neither formulation assumes statistical
independence or cancellation of wire errors. The universal
[native-delay theorem](../proof/lean/KernelR/HybridUniversalBirthCadenceChain.lean)
applies to every admissible supplied delay family; the indexed corollary
additionally realizes each prescribed bounded error sequence.

**Scope near the result:** the model theorem concerns every finite
`CrossingExecution` satisfying `CrossingCompleteThrough model T`, with the same
initial state, parameters, source queue and fixed router. The native comparison
uses `Execution` and `CompleteThrough e T`. Constructed witnesses supply both
classes. Positive flows cannot bypass events enabled by their respective semantics; legal
simultaneous event orders and flow subdivisions give the same physical
endpoint and exact ordered per-cell FIRE lists. The global simultaneous event
list and pending-list presentation may differ by permutation.

The native execution definitions use first threshold contact. The
[threshold correspondence](MODEL_LEAN_CORRESPONDENCE.md#threshold-contacts-and-upward-crossings)
now proves the bridge to geometric upward crossings on this protocol.
[`CrossingChainHeadline.every_finite_chain_every_crossing_execution`](../proof/lean/KernelR/CrossingChainHeadline.lean)
constructs a crossing witness and quantifies over every geometrically complete
model execution under the same static hypotheses. Its exact refinement retains
all paths and jumps; the endpoint, ordered FIRE dates, learning, counts and
prescribed wire errors follow from the native results.

This comparison assumes completeness through T. For the same fixed finite-source
program, the [progress theorems](../proof/lean/PROGRESS.md) extend every legal
finite prefix to any horizon at or after its endpoint, rule out infinitely
many physical jumps in bounded time, and prove time divergence for infinite
presentations maximal under extension at a flow limit. After source exhaustion,
time can progress by quiet flow.

In the indexed corollary, delay functions are constructed after the input/error
family is fixed. The native-delay theorem
instead accepts the delay functions fixed in advance. Neither formulation
asserts an online synthesis algorithm, continuity or one function uniform
across different families. Frozen
probes, cuts/settings copies, indefinite networks and operational noise/drift
retain their own obligations. See the [proof ledger](../proof/lean/EVERY_N_PLAN.md)
and [coverage map](../proof/lean/N_CELL_COVERAGE.md).

The earlier **staged three-cell protocol** remains proved from A's original
birth and independent B/C births at 160/480 through **789.9**, with
**A54/B61/C34**, all READY/q=0.1, no RAW and no pending tokens. Its
[original headline](../proof/lean/KernelR/Headline.lean) and
[checkpoint map](../proof/lean/HYBRID_EXECUTION.md#constructed-protocol-checkpoint)
remain available. The new common-time birth program has different preparation
and traffic; its N=3 instance is not the old staged protocol.

R's structural mechanism is two memories with complementary gates: ERROR
activity increases an input's log-gain while the main cell is READY; protected
MARK activity increases recovery while admission is closed. Gain changes the
response to future inputs; recovery changes the actual SLOW-to-READY return.
The constructed protocol uses both to acquire and transmit cadence. The
[kernel equations](../kernel/README.md) and
[model correspondence](../docs/MODEL_LEAN_CORRESPONDENCE.md) give their exact gates.

This work draws inspiration from Nicolas Breuillaud's
[*The Reset Operator: A Structural Constraint on Recursivity*](https://ssrn.com/abstract=6964960).
The paper's structural argument concerns saturation in regimes where recovery
can no longer keep pace with forcing.

The Lean theorem establishes the behavior of **the R model** for its declared
parameter families and admissible inputs. It verifies the learning and cadence
protocol in this setting; the paper's broader argument about saturation when
recovery is insufficient remains separate from what is proved here.

## Lean headline: signatures, axioms and reproduction

### Geometric upward-crossing entry point

The model-facing entry point is
[`CrossingChainHeadline.every_finite_chain_every_crossing_execution`](../proof/lean/KernelR/CrossingChainHeadline.lean)
in `KernelR.Hybrid.CrossingChainHeadline`. It constructs a complete execution
in the model's upward-crossing semantics and compares every complete crossing
execution from the same initial snapshot and fixed router. The theorem below
takes prescribed bounded per-emission errors and constructs fixed native delay
functions realizing them.

```lean
namespace KernelR.Hybrid.CrossingChainHeadline

theorem every_finite_chain_every_crossing_execution {n θ bornCells K ε}
    (hborn : ∀ i : Fin (n+1), BirthState (bornCells i))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q = .ready)
    (hqueue : ∀ i, (bornCells i).pending = sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ → ℝ) (error : ℕ → ℕ → ℝ)
    (hK : 4 * (n+1) + 12 ≤ K) (hsigma : ∀ j, 0 ≤ sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n ≤ 3/20)
    (hcentre : ∀ j, j < n → (3/10 : ℝ) + sigma j ≤ centre j ∧ centre j ≤ 2/5 - sigma j)
    (herror : ∀ j, j < n → ∀ i, -sigma j ≤ error j i ∧ error j i ≤ sigma j) :
    ∃ chain : ConstructedIndexedBirthCadenceChain θ bornCells K sigma centre error
        (cadenceChainTerminal n K),
      (∃ model : CrossingExecution θ chain.chain.router
          (familyPreparationBornSource bornCells K) chain.chain.final,
        CrossingCompleteThrough model (cadenceChainTerminal n K)) ∧
      chain.chain.AllCrossingComplete ∧ chain.AllCrossingCompleteErrors

end KernelR.Hybrid.CrossingChainHeadline
```

`AllCrossingComplete` quantifies over every `CrossingExecution` satisfying
`CrossingCompleteThrough model T` and gives the same physical endpoint and
ordered per-cell FIRE dates. `AllCrossingCompleteErrors` gives the prescribed
wire errors on those actual FIRE lists. The companion
`CrossingChainHeadline.terminal_state_and_counts` transfers the terminal
memories, recovery, FAST counts and total traffic to each model execution.

For delay functions supplied in advance, the native construction below produces
a `ConstructedBirthCadenceChain`. Its `crossingExecution` and
`every_crossing_complete` results in
[HybridCrossingCorrespondence](../proof/lean/KernelR/HybridCrossingCorrespondence.lean)
supply crossing existence and universal observations for that same fixed delay
family. This keeps the native-delay and indexed-error quantifier orders explicit.

#### Geometric headline axiom transcript

The source ends with `#print axioms every_finite_chain_every_crossing_execution`
and `#print axioms terminal_state_and_counts`. A verbatim compiler transcript
for these two geometric declarations is still to be recorded here. Capture
their actual output from this revision with the following commands from
`proof/lean`.

```sh
lake build KernelR.CrossingChainHeadline
lake env lean KernelR/CrossingChainHeadline.lean
```

The [validation ledger](../proof/lean/EVERY_N_PLAN.md#validation-and-checkpoint-discipline)
records a local build of 9,592 jobs and a global audit of 28,970 project
theorem declarations at `ef5a510`, the geometric-crossing checkpoint. That audit permits
only `propext`, `Classical.choice` and `Quot.sound`. The per-declaration compiler
transcript above remains a separate item to capture from a real build.

### Native first-contact proof steps

The native-delay proof entry point is
[`universal_birth_cadence_chain_exists`](../proof/lean/KernelR/HybridUniversalBirthCadenceChain.lean)
in `KernelR.Hybrid`. Its exact signature makes the delay functions explicit
inputs, before the existential physical witness:

```lean
namespace KernelR.Hybrid

theorem universal_birth_cadence_chain_exists {n θ bornCells K ε}
    (hborn : ∀ i : Fin (n+1), BirthState (bornCells i))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q=.ready)
    (hqueue : ∀ i, (bornCells i).pending=sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ → ℝ) (delay : ℕ → ℝ → ℝ)
    (hK : 4*(n+1)+12≤K) (hsigma : ∀ j, 0≤sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n≤3/20)
    (hcentre : ∀ j, j<n → (3/10:ℝ)+sigma j≤centre j ∧ centre j≤2/5-sigma j)
    (herror : ∀ j, j<n → ∀ time, -sigma j≤delay j time-centre j ∧ delay j time-centre j≤sigma j) :
    ∃ c : ConstructedBirthCadenceChain θ bornCells K sigma centre delay (cadenceChainTerminal n K),
      c.AllComplete

end KernelR.Hybrid
```

Its `#print axioms` output is:

```text
'KernelR.Hybrid.universal_birth_cadence_chain_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

[**UniversalChainHeadline.lean**](../proof/lean/KernelR/UniversalChainHeadline.lean)
groups the indexed-error corollary and its observations in
`KernelR.Hybrid.UniversalChainHeadline`:

| Declaration | Checked conclusion |
|---|---|
| `every_finite_chain_every_complete_execution` | A nonempty complete class and universal observations for every N=n+1 and prescribed error family |
| `terminal_state_and_counts` | The actual competing trace's endpoint, own memories, per-cell FAST/full traffic and total count |
| `prescribed_errors_on_every_complete_execution` | Exact prescribed errors on every complete trace's actual FAST sender list |

<details>
<summary>Exact Lean signatures and quantifiers</summary>

`AllComplete` quantifies over **all** finite operational executions from the
same birth queue under the chosen fixed router, with `CompleteThrough e T`.
It gives physical endpoint equality modulo queue permutation and exact ordered
FIRE dates per cell. `AllCompleteErrors` drops the physically proved 14 leaf /
12 relay preparation FIREs before applying zero-based fast emission indices.
Neither property is an input to the existence theorem.

```lean
namespace KernelR.Hybrid.UniversalChainHeadline

theorem every_finite_chain_every_complete_execution {n θ bornCells K ε}
    (hborn : ∀ i : Fin (n+1), BirthState (bornCells i))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ i q, (bornCells i).aux 0 q=.ready)
    (hqueue : ∀ i, (bornCells i).pending=sourceTrain 0 (finiteChainPreparationPort n i) 0 8 16)
    (sigma centre : ℕ→ℝ) (error : ℕ→ℕ→ℝ)
    (hK : 4*(n+1)+12≤K) (hsigma : ∀ j, 0≤sigma j)
    (hbudget : KernelR.Chain.pathJitter sigma n≤3/20)
    (hcentre : ∀ j, j<n → (3/10:ℝ)+sigma j≤centre j ∧ centre j≤2/5-sigma j)
    (herror : ∀ j, j<n → ∀ i, -sigma j≤error j i ∧ error j i≤sigma j) :
    ∃ c : ConstructedIndexedBirthCadenceChain θ bornCells K sigma centre error (cadenceChainTerminal n K),
      c.chain.AllComplete ∧ c.AllCompleteErrors

variable {n θ bornCells K sigma centre error T ε}
  (c : @ConstructedIndexedBirthCadenceChain n θ bornCells K sigma centre error T)

theorem terminal_state_and_counts (hb : PhysicalBox θ ε) {u : Snapshot (n+1)}
    (e : Execution θ c.chain.router (familyPreparationBornSource bornCells K) u)
    (hc : CompleteThrough e T) :
    UniversalCadenceOutcome θ bornCells K T u e.emissionTimes e.ledger.emissions.length

theorem prescribed_errors_on_every_complete_execution (hb : PhysicalBox θ ε) :
    c.AllCompleteErrors

end KernelR.Hybrid.UniversalChainHeadline
```

The [universal chain implementation](../proof/lean/KernelR/HybridUniversalBirthCadenceChain.lean)
also exports `universal_birth_cadence_chain_exists` for every admissible
caller-supplied native delay family. The [operational uniqueness theorem](../proof/lean/KernelR/HybridUniversalExecution.lean)
is proved from physical integral-flow uniqueness, confluence of all nine
jump constructors, and actual finite-trace comparison. No uniqueness, event
priority, `CellLaw`, output calendar or target phase is a caller premise.

</details>

The project pins **Lean 4.35.0** and **Mathlib v4.35.0**, with Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` in
[lake-manifest.json](../proof/lean/lake-manifest.json).
The universal proof was reviewed in [PR #17](https://github.com/HevisNico/kernel-R/pull/17).
The published source and its [workflow checks](https://github.com/HevisNico/kernel-R/pull/17/checks)
are pinned to `f032e7f4dd07485945459236bd89e72748d6aec7`.
The preceding indexed-existence checkpoint is
[550fc9509c8390a07fdb0cec02170a72cbc3071c](https://github.com/HevisNico/kernel-R/commit/550fc9509c8390a07fdb0cec02170a72cbc3071c),
reviewed in [PR #15](https://github.com/HevisNico/kernel-R/pull/15).
To check the integrated sources from the repository root with Lean installed:

```sh
git rev-parse HEAD
cd proof/lean
lake exe cache get
lake build KernelR.CrossingChainHeadline
lake build KernelR.HybridUniversalBirthCadenceChain
lake build KernelR.UniversalChainHeadline
lake build
lake build Audit
```

For the historical frozen checkpoint, first fetch and check out
`f032e7f4dd07485945459236bd89e72748d6aec7`, then run its native-module,
full-project and audit builds. The geometric crossing module belongs to the
current source revision. The three native indexed headline `#print axioms`
outputs recorded for the historical checkpoint are:

```text
'KernelR.Hybrid.UniversalChainHeadline.every_finite_chain_every_complete_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KernelR.Hybrid.UniversalChainHeadline.terminal_state_and_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KernelR.Hybrid.UniversalChainHeadline.prescribed_errors_on_every_complete_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

These are Lean's standard logical foundations. The source check rejects
admitted proofs and added project axioms; the global audit checks every
imported/current project theorem against this list.

| Universal proof checkpoint | Verified result |
|---|---|
| Complete frozen-source build | 9,557 build jobs |
| Global axiom audit | 27,741 project theorems |
| Source checks | 504 Lean files; five upstream modules unchanged |
| Generated evidence and robust replay | Match pinned inputs; 16 certificates replayed |
| Project tests | 12 pass |
| New universal paired controls | 20 pairs pass |
| Confirmed finite-chain controls | 218 passing pairs |
| Configured CI inventory | 1,321 pairs, plus axiom-audit corruption checks |

These figures describe verified proof-source commit
[eeff210df7a2c6297d532c10203312ded3c0bbf9](https://github.com/HevisNico/kernel-R/commit/eeff210df7a2c6297d532c10203312ded3c0bbf9).
Published follow-up `f032e7f4dd07485945459236bd89e72748d6aec7` records the
validation and removes one trailing source-space, with no proof change. Its
three standard workflows passed: [Lean](https://github.com/HevisNico/kernel-R/actions/runs/41379429073),
[research](https://github.com/HevisNico/kernel-R/actions/runs/41379429036) and
[robust evidence](https://github.com/HevisNico/kernel-R/actions/runs/41379429046).
The inventory totals do not claim a fresh local rerun of every historical
suite. The [validation ledger](../proof/lean/EVERY_N_PLAN.md) distinguishes the
universal checkpoint from the earlier indexed-existence result.
The [full reproduction commands](../proof/lean/README.md#reproduce) include source,
evidence and paired corruption controls. The badge at the top follows `main`;
the source-specific checks are linked above.

This work is done with two AI assistants, **Claude** (Anthropic) and **ChatGPT** (OpenAI), under the direction of Nicolas Breuillaud.

AI assists construction of models, code, proofs and documentation. Lean checks
the resulting proof terms against their definitions and hypotheses. That check
does not experimentally validate the physical assumptions or establish every
claim made in the repository.

## Model ↔ Lean: equations, events and assumptions

The [**one-page correspondence**](../docs/MODEL_LEAN_CORRESPONDENCE.md) maps main
and auxiliary charges, gain/recovery learning, energy/work, pulses, thresholds,
jumps, caps, fixed parameters and birth families to actual Lean definitions.
The [kernel guide](../kernel/README.md) explains the cell; the
[archived model](../model/full_model_reference.md) preserves its original network
context. A22 topology and simulations remain supporting material below.

