# kernel-R

[![Lean proof checks](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml/badge.svg)](https://github.com/HevisNico/kernel-R/actions/workflows/lean.yml)

**Lean verifies pulse-driven learning and cadence transmission from birth for
every finite directed chain of R cells, under the declared protocol.**

> **For every positive finite N, admissible K, independent fixed fabrication
> and READY birth data, and every prescribed bounded per-emission error
> sequence, there exist fixed native routing functions and a complete physical
> execution. Every finite execution from those same birth data, complete through
> the same horizon under that fixed router, has the same physical endpoint and
> ordered FIRE dates per cell, realizing the prescribed errors.**

Each cell's active gain becomes its own birth gain multiplied by exp(2.4),
and recovery increases by 0.3. The root transmits a regular period-four tail
with a bounded phase error. Every complete execution under the constructed
fixed router has the same terminal physical state and ordered FIRE dates per
cell. Existence is constructed separately, so this universal class is nonempty.

The [published proof snapshot](https://github.com/HevisNico/kernel-R/commit/f032e7f4dd07485945459236bd89e72748d6aec7)
contains the strengthened theorem. Proof links below are pinned to that
snapshot; the reproduction commands explicitly check out its sources.

1. [Result: every finite chain, with explicit scope](#result-every-finite-chain-with-explicit-scope)
2. [Lean headline: signatures, axioms and reproduction](#lean-headline-signatures-axioms-and-reproduction)
3. [Model ↔ Lean: equations, events and assumptions](#model--lean-equations-events-and-assumptions)

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
The [contact definition](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/KernelR/HybridFiniteCadenceContact.lean)
and [chain assembly](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/KernelR/HybridFiniteChainPreparedData.lean)
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
| Each active log-gain, leaf port 0 / relays port 2 | Own birth value +2.4 |
| Each recovery | Own birth value +0.3 |
| Endpoint | All READY/q=0.1, RAW absent, empty global queue |

For the regular tail, actual dates have the form `t_k = τ + 4*k + η_k`,
with `|η_k| <= J` and `J <= 0.15`. Successive intervals therefore lie in
`[4-2*J, 4+2*J]`; variable wire jitter is retained. A relay preserves the
phase budget, while wires add their declared budgets. The
[packet witness and calendar](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/KernelR/HybridConstructedCadenceChainStage.lean)
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
For every prescribed sequence e_j(k) in [-σ_j,σ_j], the theorem constructs
native functions δ_j(t) bounded at **every real time**, and proves
`δ_j(F_j,k)=d_j+e_j(k)` on the actual kth fast-phase sender FIRE in the final
global execution. Wire j leaves physical cell N−1−j. Indices are zero-based
and exclude the 12/14 preparation FIREs. Every wire delay lies in [0.3,0.4].
The [indexed delay definition](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/KernelR/HybridIndexedWireDelay.lean)
uses the already constructed sender's actual FIRE list to realize these values.
The resulting function is fixed for the whole execution and bounded at all
real times. Its values away from actual FIREs need not be unique.
No statistical independence, cancellation, native delay function, reaching
execution or output calendar is supplied by the caller. The earlier
[native-function theorem](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/KernelR/FiniteChainHeadline.lean) remains
available as a separate API.

**Scope near the result:** the universal theorem concerns every finite
`Execution` satisfying `CompleteThrough e T`, with the same initial state,
parameters, source queue and fixed router. The constructed witness proves that
this class is nonempty. Positive flows cannot bypass an enabled event; legal
simultaneous event orders and flow subdivisions give the same physical
endpoint and exact ordered per-cell FIRE lists. The global simultaneous event
list and pending-list presentation may differ by permutation.

This is a theorem about executions complete through T. It does not establish
that every stopped prefix extends to T, or maximal/infinite-run progress or
a non-Zeno extension theorem. Routing functions are chosen after the
input/error family is fixed; no online algorithm,
continuity or function uniform across different families is asserted. Frozen
probes, cuts/settings copies, indefinite networks and operational noise/drift
retain their own obligations. See the [proof ledger](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/EVERY_N_PLAN.md)
and [coverage map](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/N_CELL_COVERAGE.md).

The earlier **staged three-cell protocol** remains proved from A's original
birth and independent B/C births at 160/480 through **789.9**, with
**A54/B61/C34**, all READY/q=0.1, no RAW and no pending tokens. Its
[original headline](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/KernelR/Headline.lean) and
[checkpoint map](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/HYBRID_EXECUTION.md#constructed-protocol-checkpoint)
remain available. The new common-time birth program has different preparation
and traffic; its N=3 instance is not the old staged protocol.

R's structural mechanism is two memories with complementary gates: ERROR
activity increases an input's log-gain while the main cell is READY; protected
MARK activity increases recovery while admission is closed. Gain changes the
response to future inputs; recovery changes the actual SLOW-to-READY return.
The constructed protocol uses both to acquire and transmit cadence. The
[kernel equations](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/kernel/README.md) and
[model correspondence](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/docs/MODEL_LEAN_CORRESPONDENCE.md) give their exact gates.

This work draws inspiration from Nicolas Breuillaud's
[*The Reset Operator: A Structural Constraint on Recursivity*](https://ssrn.com/abstract=6964960).
The paper's structural argument concerns saturation in regimes where recovery
can no longer keep pace with forcing.

The Lean theorem establishes the behavior of **the R model** for its declared
parameter families and admissible inputs. It verifies the learning and cadence
protocol in this setting; the paper's broader argument about saturation when
recovery is insufficient remains separate from what is proved here.

## Lean headline: signatures, axioms and reproduction

[**UniversalChainHeadline.lean**](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/KernelR/UniversalChainHeadline.lean)
groups three checked statements in `KernelR.Hybrid.UniversalChainHeadline`:

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

The [universal chain implementation](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/KernelR/HybridUniversalBirthCadenceChain.lean)
also exports `universal_birth_cadence_chain_exists` for every admissible
caller-supplied native delay family. The [operational uniqueness theorem](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/KernelR/HybridUniversalExecution.lean)
is proved from physical integral-flow uniqueness, confluence of all nine
jump constructors, and actual finite-trace comparison. No uniqueness, event
priority, `CellLaw`, output calendar or target phase is a caller premise.

</details>

The project pins **Lean 4.35.0** and **Mathlib v4.35.0**, with Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` in
[lake-manifest.json](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/lake-manifest.json).
The universal proof was reviewed in [PR #17](https://github.com/HevisNico/kernel-R/pull/17).
The published source and its [workflow checks](https://github.com/HevisNico/kernel-R/pull/17/checks)
are pinned to `f032e7f4dd07485945459236bd89e72748d6aec7`.
The preceding indexed-existence checkpoint is
[550fc9509c8390a07fdb0cec02170a72cbc3071c](https://github.com/HevisNico/kernel-R/commit/550fc9509c8390a07fdb0cec02170a72cbc3071c),
reviewed in [PR #15](https://github.com/HevisNico/kernel-R/pull/15).
To reproduce the published universal proof from the repository root with Lean installed:

```sh
git fetch origin f032e7f4dd07485945459236bd89e72748d6aec7
git checkout --detach f032e7f4dd07485945459236bd89e72748d6aec7
cd proof/lean
lake exe cache get
lake build KernelR.UniversalChainHeadline
lake build
lake build Audit
```

The three `#print axioms` outputs are:

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
suite. The [validation ledger](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/EVERY_N_PLAN.md) distinguishes the
universal checkpoint from the earlier indexed-existence result.
The [full reproduction commands](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/README.md#reproduce) include source,
evidence and paired corruption controls. The badge at the top follows `main`;
the source-specific checks are linked above.

This work is done with two AI assistants, **Claude** (Anthropic) and **ChatGPT** (OpenAI), under the direction of Nicolas Breuillaud.

AI assists construction of models, code, proofs and documentation. Lean checks
the resulting proof terms against their definitions and hypotheses. That check
does not experimentally validate the physical assumptions or establish every
claim made in the repository.

## Model ↔ Lean: equations, events and assumptions

The [**one-page correspondence**](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/docs/MODEL_LEAN_CORRESPONDENCE.md) maps main
and auxiliary charges, gain/recovery learning, energy/work, pulses, thresholds,
jumps, caps, fixed parameters and birth families to actual Lean definitions.
The [kernel guide](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/kernel/README.md) explains the cell; the
[archived model](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/model/full_model_reference.md) preserves its original network
context. A22 topology and simulations remain supporting material below.

<details>
<summary>Supporting results, experiments, reproduction and provenance</summary>

### Guides and experiments

- [N-cell composition theorem](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/reciprocal_composition/THEOREM.md): every finite chain, with source-length and path-jitter budgets.
- [Robust slow chains](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/research/robust/README.md): drift, bounded charge noise and pulse-amplitude variation, from birth; Lean scope in [robust coverage](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/ROBUST_COVERAGE.md).
- [R kernel definition](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/kernel/README.md) and [original model](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/model/full_model_reference.md).
- [Cadence cascade proof](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/reciprocal_cadence/THEOREM.md): C's faster cadence reaches A through B, from birth through time 789.9.
- [Birth-to-feedback proof](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/reciprocal_entry/THEOREM.md): pulses-only initialization through time 459.9.
- [Prepared-section theorem](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/reciprocal_learning/THEOREM.md): the local A-learns-from-B effect.
- [Lean proof project](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/README.md): constructed physical executions, conditional protocol theorems, certificate endpoint checks and finite adaptive-policy replay, with explicit coverage limits.
- [Reciprocal prototype](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/experiments/reciprocal/README.md): cells remain alive and learn back from their students.
- [Learned teaching choice](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/experiments/reciprocal/pedagogy/README.md) and [within-lesson adaptation](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/experiments/reciprocal/adaptive/README.md).
- [Complete English prototype ZIP](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/downloads/R_Reciprocal_Prototype.zip): runnable code, recordings, reports and proofs in titled folders.

Extract the ZIP and open `12_Certified_N_Cell_Composition/RESULTS.html` for the latest
proof, or `03_Visualization/OPEN_IN_BROWSER.html` for the recorded three-cell
network. The viewer replays simulations rather than solving the equations.

### Results and scope

| Work | Evidence and boundary |
|---|---|
| Reciprocal R | Numerical three-cell network; parents remain alive and relearn from peer pulses. Schedules and settings copies are supplied. |
| Teaching efficacy | Actual and reversed feedback both improve transmission; that alone does not establish learned pedagogy. |
| Curriculum selection | Native R gains store a teaching choice in an added diagnostic/feedback/readout architecture. |
| Within-lesson adaptation | A learned stopping policy improves on fixed durations; a programmed equivalent rule matches it. |
| Local feedback theorem | ±0.3% and ±10% physical boxes, from a prepared section. |
| Entry and composed theorem | The declared READY birth family reaches that section; pulses-only protocol through time 459.9. |
| Cadence cascade theorem | From birth through 789.9, on 45-parameter boxes: C->B->A; b gains 0.2 in each cell's fast stage; A's frozen period-4 probe improves 4/8 to 8/8. |
| N-cell composition theorem | Every finite directed chain, 15*N independent physical parameters: K>=4*N+12 and summed link-jitter budgets <=0.15. Fixed link delays allow arbitrary depth. |
| Robust slow chains (research) | Prepared or birth-entered slow chains under measurable drift inside ±0.3% or ±10%, charge noise \|w\|<=nu and received-amplitude factor in [1-alpha,1+alpha]: K>=3*N+1, T>=7.5+2*sum(delta_i+sigma_i). Eight certified (epsilon,nu,alpha) points, and closed ranges such as every nu in [0,0.002] ([ranges](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/research/robust/ranges/README.md)); delta=0 without noise or amplitude variation. Written proofs and integer-replayed certificates; the Lean chain induction is conditional on each cell's `CellLaw` and covers timing and counts only. |

The composed proof starts with b near 0.08, establishes one protected full MARK
in each cell, and reaches b near 0.18 at time 319.9. It then proves
`g_A,after = g_A,birth * exp(1.8)` on A's feedback port, with an isolated retained
probe changing from 0/8 to 8/8. The box contains all 30 original per-port physical
parameters of A and B independently.

The cadence extension reaches 789.9, including C's introduction, 20/18/16 fast
emissions in C/B/A and two full recovery MARK doses in each. It covers all 45
per-port physical parameters independently, with per-pulse wire jitter in [0.3,0.4].
The [cadence results](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/results/reciprocal_cadence/README.md) include retained probes
and causal cuts: without either reverse link, A remains at 4/8.

These ±10% prefix results do not certify the older entire A22 network at ±10%,
the settings-copy variant, open recurrence after 800 or adaptive pedagogy.
The written results include retained probes and causal cuts beyond the Lean
protocol statements above. Those full written statements combine hybrid-flow
arguments with interval checks; their additional conclusions are not all
formalized in Lean, and no independent peer review is claimed.

The [Lean project](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/README.md) proves physical flow, reserve and memory
invariants, the common-birth finite-chain construction and complete-execution
comparison above, the earlier staged N=3 protocol, and generic conditional results. It also checks exact rational certificate endpoints and
recorded cadence/adaptive counters. These evidence checks do not establish
membership of the actual trajectories in every recorded interval. Both finite-chain factories now also prove the same physical result for
every complete finite execution under their fixed router. Retained probes
and indefinite network continuation remain separate obligations.

The [N-cell extension](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/results/reciprocal_composition/README.md) uses a closed
packet contract and a written induction, supported by 81 N-independent local
inequalities and 12 exact polynomial identities. Physical tolerances stay at
±10% as N grows. Source length and time grow linearly; fast-block traffic is
quadratic at the supplied minimum source length. Per-pulse wire jitter must
obey the path budget; the old 25-pulse train and full ±0.05 jitter per link
are not claimed to work unchanged at arbitrary depth.

### Replay the written certificates

Python 3.12 and its standard library suffice; no numerical packages or network
access are required.

Dependency replay runs only authenticated source snapshots in a temporary
directory, with isolated Python startup. Unlisted modules, packages and caches
in a supplied dependency directory cannot join that snapshot.

```sh
python -B -m unittest discover -s tests
python -B certify/reciprocal_learning/tests.py
python -B certify/reciprocal_entry/tests.py --link-code certify/reciprocal_learning --link-003 results/reciprocal_learning/eps3e-3/certificate.json --link-01 results/reciprocal_learning/eps1e-1/certificate.json
python -B certify/reciprocal_entry/verify.py results/reciprocal_entry/eps1e-1/certificate.json --link-certificate results/reciprocal_learning/eps1e-1/certificate.json --link-code certify/reciprocal_learning
python -B certify/reciprocal_cadence/tests.py
python -B certify/reciprocal_composition/tests.py
```

The standalone certificate suites cover 14 local-theorem, 16 entry/composition,
18 cadence and 21 N-composition tests; the project regression suite is run
separately above. The cadence
checker replays 95 actual input cases, 1,030 strict obligations and 2,533 enclosures
for each physical box, and rechecks the authenticated earlier theorems.
The entry checker
verifies 59 obligations and 170 enclosures, then rechecks the pinned local theorem's
31 obligations and 103 enclosures. The two arithmetic implementations are outward
Decimal intervals and integer fixed point with explicit exp/ln series tails.

### Restore recordings or run a fresh experiment

The recorded data are kept once in the ZIP instead of duplicating dozens of
large JSON files in the source tree. Restore them with their SHA-256 checks:

```sh
python -B tools/prepare_recordings.py
```

This creates ignored `audit_runs/` inputs. Existing different local outputs are
never overwritten. The full records remain directly inspectable inside the ZIP.
To run a fresh network:

```sh
python -m pip install -r requirements.txt
python -u -B experiments/reciprocal/simulate.py --out audit_runs/new_reciprocal
python -u -B experiments/reciprocal/analyse.py --out audit_runs/new_reciprocal
python -u -B experiments/reciprocal/validate.py --out audit_runs/new_reciprocal
```

NumPy 2.3.5 and SciPy 1.17.0 are pinned. Use a new output directory for each run.
The individual experiment guides provide further teaching and adaptation commands.
New adaptive plans lock both simulation engines and the numerical runtime;
legacy two-file plans are rejected by the updated validators. See the
[adaptive reproduction notes](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/experiments/reciprocal/adaptive/README.md#reproduce).
The bundled adaptive records have been recomputed on the original seeds with
that complete manifest. All 127 experiment checks and continuous teacher replay
pass; legacy adaptive development and aborted-run records have been removed.

After installing the numerical requirements, run the terminal-event and
provenance regressions with:

```sh
python -B -m unittest discover -s experiments/reciprocal/tests -v
```

### Rebuild the ZIP

```sh
python -B tools/prepare_recordings.py
python -B experiments/reciprocal/package.py
```

The output is `dist/R_Reciprocal_Prototype.zip`, constrained below 30,000,000 bytes.
The provided download is a pinned research snapshot; rebuilding an archive need
not preserve ZIP timestamps, while its source/data manifest remains verifiable.

Optional viewer QA uses Node.js: `npm install`, then `npm run check:viewer`.
`npm run check:browser` additionally needs an installed Playwright Chromium binary.
The original reports distinguish DOM/SVG checks from unavailable full-browser tests.

### Where the robust results live

The robust results are in `research/robust/`, not in `certify/`, `proof/` and `results/`.
They originate in a tested offline package. The numerical sources, certificates and
traces retain their identities; the current guide and its documented provenance
updates adapt that snapshot to this repository. Their protocol is a different, slow-input chain: it is not the fast period-4
packet protocol of the N-cell composition theorem. Their status is that of the other
written theorems: hybrid arguments written by hand, finite inequalities replayed in
independent integer arithmetic, and, in Lean, the chain induction and the certificate
endpoints. Proving each cell's `CellLaw` from the hybrid execution is the open step
([plan](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/proof/lean/CELLLAW_PLAN.md)).

### Reference boundary and limitations

The [kernel guide](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/kernel/README.md) describes R as a cell and links the current
three-cell and chain protocols. The `model/` snapshots and
[archived A22 kernel guide](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/kernel/reference/A22_KERNEL_README.txt) preserve the
original reference context. `kernel/KERNEL_SHA256SUMS` identifies upstream engine
files; those engines are not vendored here. See [provenance](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/docs/PROVENANCE.md).

General pedagogy, semantic memory, new waveform invention and chip energy/area
benefits remain unproved. Observation bins, feedback coding, lesson primitives
and copying rules are supplied components unless explicitly learned in a test.
R's monotone parameters impose saturation and forgetting limits. The
[proposed invention protocol](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/experiments/reciprocal/adaptive/INVENTION_PROTOCOL.md)
is a future experiment, not a completed result.

</details>

Source code is [MIT](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/LICENSE). Documents, proofs, data, certificates and other
non-code material are CC BY 4.0 under [LICENSE-docs.md](https://github.com/HevisNico/kernel-R/blob/f032e7f4dd07485945459236bd89e72748d6aec7/LICENSE-docs.md).
