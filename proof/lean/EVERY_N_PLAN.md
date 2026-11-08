# Physical finite-chain proof: construction and checkpoints

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

[CrossingChainHeadline](KernelR/CrossingChainHeadline.lean) now exports
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
See the [precise correspondence](../../docs/MODEL_LEAN_CORRESPONDENCE.md#threshold-contacts-and-upward-crossings).

[HybridCrossingProgress](KernelR/HybridCrossingProgress.lean) proves exact native
refinement of **every finite weak prefix**, at any finite date, and extends every
finite crossing history to any horizon at or after its endpoint while retaining
the original history. Maximal/infinite-run and non-Zeno statements retain the
native `InfiniteExecution` interface. This does not supply indefinitely repeatable
responding network operation.

## Every complete finite execution of the fixed program

[UniversalChainHeadline](KernelR/UniversalChainHeadline.lean) now exports
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

The generic [physical uniqueness theorem](KernelR/HybridUniversalExecution.lean)
proves this observational comparison for any fixed finite network, parameter
family and router, with `PhysicalBox` and initial `PhysicalInvariant`:
complete executions through the same T have equal time, physical coordinates,
main/auxiliary modes and RAW state, pending queues related by permutation, and
**exactly equal ordered per-cell FIRE-date lists**. The global emission list is
compared up to permutation, allowing legal simultaneous interleavings. Neither
flow subdivision nor the syntactic order of independent instantaneous moves
is made unique. No event-priority, target calendar or determinism premise is
added to the protocol theorem.

[HybridUniversalBirthCadenceChain](KernelR/HybridUniversalBirthCadenceChain.lean)
transfers these observations to the already constructed common-birth program.
For every competing complete trace, fast dates are its own full per-cell FIRE
list after `drop (finiteChainPreparationCount n i)`: **14 preparation FIREs at
the leaf, 12 at a relay**. The error index is zero-based on this suffix; wire j
still leaves physical cell `n-j`. The same chosen fixed native functions
realize the prescribed errors on every such trace. This does not move the
native-function choice outside the prescribed-error quantifier or assert
that every arbitrary router realizes a specified error sequence.

The three public headline axiom profiles contain only `propext`,
`Classical.choice` and `Quot.sound`. The [validation ledger](EVERY_N_PLAN.md)
records the successful complete frozen-source build and global audit.
The reviewed universal proof modules are included in this checkout. The
[historical release checklist](../../docs/RELEASE_UNIVERSAL_FINITE_CHAIN.md)
records the v0.2.0 integration and publication scope; later local validation is
recorded in the [current ledger](EVERY_N_PLAN.md#validation-and-checkpoint-discipline).

## Constructed family and exact quantifiers

[IndexedChainHeadline](KernelR/IndexedChainHeadline.lean) exposes
`every_finite_chain_exists`, backed by `indexed_birth_cadence_chain_exists` in
[HybridIndexedBirthCadenceChain](KernelR/HybridIndexedBirthCadenceChain.lean).
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
| Finite weak/model progress | [HybridCrossingProgress](KernelR/HybridCrossingProgress.lean) | Exact native refinement for every finite weak prefix and history-preserving crossing extension to every later finite horizon |
| Universal preparation extraction | `HybridUniversalChainPreparation` | Actual arbitrary-network prefixes through128 yield each relay/leaf preparation from source queues, with other-cell interleavings retained |
| Finite continuation | [HybridChainProgress](KernelR/HybridChainProgress.lean) | Every legal finite prefix of the fixed finite-source program extends to a complete execution at any horizon at or after its endpoint |
| Physical-event non-Zeno | [HybridNonZeno](KernelR/HybridNonZeno.lean) | Under the birth, physical-box and bounded-fanout hypotheses, infinitely many physical jumps force time divergence. The constructed chain supplies the fanout bound. |
| Maximal infinite-run progress | [HybridMaximalProgress](KernelR/HybridMaximalProgress.lean) and [proof guide](PROGRESS.md#semantic-extension-at-a-finite-flow-limit) | Infinite presentations maximal under extension at a flow limit progress beyond every finite horizon of the fixed finite-source program. Time can advance by quiet flow after source exhaustion. |
| Operational perturbations | Separate obligations | Drift, noise and amplitude histories remain open |

This closes constructive physical existence for the new common-birth family;
it does not establish all six conclusions of the written finite-chain theorem.
Broader introductions, ports or source programs retain their own obligations.
The [coverage guide](N_CELL_COVERAGE.md) separates the older conditional API
from the new construction.

## Validation and checkpoint discipline

### Memory saturation local validation

The separate [port-memory saturation result](../../docs/GAIN_MEMORY_SATURATION.md)
adds native, weak and direct upward-crossing theorems without changing the
existing dynamics, guards, physical box, chain protocol or trusted headline.
The actual section cover permits cap closure and retains complete ERROR
entry/exit boundaries, READY exposure and positive energy.

Code checkpoint: `2f4d268d7842d53ce8da87af73c7491c02340ca2`, based on main
`0f39642`. Observed local checks on 6 November 2026:

- `lake build KernelR.HybridMemorySaturation KernelR.HybridCrossingMemorySaturation`
  passed; the crossing target used 3,550 dependency/build jobs. This is a
  targeted cached-dependency build, not the project-wide validation total.
- An earlier scoped `MemorySaturationAudit.lean` checkpoint passed for 1,966
  imported project theorem declarations. The final global measurement below
  includes the later stationary witness and is the current integration total.
- Source checks passed for 574 Lean files and the five inherited module
  identities. The frozen source-boundary check passed with only the exact
  new modules and root import added to its allowlist; its old base remains
  unchanged.

The full default local `lake build` passed with 9,626 jobs, including the
unchanged global `Audit` target: 29,425 project theorem declarations, using
only `propext`, `Classical.choice` and `Quot.sound`. All twelve paired
controls passed on the final code, including weak/crossing transfer and the
positive-duration at-cap witness; infrastructure timeouts are not accepted
as semantic rejections. Dependency caches were reused.

A fresh checked Lean export retained the same 84 trusted semantic declarations.
The source-hash record and reading list were regenerated for this checkpoint,
and the authenticated document check passed. These observations do not assert
a fresh external-dependency rebuild, rerun of every historical control, or a
complete green CI run. The stationary positive-duration witness begins at cap; no
cap-reaching section from a subcap protocol birth is claimed.

### Zero-recovery milestone local validation

The [zero-recovery result](../../docs/RESET_ZERO_RECOVERY.md) is a separate
arbitrary-network obstruction, not a new finite-chain hypothesis or a general
Reset Operator theorem. `HybridZeroRecovery` proves native locked snapshots,
paths and no firing from SLOW/q=1/4/b=0 with no MARK flow on the selected cell.
`HybridZeroRecoveryCrossing` proves the corresponding weak and model crossing
statements directly, retaining that explicit no-MARK premise. The quiet-sensor
input-based corollary is native. A fully exposed isolated MARK repairs b=0 to
0.1; actual complete locked native and crossing witnesses of arbitrary
positive duration are constructed within the current physical bounds.

Code checkpoint: `d8f55708230082d3499ad0d06b62ee90f608f265`, based on main
`0f39642`. Observed local checks on 6 November 2026:

| Measurement | Recorded result and scope |
|---|---|
| Targeted build | The two new modules passed with 3,560 dependency/build jobs under Lean 4.35.0 and the pinned dependencies. This is not a fresh full-project rebuild. |
| Scoped axiom audit | `ZeroRecoveryAudit.lean` passed for 1,996 project theorem declarations in the imported closure, allowing only `propext`, `Classical.choice`, `Quot.sound`. This is not the count of new theorems or a global audit total. |
| New contracts | The modules declare 19 explicit public theorems. Their printed headline axiom profiles use only the three allowed axioms. |
| Paired controls | All 20 pairs passed: one for each new public theorem plus retention of the no-MARK hypothesis. Every original compiled before its altered version was individually rejected; parser and import failures are not accepted substitutes. |
| Non-vacuity | Actual complete locked native and crossing executions are constructed through every later finite horizon; the state is physically admissible for either fabrication box, but is not a nominal birth state. |

The full default local `lake build` subsequently passed with 9,626 jobs,
including the unchanged global `Audit` target: 29,377 project theorem declarations
with only the same three permitted axioms. Dependency caches were reused;
this is not a fresh external-dependency rebuild or a rerun of every historical
control. Completed remote CI is not claimed.

The original source-boundary base and byte-identity checks remain unchanged;
only the two exact new modules, dedicated audit file and added root import
are whitelisted. A fresh checked Lean export retained the same 84 trusted
semantic declarations. The source-hash record and reading list were
regenerated for the code checkpoint and their authenticated check passed.

### Trusted headline: fixed code checkpoint and final-head CI record

The initial mathematical and verification source checkpoint is
[`e7212249c339fdf282423912244d37c6925c0cd6`](https://github.com/HevisNico/kernel-R/tree/e7212249c339fdf282423912244d37c6925c0cd6).
The measurements below retain that initial scope and checkpoint. The generated
[trusted-base guide](../../docs/TRUSTED_BASE.md) authenticates the current
verification checkpoint, including the auxiliary-attribution follow-up below.

| Measurement | Recorded result and scope |
|---|---|
| Local targeted build | `lake build KernelR.TrustedBase` passed with 3,790 dependency/build jobs. This is a targeted build including imported libraries, not a full-project local build or a source-file count. |
| Scoped local axiom audit | The unchanged `Audit.lean` scanner, importing `KernelR.TrustedBase` instead of the full root, checked 7,050 project theorems in that dependency closure. Only `propext`, `Classical.choice`, `Quot.sound` were permitted. This is not the global CI theorem total. |
| Local trusted statement check | The explicit allowlist contains 84 semantic parent declarations. The checked closure contains no construction structures; attributed compiler auxiliaries are traversed rather than treated as opaque leaves. |
| Local new paired controls | All 19 pairs passed: nine router/headline pairs and ten trusted-checker pairs. These are distinct accepted-original/rejected-mutation cases, not compiler-process counts or a total of the historical suites. |
| Local source hygiene | `check_sources.py` checked 571 project Lean files and the five inherited module identities. `check_trusted_source_boundary.py` authenticated every existing Lean file against base `17928f25086bd8e1765dee1fbf6acce8ebc1b673`; only the declared new modules and added root imports are allowed. |
| Local metadata freshness | A fresh checked Lean export matched the CI-produced declaration names, ranges and auxiliary attribution exactly. The renderer authenticates its fixed source snapshot and every written-model heading. |

The final-head CI record is generated by
[`trusted_validation_report.py`](scripts/trusted_validation_report.py) only
after the complete regression sequence succeeds. The workflow preserves it
as `trusted-base-validation-<head-commit>`, including `validation.json`, the
captured full-target build log and global audit log. The JSON separately
records the exact PR `head_commit` and tested merge `build_commit`, CI build
jobs, globally audited theorems, project Lean files and new paired controls.
The PR description links that final record and its observed CI result.

A commit cannot contain its own hash in its checked-in ledger. The generated
CI record supplies the exact final-head reference; the static figures above
retain their fixed code checkpoint and local/scoped labels. They do not
claim that a still-running CI suite has completed. Mathematical human review
follows the [trusted reading path](../../REVIEW.md); proofs are checked by Lean.

### Source-declared helper attribution

Verification checkpoint
[`789620b75fe40f983ae2a8a1944796067a157e0c`](https://github.com/HevisNico/kernel-R/tree/789620b75fe40f983ae2a8a1944796067a157e0c)
strengthens the checker without changing the mathematical statement, model
definitions or explicit allowlist. An independently source-declared helper
remains a separate semantic dependency even if its name ends in `match_1`,
`proof_1`, `_f`, or another recognized compiler-support suffix. Matchers also
require Lean's matcher metadata. Other generated support requires parent
source metadata and no independent source range; an equality instance is
attributed to an inductive only when its generated range lies inside that
inductive's source declaration.

The original literal-only counterexample was accepted before this change and
rejected afterwards. The checker inventory contains 49 pairs, covering every recognized suffix
family, private helpers, handwritten equality instances, genuine recursive
and private matchers, deriving with and without fields, helpers declared after
deriving, and separately compiled/imported fixtures. The complete new-suite
inventory is 60 pairs: these 49, two actual-headline checks, and nine
router/headline checks. All 60 pairs passed locally. The CI validation report uses the same
inventory function as the test runner, including imported-module controls.
The targeted `lake build KernelR.TrustedBase` passed locally with 3,790 jobs
and the same 84 semantic parents. A fresh checked export retains exactly the
same declaration metadata and 523 attributed helpers as the initial checkpoint.
The regenerated guide and manifest pin and authenticate this verification
checkpoint. The final-head CI artifact remains the authority for the full
project build, global audit and complete historical regression sequence.

### Explicit fixed-delay headline and reproducibility review

`FixedDelayChainHeadline.every_finite_chain_fixed_delay` takes the native delay
functions as inputs and states existence and universal outcomes in both native
and geometric semantics under `canonicalFiniteChainRouter`. The router's root,
parent, receiving port, contact window and delay index are explicit; the
constructed chain is proved to use that router. No protocol hypothesis or
axiom is added. The indexed-error theorem remains a separate result.

A local build of `KernelR.Recorded`, `KernelR.HybridFiniteChainCanonicalRouter`
and `KernelR.FixedDelayChainHeadline` passes **3,788 jobs**. The unchanged audit
scanner over these modules and their dependencies checks **7,083 project
theorems**, permitting only `propext`, `Classical.choice` and `Quot.sound`, with
no admitted proofs or added project axioms. These are scoped local totals.
Source hygiene passes for **567 Lean files**, including the five unchanged
inherited modules. `Recorded.lean` and its generator now use a finite
8,000,000-heartbeat budget; generated evidence still matches.

All **six paired fixed-delay controls** pass, covering the supplied delay,
both universal semantic contracts and literal parent/port/window/index/root
routing. The configured Lean paired-control inventory is **1,385**
(1,379 + 6). Thirteen project Python tests and all nine range tests pass;
all six range certificates replay independently, with **672 strict obligations**.
Their numerical payloads and pinned point sources are unchanged. All 16 robust
certificates and the generated Lean evidence replay unchanged.

The README's global **9,618 jobs / 29,298 theorems** are explicitly anchored
to `b5435f3`, not this revision. The complete suite at that checkpoint stopped
at its 90-minute limit after its build, audit and counting tests had passed.
The workflow here retains every check and uses the 120-minute budget also
proposed separately in PR #31.

### Exact counts on the constructed finite-chain witness

`ConstructedBirthCadenceChain.sectionCovered` constructs actual complete
ERROR/MARK covers without a caller-supplied cover or gate premise.
`exact_section_counts` identifies four ERROR sections on each active port
and three MARK sections per cell, summed over ports. The original birth,
physical-box, source-budget and wire hypotheses of the factories are retained.

The application graph builds in **3,758 jobs**. The unchanged audit scanner
imports all **48 changed modules** across this PR and checks **6,553 project
theorems** in their dependency closure, permitting only `propext`,
`Classical.choice` and `Quot.sound`, with no admitted proofs or added project
axioms. These are scoped local totals, not a completed local global build.
The umbrella imports all new modules for the ordinary global CI audit.

Source hygiene passes for **565 Lean files**, with all five inherited upstream
modules unchanged. All **six paired applied controls** in
[`check_hybrid_chain_section_counts_negative.py`](scripts/check_hybrid_chain_section_counts_negative.py)
pass, including counts, cover uniqueness and own-birth offsets. Together with
the 11 section-run pairs, the configured CI inventory is **1,379 pairs**
(1,362 + 11 + 6), separately from audit-corruption checks. The audit's positive
public/private controls and corruption-rejection controls pass locally.

The preceding `93abed8` checkpoint also passes the global build, global audit
and audit-corruption steps in
[Actions run 42012958868](https://github.com/HevisNico/kernel-R/actions/runs/42012958868).
Its remaining regression steps were running when this entry was prepared;
its global totals are not substituted for the scoped application totals above.

### Constructive section covers: checkpoint `93abed8`

The **33 changed Lean modules** and their dependency closure build successfully
in **3,749 jobs**. The unchanged audit scanner, importing those 33 modules,
checks **6,488 project theorems**, permitting only `propext`, `Classical.choice`
and `Quot.sound`, with no admitted proofs or added project axioms. This is a
dependency-closure audit, not a new full-project declaration total; global
validation of this checkpoint is left to its GitHub Actions run.

Source hygiene for this checkpoint covers **555 Lean files**, including the
15 new modules, with all five inherited upstream modules unchanged. All
**11 new paired controls** in
[`check_hybrid_section_runs_negative.py`](scripts/check_hybrid_section_runs_negative.py)
pass: closed counts, open boundaries, composition, exposure, foreign events,
router copies and port relabeling. The configured CI inventory becomes
**1,373 pairs** (1,362 plus 11), separately from audit-corruption controls.

This checkpoint supplies constructive local covers and preserves actual
section runs through causal weaving, queue framing and router changes.
The complete finite-chain cover-existence corollary is still in progress;
the applied counts of four active-port ERROR sections and three MARK sections
are not claimed by this checkpoint.

### Exact dose counting: checkpoint `62376ff`

At `62376ff7dda182bd7e31463eede337fb3390828b`, the local
`lake build KernelR.HybridDoseCounting` passes **3,502 jobs**. This is the
module build, not a new full-project build total. Its six printed headline and
count-uniqueness results use only `propext`, `Classical.choice` and `Quot.sound`.
Source hygiene covers **540 Lean files**, with all five inherited upstream
modules unchanged; generated evidence matches and all **16 robust certificates**
replay.

All **11 new paired controls** in
[`check_hybrid_dose_counting_negative.py`](scripts/check_hybrid_dose_counting_negative.py)
pass locally and in [GitHub Actions run 41994544240](https://github.com/HevisNico/kernel-R/actions/runs/41994544240).
The configured CI inventory is **1,362 pairs** (the preceding **1,351** plus
these **11**), separately from axiom-audit corruption checks. This inventory
counts generated cases; it does not assert a fresh rerun of all historical
suites. The completed global build in that run passes **9,593 jobs** and its
axiom audit checks **29,018 project theorems**, permitting only `propext`,
`Classical.choice` and `Quot.sound`, with no admitted proofs or added project
axioms. All regression steps and all three workflows at this revision finish
successfully. These totals describe `62376ff`, not subsequent revisions.

### Geometric crossing: checkpoint `ef5a510`

The geometric-crossing checkpoint at `ef5a510` passed a completely fresh local project
build (**9,592 jobs**) and global axiom audit (**28,970 project theorems**),
allowing only `propext`, `Classical.choice` and `Quot.sound`. Source checks cover
**539 Lean files**, with all five inherited upstream modules unchanged. All
**81 paired controls** passed: 14 geometric, six scalar transversality, seven
actual-contact, 36 constructed-chain and 18 causal-weave pairs. These are local
validation results, not a claim about an unobserved GitHub workflow run or a
published release. The genuine full-cell grazing fixture in
[`scripts/fixtures/crossing_grazing.lean`](scripts/fixtures/crossing_grazing.lean)
exhibits a weak/model flow excluded by native first-contact urgency outside the
physical box and protocol; it is not a counterexample to the finite-chain result.

### Universal-complete result: historical validated checkpoint

The complete frozen-source universal checkpoint passes **9,557 build jobs**
and the global axiom audit of **27,741 project theorems**. Source checks cover
**504 Lean files**, with all five inherited upstream modules unchanged.
Generated evidence matches, **16 robust certificates** replay, and **12
project tests** pass. The three public `UniversalChainHeadline` declarations,
the native universal factory and the generic complete-execution comparison
use only `propext`, `Classical.choice` and `Quot.sound`.

All **20 new universal paired controls pass**: the valid conclusions compile
first and each altered conclusion is independently rejected with a Lean
diagnostic. The confirmed finite-chain inventory is **218 passing pairs**;
CI configures **1,321 pairs**, plus axiom-audit corruption controls. These totals
do not claim a fresh rerun of every historical suite. The frozen proof tree
is `5dab922f4adb45ff42f53377dcc784b689a27d43`. Verified code commit:
`eeff210df7a2c6297d532c10203312ded3c0bbf9`. Its Lean/workflow/control sources match
the frozen export exactly; only its Markdown documentation differs. The
following documentation/formatting commit records this identifier and removes one trailing space
in the universal preparation source, without changing any Lean statement or
proof. Those published sources are now integrated without changes to the Lean
files or controls; fresh integration CI is recorded separately and is not
presumed successful.

### Prescribed-error existence: historical validated checkpoint


The earlier prescribed-error existence construction passed the complete frozen-source
export: **9,543 build jobs**, **27,587 audited project theorems**, **490 Lean
sources**, generated-evidence checks, **16 robust certificates** and **12
project tests**. All three public indexed headline theorems depend only on
`propext`, `Classical.choice` and `Quot.sound`. No admitted proof or added
project axiom is accepted. Verified indexed code commit:
[550fc9509c8390a07fdb0cec02170a72cbc3071c](https://github.com/HevisNico/kernel-R/commit/550fc9509c8390a07fdb0cec02170a72cbc3071c).
The following documentation-only commit records this identifier; the Lean,
workflow and control-script sources are unchanged from the verified code tree.

The 20 new indexed paired controls pass, bringing the confirmed finite-chain
inventory to **198 passing pairs** and the configured CI inventory to
**1,301 paired controls**, plus axiom-audit corruption checks. These totals
do not assert a fresh local rerun of every historical suite. The indexed
controls include actual final fast sender indices, prescribed delay values
and retained whole-execution terminal/count conclusions.

### Native-function construction: historical validated checkpoint

The completed native-function construction passed the pinned complete export:
**9,537 build jobs**, **27,515 audited project theorems**, **484 Lean sources**
and five unchanged inherited modules. Generated evidence, all **16 robust
certificates** and **12 project tests** pass. The audit allows only `propext`,
`Classical.choice` and `Quot.sound`.

At that checkpoint, all **178 finite-chain paired controls passed**:48 first-checkpoint,40 preparation,
15 full-budget,19 receiver,20 port/index and36 global-construction contracts.
Each valid conclusion compiles before its altered conclusion is individually
rejected with a Lean diagnostic. CI configured **1,281 paired controls**, plus
axiom-audit corruption checks; this inventory does not claim a fresh local
rerun of every historical suite. Verified code commit:
[2c50e42e4ba02bd77c20dfd2612a587dfda4c224](https://github.com/HevisNico/kernel-R/commit/2c50e42e4ba02bd77c20dfd2612a587dfda4c224).
A following documentation-only commit records that identifier; proof sources
are unchanged. Fresh CI status is recorded in PR #15; in-progress CI is not
labeled green.

That checkpoint's [native finite-chain headline](KernelR/FiniteChainHeadline.lean) groups
existence from independent births, terminal memories/state and actual counts.
Its three `#print axioms` outputs contain exactly the three permitted logical
axioms. The [native headline source](KernelR/FiniteChainHeadline.lean) retains those exact signatures.

### First exported checkpoint: historical validated baseline

Commit `21cf9821af0f90ada4301b9791ed8492f936d934` published the first13 modules.
Its complete exported-tree build passed **9,502 jobs**, its global audit
passed **26,659 project theorems**, and source checks covered **449 Lean
files**, with five inherited modules unchanged. Generated evidence, all
**16 robust certificates**, **12 project tests** and **48 new paired
controls** passed. CI configured **1,151 paired controls**, plus axiom-audit
corruption checks; that inventory does not claim a fresh local rerun of every
historical suite. These figures describe that commit, before the completed
common-birth construction.

Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the audit.
Each exported checkpoint must record exact build/audit results and its remaining
quantified premises. The N=3 baseline remains separately completed. A pause
stops new work; the branch, validated commits and this ledger provide the
restart point. No push, PR publication or merge is performed without the user’s
explicit instruction. The [historical PR description](UNIVERSAL_EXECUTION_PR.md)
records the reviewed universal proof change; the current
[release checklist](../../docs/RELEASE_UNIVERSAL_FINITE_CHAIN.md) does not
authorize an automatic merge or release publication.

## Recovery-limited firing rate local validation

Code checkpoint: `b33af69356790f3ab45fd8dc4ee675c721221e3a`, based on main
`0f39642`. The new native and direct weak/crossing proof modules are
[HybridResetRate](KernelR/HybridResetRate.lean) and
[HybridResetRateCrossing](KernelR/HybridResetRateCrossing.lean). They establish
actual FIRE gaps and finite-window count bounds for arbitrary finite networks
under a pathwise recovery envelope, with a uniform specialization from the
initial built-in recovery cap. No protocol or completion premise is imposed.

Local validation on 6 November 2026:

- Full default `lake build`: passed, 9,626 jobs including cached dependencies.
- The unchanged global `Audit` target passed for 29,405 imported project
  theorem declarations, allowing only `propext`, `Classical.choice` and
  `Quot.sound`. New modules are included through the umbrella import.
- `python scripts/check_hybrid_reset_rate_negative.py`: ten paired controls
  passed; valid contracts compile and mutated contracts fail with type errors.
- Source hygiene and five inherited-source identities passed; the unchanged
  base byte checks retain the same base and permit only named added modules.
- Generated numerical evidence freshness, sixteen robust certificate replays
  and all three project-layout tests passed.
- A fresh Lean metadata export retained the same 84 trusted semantic
  declarations. The source-hash record and reading list were regenerated for
  the code checkpoint; the authenticated document check passed.

The dependency caches were reused. These are local checks, not a fresh
external-dependency rebuild or the entire CI workflow. The new paired suite
is included in CI; the unchanged historical negative suites retain their
existing CI stages. See [scope](../../docs/RESET_RATE_SATURATION.md).
