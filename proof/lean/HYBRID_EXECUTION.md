# Physical execution semantics and analytic refinement

The [trusted-base guide](../../docs/TRUSTED_BASE.md) identifies the definitions
used by the fixed-delay headline's statement. Its explicit-router restatement
preserves these execution semantics and their existing hypotheses.

A physical common-birth construction now covers every positive finite N;
every finite complete execution of its fixed program now has the same
physical endpoint and exact per-cell FIRE dates. The
[progress theorems](PROGRESS.md) cover finite continuation and maximal
infinite-run progress for this fixed finite-source chain. The
[construction section](#constructed-common-birth-chain-for-every-finite-n)
records its precise family and quantifiers. Retained probes/copies and the
full written theorem remain open.
The [geometric crossing correspondence](../../docs/MODEL_LEAN_CORRESPONDENCE.md#threshold-contacts-and-upward-crossings)
now also transfers the complete finite-chain outcomes to model histories.
Every finite weak prefix refines exactly to native paths and jumps, and every
finite crossing prefix extends to any later finite horizon with its history
retained. Infinite/maximal-run theorems keep their native `InfiniteExecution`
interface.
The declared three-cell cadence is now constructively realized from A's READY
birth through789.9, including independent B/C births at160/480. Cumulative
counts are A54/B61/C34; the cadence contributes A16/B18/C20. All three cells
finish READY at q=0.1, with RAW absent and no pending tokens, physical reserve
and cap bounds, and `CompleteThrough789.9`. Active log-gains A2/B2/C0 are their
own birth values+2.4, and every recovery is its own birth value+0.3. Other
teaching gains are preserved.

The construction uses C's actual autonomous leaf ledger, physical B and A
receivers and causal queue weaving. At639.9 the global source queue contains
only the 25 external C tokens; later wires are issued by genuine FIRE jumps
and consumed by genuine arrivals. Neither a later reaching execution nor a
received calendar or output count is supplied. The earlier660 global prefix
and C-only789.9 witness remain available. Fixed independent fabrication
parameters, canonical pulses and bounded delays retain their declared scope;
fine operational robustness, probes/copies and universal guarantees through
the separate staged-birth operations remain distinct obligations. The common-birth finite-chain construction and validation are tracked in
[finite-chain construction](../../docs/FINITE_CHAIN_CONSTRUCTION.md).

## Constructed common-birth chain for every finite N

[IndexedChainHeadline](KernelR/IndexedChainHeadline.lean) exposes
`every_finite_chain_exists`, backed by `indexed_birth_cadence_chain_exists` in
[HybridIndexedBirthCadenceChain](KernelR/HybridIndexedBirthCadenceChain.lean).
It constructs `ConstructedIndexedBirthCadenceChain` for every positive finite N
(`n=N-1` in Lean). This is a separate protocol from the completed staged A/B/C construction. Each independently
chosen cell is born at0;16 period-eight preparation inputs drive leaf port1
and relay port2. The leaf's K period-four port0 inputs start at160, with
`K ≥ 4*N+12`, and are already retained in the original global source queue.
Preparation reaches159.9. One fixed router has contacts closed before160
and open on `[160,T+1)` for the fast phase, where
`T=160+4*(K-1)+1.1*(N-1)+8`.

The factory takes independent `BirthState`s, all auxiliaries initially READY,
fixed independent `PhysicalBox` parameters (±0.3% or ±10%), canonical pulses
and the exact preparation queues. For every link j<N-1 it takes a fixed centre
d_j, nonnegative σ_j and an arbitrary prescribed sequence `error j k`, with
`0.3+σ_j ≤ d_j ≤ 0.4-σ_j`, `|error j k| ≤ σ_j` for every k, and cumulative
`sum σ_j ≤ 0.15`. Native delay functions are constructed with global bounds
`|δ_j(t)-d_j| ≤ σ_j` for every t, and with
`δ_j(F_jk)=d_j+error j k` at each actual kth fast-phase sender FIRE in the
final global execution. Wire j leaves physical cell `n-j`
(`indexedCadenceSender n j`); its index starts at0 in `chain.fastExecution`,
excluding the12/14 preparation FIREs.

No prepared state, reaching execution, received calendar, output count, native
delay function or `CellLaw` is a caller premise. The chosen indexed stage and
its exact ordered sender ledgers are preserved through later physical weaves
and retained in the birth wrapper. Preparation retargeting retains its actual
ledger and deliveries; genuine wires are issued and consumed under the one
fixed router. The earlier `birth_cadence_chain_exists` API remains available
for caller-supplied native functions with the same global bounds.

At T all cells are READY/q=0.1 with RAW absent and an empty global queue.
`CompleteThrough`, reserve/cap bounds and raw validity are conclusions.
Active log-gain is its own birth value+2.4 (leaf port0, relay port2), and recovery
is its own birth value+0.3. Other gains retain their actual preparation values.
On this constructed witness,
[`exact_section_counts`](KernelR/HybridFiniteChainDoseCounting.lean) identifies
these increments with four complete exposed ERROR sections on the active port
and three protected MARK sections summed over all ports. The leaf's additional
preparation ERROR lies on port1.
At leaf-to-root depth j, fast traffic is `K-5-2*j`, totaling `N*(K-N-4)`.
Preparation contributes14 leaf FIREs and12 per relay, totaling `12*N+2`;
the actual full ledger contains `N*(K-N+8)+2` emissions. Physical indices
run root0 to leaf n, reversing the depth index: `j=n-i.val`.

The full-budget receiver derives high latencies in[0.16,0.26] with first≤rest;
`Packet.relayCadence` proves the closure used in construction. This does not
supply the older, narrower `Chain.Refinement.RelayLaw`. The new indexed
factory closes the prescribed-sequence realization obligation for the whole
birth-to-terminal execution; its generated delay functions and retained actual
stage satisfy both global native bounds and the requested per-emission values.

See the [finite-chain coverage guide](N_CELL_COVERAGE.md) and
[construction guide](../../docs/FINITE_CHAIN_CONSTRUCTION.md) and
[validation ledger](../../docs/VALIDATION_LEDGER.md). Retained probes,
cuts/settings copies and operational drift/noise/amplitude histories remain
open. The universal-complete layer below compares every finite execution of the
fixed common-birth program complete at T, without claiming all six conclusions
of the written finite-chain theorem.

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
`Classical.choice` and `Quot.sound`. The [validation ledger](../../docs/VALIDATION_LEDGER.md)
records the successful complete frozen-source build and global audit.
The reviewed universal proof modules are included in this checkout. The
[historical release checklist](../../docs/RELEASE_V0_2_0.md)
records the v0.2.0 integration and publication scope; later local validation is
recorded in the [current ledger](../../docs/VALIDATION_LEDGER.md#validation-and-checkpoint-discipline).

## Physical definitions

For FIRE/MARK, the native equality guards below are related to the written
upward-crossing rule by [HybridCrossingExecution](KernelR/HybridCrossingExecution.lean)
and [HybridCrossingCorrespondence](KernelR/HybridCrossingCorrespondence.lean).
Weak READY flows permit equality without a jump; model FIRE/MARK require an
actual strictly-below historical left interval and a full-cell incoming-mode
ODE germ above threshold to the right. `CrossingCompleteThrough` excludes
exactly jumps satisfying both conditions. The protocol derives transversality
and strict routing, so no new physical caller inputs are added. The converse
from complete native histories supplies equal observations and ordered FIRE
lists, not identity of every simultaneous-event presentation.

`KernelR/Hybrid.lean` defines a pulses-only finite network with all q/m/z/b/E
coordinates, main and three auxiliary modes, raw-current origins and pending
delivery tokens. Parameters are independent per cell and port. `PhysicalBox`
states the ±0.3% or ±10% fabrication family. `BirthState` states the common
zero-time birth family, including allowed residual ERROR phases. Its pending
queue must separately be fixed to the supplied source protocol. The field here
uses fixed fabrication parameters and canonical amplitudes. The drift, charge
noise and amplitude variation studied by the conditional `Robust` modules have
not yet been instantiated in this operational semantics.

`field` contains the actual equations, complete work expression, energy gates,
and gain/recovery cap gates. A positive-duration `Flow` supplies continuous
coordinates satisfying integral ODEs on every prefix, with fixed discrete state.
Strict pre-guard conditions prevent advancing through a mode's first section.
Raw support and pending-delivery urgency prevent passing current ends or arrivals.

`Jump` permits only guarded section changes, delivery of an actual queued token,
or the end of an active raw current. Jumps preserve physical coordinates and time.
A fire appends routed tokens. An arrival removes one actual occurrence and requires
a free port. Canonical currents have half-open support, independently of main mode;
reopening admission retains any unfinished raw tail.

Source tokens are supplied in the initial pending queue or explicitly at a
`BirthStep` for the fresh cell. `CausalRouter` states causality of the supplied
wiring; generic ledger identities do not require that extra premise. The
staged-birth extension is described below. Settings copying still needs a
separate semantic operation or a proved reduction.

`Execution` retains arbitrary legal zero-time interleavings without a total event
priority. `simultaneous_fire_mark_orders` constructs both compatible orders for
simultaneous main-fire and auxiliary-MARK guards. It does not establish global
confluence or simulator coverage of all simultaneous events.

`CompleteThrough` requires reaching the horizon and discharging enabled jumps
and due deliveries, including events exactly at the horizon. `Flow.prefix`
constructs a valid shorter prefix of an existing flow; `Flow.suffix` later
retains its already-given remainder. Neither result extends beyond the supplied
execution. `birth_resting_complete_exists` exhibits a complete
positive-duration silent execution from a nominal READY state and proves that
this state belongs to `BirthState`, with the prescribed nominal log-gains and
an empty source queue. This is one concrete birth-family witness, not existence
for every initial state or for the complete training protocols. The
source-driven construction below covers the declared READY A birth family,
with initially READY auxiliaries and the exact protocol queue.

## Detailed sections

The construction is described in five pages:

| Page | Content |
|---|---|
| [Constructed protocol checkpoint](hybrid/CHECKPOINT.md) | the current birth-protocol factory and its earlier factories, stage by stage |
| [Checked implications](hybrid/IMPLICATIONS.md) | a table of the modules and the consequences they prove from the operational equations, with their boundaries |
| [Doses, sensor cycle and isolated inputs](hybrid/SENSOR_AND_INPUTS.md) | doses and clipping, the actual sensor cycle, isolated main inputs |
| [Birth and preparation](hybrid/BIRTH_AND_PREPARATION.md) | the first birth-to-preparation phase, receiving calendars, staged birth, common latency |
| [Teaching and cadence](hybrid/TEACHING_AND_CADENCE.md) | routed calendars, teaching across B's birth, reciprocal entry, C introduction, cadence, event budget, connection to finite-chain composition |

## Remaining obligations for the complete theorem

1. Extend beyond the declared common-birth/source/port family where required
   by the full written theorem. Arbitrary bounded prescribed per-emission errors
   now have a whole-chain birth-to-terminal realization with generated fixed
   native delay functions and exact final fast sender ledgers.
2. Establish sound real enclosure membership for remaining stored certificate
   bounds. Exact endpoint comparisons alone remain insufficient.
3. Formalize retained frozen-probe responses, later cuts/settings copies and
   their physical preservation semantics.
4. Extend progress beyond the fixed finite-source program. For that program,
   [finite continuation and maximal-run progress](PROGRESS.md) are proved.
   Indefinitely responding network operation under continuing inputs remains
   open.
5. Instantiate operational drift, charge noise and amplitude variation in the
   physical semantics; the existing robust analyses remain conditional.

Certificates, manifests, recordings and the pinned prototype ZIP retain their
existing identities and scope. Neither physical construction assumes a recorded
pulse-case word, and finite counter replay does not prove trajectories.
The partial-dose calculation is not a reachable training counterexample.

## Validation

Use the pinned Lean/Mathlib versions and the complete command list in the
[Lean guide](README.md#reproduce). The authoritative CI sequence is
[lean.yml](../../.github/workflows/lean.yml); it builds `KernelR` and `Audit`,
checks source/evidence identities and runs every negative-control suite.

The audit scans every imported and current project theorem and permits only
`propext`, `Classical.choice` and `Quot.sound`. Its own negative controls cover
corruption in imported artifacts and current declarations. Standalone controls
reuse the same compiler options and dependency artifacts as the main build.
Each positive control must compile before its altered conclusion must fail
with a Lean diagnostic; an unrelated compiler or import failure is insufficient.

The physical suites exercise guards, real doses and raw tails, reserve/cap
bounds, event budgets, exact queues and deliveries, staged births, own memories,
wire jitter, conditional cadence and the original-birth constructors. The
29 paired controls in `check_hybrid_feedback_entry_negative.py` additionally
check B344, its residual first FIRE, cumulative A28/B15, the issued Aport2 token
and both interval-scoped emitting products. The additional 40 paired controls
in `check_hybrid_reverse_receipt_negative.py` pass for the actual reverse
receipt and352 handoff, including the original-birth factory, own memories,
real sender clocks/RAW expiry, retained A cut, B352 source, A28/B15 and27
sources. The 40 additional `check_hybrid_reverse_epoch_negative.py` paired controls
exercise the later weak cuts, actual reverse receipts, learned-cycle induction,
exact future queue and original-birth459.9 factory. All valid conclusions compile
and every altered conclusion is rejected. The 50 new pairs in
`check_hybrid_c_teaching_existence_negative.py` also pass for C's real birth,
weak and retained SLOW paths, protected MARK, true three-cell execution,
own memories, cumulative A38/B43/C14 and exact 25-source queue.
The preceding autonomous-C/leaf-packet checkpoint passed the complete pinned
build (9,458 jobs) and global audit (25,538 project theorems), with 405 Lean
source files and five unchanged upstream modules. Generated evidence, all 16
robust certificates and 12 project tests passed. Its 53 additional paired
controls passed: 25 local-C-tail, 20 constructed-leaf/projection and eight
actual high-return-prefix checks. The high suite had 32 passing pairs, and
that checkpoint configured 877 controls.

The completed N=3 historical export passed the pinned build (**9,489 jobs**)
and global
axiom audit (**26,317 project theorems**), allowing only `propext`,
`Classical.choice` and `Quot.sound`. Source checks cover **436 Lean files** and
five unchanged upstream modules; generated evidence, all **16 robust
certificates** and **12 project tests** pass. All new proof modules compile
with the default heartbeat limit.

At that N=3 checkpoint, all **226 new paired controls passed**:48
cascade/birth/protocol,30 receiver/BC,
34 strong-jitter source, 22 learned-source prefix, 18 causal weave, 17 high-jitter,
14 jitter span, 12 MARK-only, 12 mixed, 12 router transport and 7 future-frame.
Each valid conclusion compiles before its altered conclusion is rejected with
a Lean diagnostic. CI configures **1,103 paired controls**, plus axiom-audit
corruption checks; this inventory does not assert a fresh local rerun of every
older suite. Fresh CI status and the verified commit are reported on the PR.

The public [headline](KernelR/Headline.lean) groups the existence, actual terminal
state/counts and own learned-memory theorems and retains their exact signatures
and `#print axioms` commands. The [repository overview](../../README.md) states
the current finite-chain scope; the
[model correspondence](../../docs/MODEL_LEAN_CORRESPONDENCE.md) maps equations
to their operational definitions. N=3 remains finalized; the distinct
common-birth every-N construction is tracked in
[finite-chain construction](../../docs/FINITE_CHAIN_CONSTRUCTION.md). The validated baseline figures above remain
those of the N=3 commit; current finite-chain validation and checkpoint
history are recorded there.

Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Fresh CI status
is reported separately on the PR.
