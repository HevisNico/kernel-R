# N-cell Lean coverage and remaining refinement obligations

The [written finite-chain argument](../reciprocal_composition/THEOREM.md) now
has a constructed physical common-birth family for every positive finite N,
as well as its earlier abstract induction. The new universal-complete layer now
also proves the terminal physical outcome and actual per-cell FIRE dates for
**every complete finite execution** of the same fixed program through its
terminal T. The [progress theorems](PROGRESS.md) separately cover stopped
prefixes and semantically maximal infinite runs of that finite-source program.
The full written theorem, retained probes/copies and operational perturbations
remain separate obligations.

The [geometric correspondence](../../docs/MODEL_LEAN_CORRESPONDENCE.md#threshold-contacts-and-upward-crossings)
also covers every geometrically complete model execution of this protocol:
it refines to a complete native execution with the exact same paths and jumps,
so physical endpoints, ordered per-cell FIRE lists, counts and prescribed errors
transfer. Conversely, a complete native outcome has a crossing representative
with the same observations and FIRE lists. This does not identify every native
simultaneous-event linearization with a crossing history. Birth, fabrication,
source, delay and budget hypotheses are unchanged.

See [UniversalChainHeadline](KernelR/UniversalChainHeadline.lean) and the
[exact quantifiers and validation ledger](EVERY_N_PLAN.md). The indexed order
is **∀ admissible data/errors, ∃ fixed native functions and a complete witness,
∀ finite executions complete at T under that same router**. This is not a
universal assertion about stopped prefixes or indefinite network runs.

`every_finite_chain_exists` in
[IndexedChainHeadline](KernelR/IndexedChainHeadline.lean), backed by
`indexed_birth_cadence_chain_exists` in
[HybridIndexedBirthCadenceChain](KernelR/HybridIndexedBirthCadenceChain.lean),
starts from independent READY births at0 with independent fixed fabrication parameters.
Sixteen period-eight inputs prepare each relay on port2 and the leaf on port1;
K period-four inputs drive leaf port0 from160, with `K ≥ 4*N+12`.
A single fixed gated router covers preparation and cadence. The factory has
no prepared-state, reaching-execution, received-calendar, output-count,
native-delay-function or `CellLaw` premise. For each link j<N-1, the caller
prescribes `error j k` for every emission index k with `|error j k| ≤ σ_j`,
fixed centre `0.3+σ_j ≤ d_j ≤ 0.4-σ_j`, nonnegative σ_j and cumulative
`sum σ_j ≤ 0.15`. The factory constructs fixed native δ_j(t), bounded within
σ_j of d_j for every time, and proves `δ_j(F_jk)=d_j+error j k` on the final
fast execution's actual ordered sender ledger. Sender j is physical cell
`n-j`; error indices start at0 in `chain.fastExecution`, excluding preparation
FIREs. The actual indexed stage is retained through the birth wrapper.
The earlier `birth_cadence_chain_exists` API takes native functions as inputs.
The new `ConstructedBirthCadenceChain.all_complete` comparison applies to its
fixed router as well. `HybridUniversalExecution` proves the needed physical
uniqueness, including capped actuator gates, and legal jump confluence; it is
not an added caller premise. At an arbitrary complete trace, FAST errors are
indexed after dropping its own12/14 preparation FIREs from the full list.

The [construction ledger](EVERY_N_PLAN.md) records both APIs and validation.

At `T=160+4*(K-1)+1.1*(N-1)+8`, all cells are READY/q=0.1 with no RAW and an
empty pending queue; `CompleteThrough`, physical bounds and raw validity
are derived. Each active log-gain is its own birth value+2.4, and recovery is its
own birth value+0.3. On the constructed common-birth witness,
[`ConstructedBirthCadenceChain.exact_section_counts`](KernelR/HybridFiniteChainDoseCounting.lean)
identifies these with four complete exposed ERROR sections on the active port
and three protected MARK sections summed over all ports. The leaf also has
one preparation ERROR on port1. At leaf-to-root depth j, fast emissions are `K-5-2*j`,
totaling `N*(K-N-4)`. Preparation contributes `12*N+2` actual FIREs; cumulative
traffic is `N*(K-N+8)+2`. Lean uses `n=N-1`, root0 and leaf `Fin.last n`, so
physical cell i has depth `n-i.val`.

The original N=3 staged A/B/C protocol is separately completed at789.9,
with independent B/C births at160/480 and cumulative A54/B61/C34. Its cadence
emits A16/B18/C20; all finish READY/q=0.1 with no RAW or pending tokens,
active log-gains A2/B2/C0 equal to own birth+2.4 and recovery own birth+0.3.
Its source/birth program differs from the scalable common-birth protocol;
the new whole-execution cover theorem above applies to that common-birth
witness, not to this separately staged execution.

`birth_protocol_complete_cadence_exists` returns
`ConstructedBirthCadenceProtocol`, retaining both genuine births and the
actual two-cell execution between them. C teaching and cadence execute under
one fixed gated three-cell router. Retargeting preserves the complete physical
ledger and delivered occurrences, and cumulative counts54/61/34 are proved
for that actual staged execution.

The autonomous C witness and P(3,17,0) leaf packet remain components. B's real
receiver emits18 signals and supplies P(5,13,1/20), and A's receiver of the next
wire packet emits16. Causal weaving constructs actual global issuance and
arrival from the original external C25 queue. No reaching execution, receiving
calendar or output count is a factory premise; future wire tokens are not
preloaded into the global source queue. The previous C660 checkpoint and
C-only789.9 endpoint remain historical witnesses.

`HybridBirthLearnedRest` separately bridges Aport2/Bport2 projections of639.9
to isolated learned one-cell contracts with settling7.5. Its empty analysis
queues do not physically remove global tokens. Neither that bridge nor either
finite construction supplies universal
physical contracts for arbitrary introductions or port permutations, or an
indefinitely repeatable network contract.

## Checked composition

| Written argument | Lean module and declarations | Scope |
|---|---|---|
| Packet definition and spacing | `Chain.Packets`: `Packet`, `Packet.ideal_gap`, `Packet.actual_gap` | Existential ideal dates and bounded phase errors; width-one pulses are separated |
| Wire rule | `Packet.wire`, `wire_actual`, `wire_delay_bounds` | Fixed centres shift ideal dates, arbitrary bounded errors add their full budgets |
| Relay closure | `Packet.relay`, `relay_actual_prefix`, `relay_actual_second_fire`, `relay_actual_first_high`, `relay_actual_regular_tail` | Constructs P(m+2,L-4,J), preserves retained errors and proves exact correspondence to the declared emitted input indices |
| Leaf packet | `leafPacket` | Constructs P(3,K-8,0) from the declared leaf firing dates and latency bounds |
| Constructed physical C leaf | `HybridBirthCadenceLocalC`, `HybridConstructedCadenceLeafPacket` | Actual autonomous C639.9→789.9 ledger refines P(3,17,0); bounded-delay labels refine P(3,17,1/20), used by the constructed causal C→B→A weave |
| Constructed physical N=3 | `HybridLocalCadenceReceiver`, `HybridConstructedCadenceBC`, `HybridConstructedCadenceCascade`, `HybridBirthCadenceCascade`, `HybridBirthCadenceProtocol` | Actual leaf, B/A receivers and causal weave; A54/B61/C34 at789.9; separate from the new common-birth every-N family |
| Constructed common-birth every-N | `HybridFiniteChainFamilyPreparation`, `HybridPreparedCadenceChainConstruction`, `HybridBirthCadenceChain` | Actual birth preparation, variable-K leaf, full-budget physical receivers and causal weave; terminal own memories and cumulative counts |
| Prescribed-error whole-chain realization | `HybridIndexedPreparedCadenceChain`, `HybridIndexedBirthCadenceChain`, `IndexedChainHeadline` | Generated fixed native functions match every prescribed error on final fast sender FIREs; actual birth, router, memory and count invariants retained |
| Every complete physical trace | `HybridUniversalExecution`, `HybridUniversalBirthCadenceChain`, `UniversalChainHeadline` | Every finite native trace complete through fixed T, under the same initial state/router; physical endpoint equality, exact ordered per-cell FIRE lists and prescribed FAST errors |
| Geometric model correspondence | `HybridCrossingExecution`, `HybridCellOrbitExistence`, `HybridWeakNativeRefinement`, `HybridCrossingCorrespondence`, `CrossingChainHeadline` | Actual historical left approach and full-cell right ODE germ; exact model-to-native refinement, with native-to-model observational representatives |
| Every finite weak/model prefix | `HybridCrossingProgress` | Exact native refinement at every finite date and history-preserving crossing extension to every later finite horizon; infinite/maximal-run theorems retain the native interface |
| Physical packet closure | `HybridLocalCadenceBudgetReceiver`, `HybridCadencePacketRelay` | Cumulative jitter≤0.15; directly proved high latencies[0.16,0.26], first≤rest, exact actual output packet |
| Universal induction | `Chain.Induction.compose_every_finite_chain`, `root_contract` | Every positive finite N; validates every intermediate tail and cumulative jitter budget |
| Actual stream interface | `Chain.Refinement.realized_chain` | Composes explicit routed streams, given a leaf refinement and local `RelayLaw` proofs |
| Resource algebra | `Chain.Algebra`, `traffic_closed_form`, `traffic_at_minimum` | Twelve integer identities, natural-number counts, root tail, root emissions and quadratic total traffic |
| Jitter specialization | `pathJitter_mono`, `uniform_jitter_total`, `full_jitter_iff_four_cells`, `fixed_delays_any_depth` | Nonuniform cumulative budgets; uniform min(1/20,3/(20 links)); full 1/20 jitter is sufficient through four cells |
| Dose words and settings | `Chain.Consequences` | Leaf/relay word counts, four total ERROR doses, two fast MARK doses, gain exp(12/5), final recovery interval |
| Exact whole-execution dose counts | `HybridDoseCounting`: `Execution.memory_of_section_covers`, `from_birth_memory_of_section_covers` | Conditional on actual complete exposed ERROR/MARK covers; gain increments are 0.6 times each port's ERROR count and recovery is 0.1 times the sum of MARK counts. The finite-chain application below constructs these covers. |
| Constructed finite-chain section counts | [`HybridFiniteChainDoseCounting`](KernelR/HybridFiniteChainDoseCounting.lean): `ConstructedBirthCadenceChain.sectionCovered`, `exact_section_counts` | Actual covers for the birth-to-terminal witness under its original physical hypotheses: active-port ERROR count 4 and MARK count 3 summed over all ports of each cell. The leaf additionally has one preparation ERROR on port1. Universal endpoint comparison does not assert covers for other complete traces. |
| Cuts and terminal time | `cut_propagates`, `all_cells_quiescent_by` | Induction from explicit local silence and settling-time hypotheses |
| Same-gain root ordering | `same_gain_ready_comparison`, `first_crossing_no_later` | Residual charge cannot delay the first crossing when comparing the same realized gain |
| Local certificate endpoints | `Certificates.Composition003`, `Composition010` | All 162 strict comparisons and validity of all 352 rational enclosures in the two committed certificates |

The finite signal interface records an exact event count, so its refinement
contract excludes both missing and additional emissions. The packet representation
includes bounded padding phases beyond the finite packet.
Only indices below m+L represent actual events. This lets retained phase errors be
selected without adding a physical independence or retiming assumption.

The natural-number theorems prove the subtraction side conditions; integer
polynomial identities alone would not justify truncated natural subtraction.
No theorem restricts N to a tested maximum, and none assumes identical devices.

## What is still required for the full physical theorem

1. Extend beyond the declared common-birth preparation, source and port
   family where required by the full written statement. The new family already
   constructs arbitrary finite chain length without local-law premises.
2. Prove sound enclosure membership for remaining exp/log expressions and
   trajectories. Generated endpoint comparisons alone do not supply it.
3. Supply the older `Chain.Refinement.RelayLaw` with its narrower timing bounds
   if using that API. The new physical construction instead uses the proved
   broad-latency `relayCadence` closure and does not assume this law.
4. Formalize retained frozen probes, cuts/settings copies and their physical
   preservation semantics and operational drift/noise/amplitude histories.
   Universal refinement for the declared finite-complete class and
   [progress for the fixed finite-source program](PROGRESS.md) are proved.
   Indefinitely repeatable responding operation remains open.

Existing `Doses`, `Flow`, `Recovery`, `Energy` and `Cadence` lemmas support
these obligations but do not already discharge all of them. The older abstract
local contracts remain ordinary quantified premises.
The new common-birth factory supplies its physical leaf and receivers through
construction instead of requiring those contracts from callers. There are no
admitted proofs or new axioms.

## Reproduction and falsification

Run the commands in the [Lean guide](README.md). The generated-evidence check
covers both N-cell certificates. The axiom audit includes every imported chain
and certificate theorem. Negative tests reject altered traffic counts and an
over-budget four-link jitter claim, in addition to the existing endpoint,
cadence and adaptive-record corruption cases. The 29 paired controls in
`python scripts/check_hybrid_feedback_entry_negative.py` additionally check
the constructed weak entry and first reverse FIRE, own memories and exact
source/wire queues. The 40 additional paired controls in
`python scripts/check_hybrid_reverse_receipt_negative.py` pass for the
actual first receipt and352 handoff, own memories, exact queues and
A28/B15. The 40 subsequent pairs in `python scripts/check_hybrid_reverse_epoch_negative.py`
cover the constructed reciprocal epoch through459.9, its actual
sources and wires, retained own memories and A38/B27: all valid conclusions
compile and all altered claims are rejected. The 50 new pairs in
`python scripts/check_hybrid_c_teaching_existence_negative.py` pass for the
actual C birth/teaching, three-cell execution, own memories and A38/B43/C14.
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
[EVERY_N_PLAN.md](EVERY_N_PLAN.md). The validated baseline figures above remain
those of the N=3 commit; current finite-chain validation and checkpoint
history are recorded there.

Only `propext`, `Classical.choice` and `Quot.sound` are allowed; no physical
leaf/relay premise is replaced by a project axiom.

The original written theorem and its authenticated snapshots are retained
unchanged. This guide states the current machine-checked coverage separately.
