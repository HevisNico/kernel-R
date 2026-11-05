# R model ↔ Lean correspondence

This map compares the [R cell equations](../kernel/README.md) with the
operational semantics in [Hybrid.lean](../proof/lean/KernelR/Hybrid.lean).
Lean proves properties of these definitions under stated hypotheses; matching
a physical device or a numerical engine requires separate justification.

Write a=ln4, κ=1/2, r=1/10, rₘ=1/40, and gₚ=exp(zₚ).

| Model component | Equation or operational rule | Exact Lean definition |
|---|---|---|
| State and fixed parameters | q, mₚ, zₚ, b, E; main READY/FAST/SLOW; auxiliary READY/MARK/SILENT/ERROR; per-port Cₚ,Lₘₚ,Lₛₚ,Lₑₚ,Mₚ | `Coord`, `MainMode`, `AuxMode`, `Snapshot`, `Parameters`; `PhysicalBox` independently bounds the five parameters at every cell/port, with ε=3/1000 or1/10 |
| Canonical pulse and raw origin | p_F(t)=a exp(−a(t−F)) on[F,F+1), zero outside; each active port retains its actual F | `a`, `pulse`, `current`, `Snapshot.raw`; `Jump.arrive` installs an origin, `Jump.rawEnd` removes it exactly at F+1 |
| READY charge and gain | q′=κ(r−q)+Σₚexp(zₚ)pₚ(t) | `drive`; `field` at `.q` with main `.ready`; gains multiply incoming current only in this mode |
| FAST and SLOW | FAST:q′=−a q until q=1/4; SLOW:q′=−b(t)q until q=r | `field` at `.q`; `Jump.fire`, `Jump.fastEnd`, `Jump.reopen`; no prescribed SLOW return date |
| Auxiliary charge | READY:mₚ′=κ(rₘ−mₚ)+Mₚpₚ; otherwise mₚ′=−L_mode,p mₚ | `field` at `.m p`, `auxDrain`; auxiliaries see raw current even while main admission is closed |
| Auxiliary thresholds | READY→MARK at1; →SILENT at4/5; →ERROR at1/10; →READY at1/40 | `Jump.mark`, `.silent`, `.error`, `.auxReady` |
| Gain learning and protection | zₚ′=8Lₑₚmₚ when auxiliary ERROR, main READY, E>0 and zₚ<ln Cₚ; otherwise0 | `errorAct`; `field` at `.z p` |
| Recovery learning | b′=½ΣₚLₘₚmₚ when auxiliary MARK, main not READY, E>0 and b<11/10; otherwise each contribution0 | `markAct`; `field` at `.b` |
| Energy and work | E′=10(100−E)−W; W sums main work, auxiliary admission/drains and actual learning actuations | `work`; `field` at `.energy`; [HybridWork](../proof/lean/KernelR/HybridWork.lean), `Execution.reserve_birth_invariant`, proves reserve bounds under physical birth/parameter hypotheses |
| Caps and actual doses | Gain/recovery actuation vanishes at its cap; full ERROR adds0.6 and protected MARK adds0.1 only when their gates remain open | `errorAct`, `markAct`; [HybridInvariants](../proof/lean/KernelR/HybridInvariants.lean) cap barriers; [Refinement](../proof/lean/KernelR/Refinement.lean) actual integral ledgers and gain/recovery balances; [HybridDoseCounting](../proof/lean/KernelR/HybridDoseCounting.lean) whole-execution integer counts, conditional on covers of complete exposed sections; [HybridFiniteChainDoseCounting](../proof/lean/KernelR/HybridFiniteChainDoseCounting.lean) constructs the finite-chain witness covers and proves active-port ERROR count 4 and all-port MARK count 3 |
| Continuous evolution and first contacts | Integral ODE on every flow prefix; strict interior guards prevent an old-mode flow from passing its first threshold contact | `Flow.integral_eq`, `.guards`, `BeforeGuards`; `.raw_support` and `.pending_urgent` prevent flowing past raw expiry or a due token |
| Events and causal wiring | Jumps preserve time and physical coordinates. FIRE appends routed tokens; arrival removes one actual due occurrence on a free port | `setMain`, `setAux`, `setRaw`, `Jump`, `Delivery`, `Router`, `CausalRouter`; `Execution` composes actual flows and jumps without a fixed simultaneous-event priority |
| Births and terminal completion | A starts in the declared birth family; later births add independent READY coordinates and sources. Completion discharges enabled jumps and every token due at the horizon | `BirthState` plus the headline's READY-auxiliary/source premises; [HybridStagedBirth](../proof/lean/KernelR/HybridStagedBirth.lean): `Newborn`, `BirthStep`, `StagedExecution`; `CompleteThrough` |

## Threshold contacts and upward crossings

The [written model](../kernel/README.md#main-unit) specifies first upward
crossings for FIRE and MARK. The native operational definitions `Jump.fire`
and `Jump.mark` enable jumps at threshold equality, while `Flow.guards`
requires strict preguards. The distinction is now resolved for the constructed
finite-chain protocol by a separate geometric semantics and a proved
correspondence; the definitions of the physical kernel are unchanged.

[HybridCrossingExecution](../proof/lean/KernelR/HybridCrossingExecution.lean)
defines `CrossingExecution` using the same integral ODE, parameters, modes,
raw pulses, queue and physical jump updates. Its underlying `WeakFlow` permits
READY charges to touch one without firing. A FIRE or MARK requires both:

- `CrossingLeft`: a genuine interval in the recorded execution history on
  which the charge approaches the contact strictly from below;
- `CrossingRight`: an incoming-mode ODE continuation of the contact cell whose
  charge is strictly above one on a right neighborhood of the contact.

The right continuation solves the equations of **all coordinates of that
cell**, including gains, recovery and energy. It is counterfactual after the
contact: threshold guards and other pending events do not truncate it.
Crossing is defined geometrically, without assuming a positive derivative.
A tangent touch followed by a return below the threshold does not meet the
right-crossing condition. `CrossingCompleteThrough` resolves precisely the
jumps enabled by both historical and right-crossing conditions, including
those at the horizon; it does not assume saturation of every equality guard.

`CellRightCrossing` is an **existential** condition: some full-cell
`CellOrbitGerm` continues above threshold. The development does not supply a
generic uniqueness theorem for these germs. At a threshold contact with
positive incoming field, however,
[`CellOrbitGerm.crossing_of_positive_field`](../proof/lean/KernelR/HybridCellOrbitGerm.lean)
applies to every germ. Thus the right-crossing conclusion at the protocol's
proved transverse contacts is independent of which germ witnesses existence.
The general existential convention remains a semantic review obligation.

The proof proceeds through the following independently checked bridges:

| Bridge | Formal result |
|---|---|
| Scalar response contacts have positive slopes | [HybridPulseTransversality](../proof/lean/KernelR/HybridPulseTransversality.lean) and the five `_transversal` response lemmas |
| Actual incoming FIRE/MARK fields are positive throughout the constructed witness | [HybridContactTransversality](../proof/lean/KernelR/HybridContactTransversality.lean), `ConstructedBirthCadenceChain.contacts_transversal` |
| Full local ODE continuations exist, including active actuators and closed caps | [HybridCellOrbitExistence](../proof/lean/KernelR/HybridCellOrbitExistence.lean), `PhysicalInvariant.cell_orbit` |
| Weak and native integral paths agree | [HybridWeakFlowStrictification](../proof/lean/KernelR/HybridWeakFlowStrictification.lean), `Flow.path_unique_weak` |
| Every competing weak prefix of this protocol is a native history with the exact same paths and jumps | [HybridWeakNativeRefinement](../proof/lean/KernelR/HybridWeakNativeRefinement.lean), `WeakExecution.toNative_of_transverse_completion` |
| Geometrically complete model histories refine to complete native histories | [HybridCrossingCorrespondence](../proof/lean/KernelR/HybridCrossingCorrespondence.lean), `CrossingExecution.toNative_complete` |

The scalar positive-slope argument uses the damped derivative equation and a
strictly higher later response value. The deadlines 9/10, 13/50 and 1/40 lie
strictly before raw expiry at pulse age 1. The scalar formula after contact is
a READY continuation, rather than the actual post-jump trajectory. The field
bridge retains the true raw origin and gain and uses a contact strictly before
expiry. The full-cell germ construction separately handles raw starts and
expirations at its initial date by the pulse's right-hand behavior.

The converse does not follow from endpoint uniqueness alone. The proof uses
strictly delayed routing, queue urgency, simultaneous-jump diamonds and
transverse completions to derive strict guards for each competing weak flow.
Strict delay is derived from the protocol's existing wire hypotheses. No
contact certificate, reaching trace, output calendar or stronger terminal
saturation is an input from the competing model execution.

[`CrossingChainHeadline.every_finite_chain_every_crossing_execution`](../proof/lean/KernelR/CrossingChainHeadline.lean)
constructs a genuine crossing witness and transfers the physical endpoint,
ordered per-cell FIRE dates, FIRE counts and prescribed wire errors to every
geometrically complete model execution. Its birth, box, source and budget
hypotheses are the original finite-chain hypotheses. Conversely, every complete
native outcome has a crossing representative with the same physical endpoint
and ordered FIRE lists; simultaneous-event presentations can differ.

[HybridCrossingProgress](../proof/lean/KernelR/HybridCrossingProgress.lean)
also gives exact native refinement of every finite weak prefix at any date
and a genuine crossing continuation to any later finite horizon, preserving
the original history. The maximal infinite-run theorems retain their native
`InfiniteExecution` interface. The correspondence is scoped to this protocol;
it does not identify first contact with upward crossing for arbitrary
unrelated initial states or parameter choices.

### Descending guards

The remaining mode transitions keep urgent equality guards: FAST ends at
q=1/4, SLOW reopens at q=1/10, and MARK→SILENT→ERROR→READY occurs at
mₚ=4/5, 1/10 and 1/40. These are unambiguous downward crossings in the physical
family: q′=−a q in FAST with a=ln4>0, q′=−b(t)q in SLOW with
b(t)≥b_birth≥2/25−1/100000=0.07999>0, and mₚ′=−L_mode,p mₚ with positive
rates in each non-READY auxiliary mode. All these thresholds are positive, so
the incoming derivative is strictly negative there. The recovery lower bound
includes the birth tolerance; monotonicity and its preservation are proved by
`Execution.recovery_nondecreasing` and `Execution.recovery_birth_bounds` in
[HybridInvariants](../proof/lean/KernelR/HybridInvariants.lean). Thus retaining
strict preguards and urgent equality for these descending sections introduces
no tangent-touch ambiguity under these hypotheses. `WeakBeforeGuards` changes
only the upper READY guards. The [review guide](../REVIEW.md) identifies the
separate human obligation to validate the crossing convention against the model.

## Constructed finite-chain result

[`FixedDelayChainHeadline.every_finite_chain_fixed_delay`](../proof/lean/KernelR/FixedDelayChainHeadline.lean)
takes the admissible delay functions as inputs and returns complete native and
crossing witnesses, together with universal observations and outcomes for
both semantics. Its conclusion names
[`canonicalFiniteChainRouter n delay T`](../proof/lean/KernelR/HybridFiniteChainCanonicalRouter.lean).
`ConstructedBirthCadenceChain.router_eq_canonical` identifies the factory's
router with that declared topology and contact window.

The separate [indexed-error headline](../proof/lean/KernelR/UniversalChainHeadline.lean)
constructs the common-birth directed-chain protocol for every positive finite
N, K≥4N+12, independent fixed parameter/birth choices and arbitrary prescribed
per-emission wire errors with cumulative budget≤0.15. It constructs fixed
native delay functions bounded at every real time. All cells are born at 0,
prepare with 16 period-eight inputs, and the leaf receives K port0 sources
from 160. The full source program is already present at birth.

At T=160+4(K−1)+1.1(N−1)+8, **every complete finite execution** from those
same birth data with that fixed router is READY/q=0.1, with no RAW or pending
token, active log-gain own birth+2.4, recovery own birth+0.3, and the same
ordered actual FIRE dates per cell. The factory constructs a complete witness,
so the universal class is nonempty. The fixed router covers preparation and
cadence; [`finiteChainPreparedData`](../proof/lean/KernelR/HybridFiniteChainPreparedData.lean)
defines its declared sources and contacts.

**Learning-section counts are witness-only.** For this constructed witness,
[`ConstructedBirthCadenceChain.exact_section_counts`](../proof/lean/KernelR/HybridFiniteChainDoseCounting.lean)
constructs actual whole-execution covers: +2.4 equals four full exposed ERROR
sections on each active port, and +0.3 equals three protected MARK sections
summed over each cell's ports. The leaf has one additional preparation ERROR
on port 1. Cover existence is asserted for the witness; the universal
comparison above transfers its memories and FIRE dates to competing complete
traces without asserting covers for those traces.

| Universal comparison step | Lean proof |
|---|---|
| Same physical integral flow, including cap contacts | [HybridFlowUniqueness](../proof/lean/KernelR/HybridFlowUniqueness.lean): `Flow.path_unique`, using scalar integral barriers |
| All nine simultaneous jump types commute observationally | [HybridJumpLocalDiamond](../proof/lean/KernelR/HybridJumpLocalDiamond.lean): `Jump.local_diamond`, modulo pending-list permutation |
| Every complete finite trace has the same physical endpoint and FIRE dates per cell | [HybridUniversalExecution](../proof/lean/KernelR/HybridUniversalExecution.lean): `Execution.observational_unique`, `Execution.emissionTimes_unique` |
| Prescribed errors on every actual fast sender list | [HybridUniversalBirthCadenceChain](../proof/lean/KernelR/HybridUniversalBirthCadenceChain.lean): `all_complete_errors`, after dropping 14 leaf /12 relay preparation FIREs |

`CompleteThrough e T` requires the terminal date T, no enabled terminal jump,
and every pending token strictly future. The comparison quantifies over
finite traces in that class. The [progress theorems](../proof/lean/PROGRESS.md)
additionally extend every legal finite prefix of the same fixed finite-source
program to a complete execution at any horizon at or after its endpoint.
The physical-event non-Zeno bound rules out infinitely many physical jumps
in bounded time under birth, physical-box and bounded-fanout hypotheses.
Every infinite presentation of that program maximal under extension at a
flow limit progresses beyond every finite horizon. Time can advance by quiet
flow after source exhaustion. Flow subdivisions and the global ordering of
simultaneous independent events may differ.

The earlier [three-cell headline](../proof/lean/KernelR/Headline.lean) retains
its distinct staged 0/160/480 births, horizon 789.9 and A54/B61/C34. Operational
drift/noise, frozen probes/settings copies, numerical observations and A22
retain their separate [coverage boundaries](../proof/lean/N_CELL_COVERAGE.md).
