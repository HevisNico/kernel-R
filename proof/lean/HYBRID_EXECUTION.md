# Physical execution semantics and analytic refinement

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
[EVERY_N_PLAN.md](EVERY_N_PLAN.md).

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
[construction/validation ledger](EVERY_N_PLAN.md). Retained probes,
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
`Classical.choice` and `Quot.sound`. The [validation ledger](EVERY_N_PLAN.md)
records the successful complete frozen-source build and global audit.
The reviewed universal proof modules are included in this checkout. The
[historical release checklist](../../docs/RELEASE_UNIVERSAL_FINITE_CHAIN.md)
records the v0.2.0 integration and publication scope; later local validation is
recorded in the [current ledger](EVERY_N_PLAN.md#validation-and-checkpoint-discipline).

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

## Constructed protocol checkpoint

The current original-birth protocol factory is
[`birth_protocol_complete_cadence_exists`](KernelR/HybridBirthCadenceProtocol.lean).
It returns `ConstructedBirthCadenceProtocol`, retaining both actual births,
the two-cell phase between them and a complete three-cell phase480→789.9. Its premises are A's READY birth/source family, independent READY B/C newborns, fixed independent physical
parameters and five bounded delay functions. There is no reaching execution,
received calendar, prescribed dose/count or assumed firing date. Earlier
factories remain available independently.

| Constructed checkpoint | Derived state and traffic | Public factory / source |
|---|---|---|
| Initial preparation, 128 | A12; prepared READY, q=0.1, no RAW; ERROR1.8/MARK0.1; sixteen future A sources retained | `birth_protocol_preparation_exists` in [HybridBirthPreparationExists](KernelR/HybridBirthPreparationExists.lean) |
| B birth and A160 delivery | A's acquired memories retained; B has its own independent newborn coordinates; 47 future external sources | `birth_protocol_b_birth_complete_exists` in [HybridConstructedBBirth](KernelR/HybridConstructedBBirth.lean) |
| First B output, (169.1,170.2) | Actual interleaved A/B execution; B's output retained under the closed reverse contact | `birth_protocol_first_receiver_fire_exists` in [HybridConstructedReceiverFire](KernelR/HybridConstructedReceiverFire.lean) |
| Common prepared section, 184 | Both q=0.1; B has full MARK0.1; fresh A184 RAW; 44 external sources | `birth_protocol_first_coupled_prepared_pair_exists` in [HybridFirstCoupledPreparedPair](KernelR/HybridFirstCoupledPreparedPair.lean) |
| Complete first teaching, 319.9 | Cumulative A28/B14; both prepared, no RAW; all 32 B sources retained | `birth_protocol_first_coupled_teaching_exists` in [HybridFirstCoupledTeaching](KernelR/HybridFirstCoupledTeaching.lean) |
| Fresh reciprocal input, 344 | Three actual Bport2 weak cycles, ERROR1.8, no new output/MARK; B's true q>=0.1; 28 future sources | `birth_protocol_feedback_weak_entry_exists` in [HybridFeedbackWeakEntry](KernelR/HybridFeedbackWeakEntry.lean) |
| First reverse FIRE, F in (344.3,344.9) | Cumulative A28/B15; A remains at q=0.1; reverse Aport2 token due at F+backward(F); 29 pending tokens | `birth_protocol_feedback_first_fire_exists` in [HybridFeedbackFirstFire](KernelR/HybridFeedbackFirstFire.lean) |
| First reverse receipt, H in (344.7,345.3) | The actual B-issued Aport2 wire is consumed; A has fresh RAW at H; B's true sender cut is retained; A28/B15 and28 external sources | `birth_protocol_first_reverse_wired_arrival_exists` in [HybridBirthFirstReverseArrival](KernelR/HybridBirthFirstReverseArrival.lean) |
| Interleaved source handoff, 352 | Real A weak response and B FAST/SLOW return; actual B352 source consumed; A28/B15, own Aport2+0.6/Bport2+1.8 and27 sources | `birth_protocol_first_reverse_interleaved_pair_exists` in [HybridBirthFirstReverseInterleavedPair](KernelR/HybridBirthFirstReverseInterleavedPair.lean) |
| Complete reciprocal epoch, 459.9 | Cumulative A38/B27; both prepared/q=0.1, RAW absent; own Aport2/Bport2+1.8 and sixteen B480..600 sources retained | `birth_protocol_reverse_teaching_exists` in [HybridBirthReverseTeaching](KernelR/HybridBirthReverseTeaching.lean) |
| Genuine C birth and B480 delivery | Independent C newborn; A/B coordinates retained;41 tokens after birth,40 after actual B480 arrival | `constructed_c_birth_exists` in [HybridConstructedCBirth](KernelR/HybridConstructedCBirth.lean) |
| First C weak response, 488 | Own Cport1+0.6, recovery unchanged; true weak cut and continuation retained; actual B488 delivered,39 sources | `c_weak_entry_exists` in [HybridCWeakEntry](KernelR/HybridCWeakEntry.lean) |
| First C learned response, 496 | Real C FIRE and low-recovery SLOW path retained; B496 fresh,38 sources | `c_first_learned_boundary_exists` in [HybridCFirstLearnedBoundary](KernelR/HybridCFirstLearnedBoundary.lean) |
| Common B/C prepared section, 504 | Protected C MARK0.1, own gain retained; both prepared, fresh B504,37 sources | `c_prepared_pair_exists` in [HybridCPreparedPair](KernelR/HybridCPreparedPair.lean) |
| Complete C teaching, 639.9 | Cumulative A38/B43/C14; all prepared/q=0.1, no RAW; exact25 C640..736 sources | `birth_protocol_c_teaching_exists` in [HybridBirthCTeaching](KernelR/HybridBirthCTeaching.lean) |
| Fresh cadence source, 652 | Three actual period-four weak C inputs; own Cport0+1.8, no MARK, carried q in[0.1,0.3]; A/B quiet and21 future C sources | `constructed_cadence_warmup_exists` in [HybridBirthCadenceWeakWarmup](KernelR/HybridBirthCadenceWeakWarmup.lean) |
| First cadence wire, H in(652.7,653.3) | Actual C FIRE and C-to-Bport2 arrival; cumulative A38/B43/C15, B fresh RAW, exact C FAST cut and21 C656..736 sources | `birth_protocol_cadence_first_wire_exists` in [HybridBirthCadenceFirstWire](KernelR/HybridBirthCadenceFirstWire.lean) |
| First relay receipt, H_A in(653.4,654.4) | Actual B FIRE issues the Aport2 token, actual arrival consumes it; A prepared/fresh RAW, B/C retained physical cuts, exact21 C sources | `first_cadence_relay_wire_exists` in [HybridCadenceFirstRelayWire](KernelR/HybridCadenceFirstRelayWire.lean) |
| First cadence wave, F_A in(653.8,655.1) | Actual A FIRE; cumulative A39/B44/C15; A FAST/q=1, B/C actual cuts and continuations, exact21 C656..736 sources | `birth_protocol_cadence_first_wave_exists` in [HybridBirthCadenceFirstWave](KernelR/HybridBirthCadenceFirstWave.lean) |
| First protected source, 656 | Actual C656 arrival; C remains SLOW with its true charge, A/B actual cuts and20 future C sources | `first_cadence_mark_source_exists` in [HybridCadenceFirstMarkSource](KernelR/HybridCadenceFirstMarkSource.lean) |
| First protected MARK return, 660 | A39/B44/C15; C READY/q=0.1/RAW660, own recovery+0.2 and port0 log-gain+1.8; A/B retained cuts and19 C664..736 sources | `birth_protocol_cadence_first_mark_return_exists` in [HybridBirthCadenceFirstMarkReturn](KernelR/HybridBirthCadenceFirstMarkReturn.lean) |
| Complete three-cell cadence, 789.9 | Cumulative A54/B61/C34; cadence A16/B18/C20; all READY/q=0.1, RAW absent, global queue empty; own active log-gains+2.4 and recoveries+0.3 | `birth_protocol_complete_cadence_exists` in [HybridBirthCadenceProtocol](KernelR/HybridBirthCadenceProtocol.lean) |

At 319.9 A retains its own birth port0 log-gain+1.8 and recovery+0.1;
B retains its own newborn port1 log-gain+0.6 and recovery+0.1. All other gains
are unchanged. B's remaining queue is exactly the two port2 source trains
320..440 and 480..600, each with sixteen inputs spaced by eight. At 344 its own
port2 log-gain has increased by1.8. The FIRE extension preserves memories and
recovery; its queue contains B352..440 (twelve), B480..600 (sixteen) and the
single newly issued reverse token. Its actual receipt then removes that wire.
At352 the subsequent B source has also been consumed: the exact remaining
queue is B360..440 (eleven sources) followed by B480..600 (sixteen), with no
unconsumed reverse wire. A's port2 log-gain is its own birth value+0.6; B's
port2 log-gain is its own independent newborn value+1.8. The previously
acquired Aport0/Bport1 gains and both recoveries are retained.

### How the execution is constructed

Fixed-mode constructors solve the actual integral equations, retaining the
current charge, per-port memories, reserve and raw origins. Their energy
bounds include input, main and auxiliary work and establish positive reserve
before forming a valid `Flow`. ERROR restarts use the remaining dose
`8*(m-0.025)`, not a fresh full dose after an intermediate cut. Coincident
exponential rates are covered.

The first weak cycles at 0,8,16 derive the first output at the source24 input.
The true FAST exit occurs at FIRE+1 with q=0.25. The source32 input arrives
while SLOW; its protected MARK uses the finite recovery ramp in the main ODE,
not an instantaneous recovery jump. The subsequent real SLOW return reaches
q=0.1 and permits source40. Learned-source iteration reaches128, with every
remaining second-train token retained. The actual birth at160 preserves A's
state and queue while adding B's independent state and sources.

Multicell products cut and resume original flow paths at actual event dates.
Neutral jumps preserve the separate global queue. An emitting local trace is
lifted by genuine global FIRE jumps, preserving its emission ledger. The
interval-scoped left/right products require contact closure only on the
emitter's actual time span. Open historical contacts therefore do not create
a false global-closure premise. Issued wire tokens use the actual firing time
and sampled delay; receipt removes that exact occurrence.

At the common prepared section184, `coupled_learned_cycle_exists` constructs
one A output, its Bport1 wire receipt, B's short learned cycle and both returns.
B's real response is before input+0.7 and its prepared return before input+6.8;
a complete short cycle reaches input+6.9. The forward delay is at most0.4,
so this fits before the next A source eight units later. The train constructor
iterates thirteen cycles for sources184..280, then a real quiet flow reaches
319.9. Each wire is issued and consumed by actual global events. No ERROR or
MARK is added on this learned extension.

The reciprocal constructor performs the real B320/328/336 weak cycles and
B344 arrival without resetting the residual main charge. The first learned
latency is at most B's own same-gain resting latency; equality is not asserted.
A positive backward delay leaves the issued reverse token strictly in the
future, proving saturation at the FIRE cut. At a source boundary with a token
due now, the caller must perform its actual arrival before claiming
`CompleteThrough`; reaching a date alone is insufficient.

### Actual reverse receipt and source352 handoff

The first-receipt and352 checkpoint uses these modules: `HybridPortFastCompletion`,
`HybridFeedbackFireProjection`, `HybridFeedbackSenderFastEnd`,
`HybridPrefixStableMemory`, `HybridQuietLeftWireArrival`,
`HybridFirstReverseWiredArrival`, `HybridFeedbackSenderReturn`,
`HybridFirstReverseInterleavedPair`, `HybridFirstReverseInterleavedMemory`,
`HybridBirthFirstReverseArrival` and `HybridBirthFirstReverseInterleavedPair`.

The actual global FIRE projection supplies B's FAST/SILENT coordinates,
SILENT-entry clock, sensor floor dates and RAW origin344. The port-generic
constructor performs the real auxiliary transitions, RAW expiry and FAST
exit at F+1. A maximal cut of that same path at H=F+backward(F) retains
coincident events and its remaining execution. The real root gives F>344.4;
bounded backward delay therefore yields H in(344.7,345.3). A remains at exact
rest until an actual arrival consumes the unique B-issued Aport2 token.
The next retained sender flow proves saturation at that receipt. No reaching
execution or received calendar is supplied by the original-birth factory.

B's actual SLOW return reopens at q=0.1, reaches a prepared section by351.5
and waits physically to352. A's first received weak cycle is constructed
through H+7.5 and cut maximally at352, with its true continuation retained.
The two real paths are woven with the separate global queue unchanged.
Only after reaching352 does an arrival consume the actual next B source.
This suffix adds no output and has exactly the B352 delivery.

At352, B is prepared/q=0.1 with fresh port2 RAW352. A is main READY, its
auxiliaries are READY in their rest bands, RAW is absent and its actual
charge is at least0.1. Its exact cut and continuation to H+7.5 remain in the
witness; no A `PreparedSection` or reset to q=0.1 is asserted at352. A's
ERROR0.6 on port2 is derived, with ERROR zero on its other ports and every B
port. Both cells' total recovery contributions on this suffix are zero.
The own-memory equalities, A28/B15, exact27-source queue and
CompleteThrough352 follow from the original-birth factory.

### Constructed complete reciprocal epoch

Thirteen modules extend the352 checkpoint. `HybridPortWeakCut` constructs a port-generic weak response and retains its
actual interior cut and continuation. Its later READY/prepared band follows
from the remaining charge solution and `relax_restart`. It does not replace
the carried charge or assert equality of endpoint energies.

`HybridFirstReverseNextWire`, `HybridReverseWeakStep` and
`HybridReverseWeakNextWire` extend the same actual352 state through B's next
source responses and real reverse receipts through `HybridReverseSourceWire`.
`HybridReverseLatencyGeometry`
uses the first residual latency bound and equal own gains at later exact-rest
sources to derive the first received gap at least7.9 and regular gaps in
[7.9,8.1]. These bounds permit A's real weak return before the next receipt,
even when its cut at a B source is outside the prepared charge band.

`HybridReverseEntryCompletion` constructs the remaining weak A inputs,
B368's actual FIRE and wire, A's first learned FIRE from its true residual,
and both guarded returns using `HybridReverseLearnedReturn`. It consumes the actual B376 source and reaches
that common prepared section with one new A output, three new B outputs
and only the declared future sources384..440 and480..600 pending.

`HybridReverseCoupledLearnedCycle`, `HybridReverseCoupledLearnedTrain` and
`HybridReverseLearnedEpoch` construct nine real coupled cycles from the
active B376 input and its eight queued successors384..440. Every B FIRE
issues its own Aport2 token, its actual receipt consumes it and A's real
FIRE remains in the ledger under its closed route. Both cells return before
the next B source; a source due exactly at the cycle endpoint is consumed
before terminal saturation is asserted. The train reaches448, then a real
quiet flow reaches459.9 without an output or delivery.

`HybridReverseTeachingCompletion` composes this352-to459.9 suffix, with
A10/B12 new outputs. `HybridBirthReverseTeaching` connects it to the original
birth trace: cumulative **A38/B27**, both prepared at q=0.1 with RAW absent,
physical invariants and `CompleteThrough459.9`. The exact pending queue is
Bport2's sixteen sources480..600. A retains its own birth log-gains+1.8 on
ports0 and2; B retains its own newborn log-gains+0.6 on port1 and+1.8 on
port2. Other gains are unchanged and each recovery is its own birth value+0.1.

### Constructed C birth and teaching

Twenty new Lean modules extend the459.9 checkpoint to639.9.
`HybridConstructedCBirth` waits physically from459.9 to480, performs C's
genuine independent `BirthStep`, and consumes B480. The birth adds Cport0's25
sources640..736; A/B's sixteen B480..600 sources are retained before the actual
B480 arrival. `HybridCBirthActivePair` projects the active B/C pair while
preserving a physically quiet A through `HybridQuietHeadExecutionProduct`.
C is READY with recovery near0.08; no prepared recovery band is assumed at birth.

`HybridPortSourceWire` constructs arbitrary-port source-to-receiver contacts.
`HybridReadyWeakCut` uses C's actual READY coordinates and narrow weak-gain
bound, retaining the true weak response and its remaining charge solution.
`HybridPortWeakStep` and `HybridCWeakEntry` reach488, deriving exactly one
ERROR0.6 on Cport1 and consuming B488. They retain the residual charge and
unchanged newborn recovery. `HybridGuardedPortSourceWire`, `HybridCSecondWire`
and `HybridCFirstLearnedBoundary` then construct the next actual wire and C's
first learned FIRE, reaching the B496 source with C's real SLOW path retained.

`HybridPortFirstLearnedCut` and `HybridLowRecoverySlowSpanExtension` retain
that exact low-recovery path, including its legal endpoint cuts. The next
B-issued wire is consumed while C remains SLOW by `HybridPortSlowWire`.
`HybridPortProtectedReturn` performs C's protected auxiliary MARK with the
actual varying recovery in the main ODE. `HybridCPreparedPair` reaches504:
B is prepared with fresh port2 RAW; C is prepared with its own recovery+0.1,
own port1 log-gain+0.6 and no new gain on ports0/2. The queue is exactly12
future B512..600 sources followed by25 C640..736 sources.

`HybridPortCoupledLearnedCycle` and `HybridPortCoupledLearnedTrain` construct
thirteen real Bport2-to-Cport1 learned cycles from the active504 input and
its12 queued successors. Every B FIRE issues a real wire; its actual receipt
and C's actual FIRE remain in the execution. Each cycle returns both cells
before the next period-eight source, preserving every gain and recovery.
`HybridCLearnedEpoch` reaches608, then waits physically to639.9.
`HybridCTeachingPair` composes16 new B outputs and14 C outputs. Finally,
`HybridBirthCTeaching` lifts the same B/C path alongside quiet A and composes
the original staged births: cumulative **A38/B43/C14**, all three prepared at
exact q=0.1 with RAW absent, physical invariants and `CompleteThrough639.9`.
The exact pending queue is Cport0's25 sources640..736. Every old A/B gain and
recovery is retained, while C's gains and recovery are measured from its own
independent newborn coordinates.

### Constructed first cadence wire

`HybridConstructedCadenceStart` waits physically to640 and consumes the actual
first Cport0 source. `HybridCadenceWeakStepExistence` and
`HybridConstructedCadenceWeakWarmup` construct the three period-four weak
responses640/644/648, their actual returns and the fresh652 arrival.
`HybridBirthCadenceWeakWarmup` lifts that same path beside physically quiet
A/B using `HybridQuietHeadNeutralProduct`. Neutral lifting permits the open
global C-to-B contact because the actual warmup emits nothing. It preserves
the true queues, sensor/energy paths and own memories. C's own port0 log-gain
gains1.8, ERROR is zero elsewhere and every MARK/recovery contribution is zero.
The successive charge bounds reach0.3; no period-eight charge reset is used.

`HybridCadenceResidualRootBounds` proves a strict response upper bound at most
0.998 through0.4 for gain at most1.9 and carried q at most0.3.
`HybridResponseMarginInput` and `HybridCadenceFirstStrongFireExistence`
use that margin to construct C's actual first FIRE F in652+(0.4,0.9).
`HybridPortFastCompletion` supplies its real post-FIRE FAST path, with true
auxiliary transitions and raw expiry on either side of the possible receipt.

`HybridCadenceFirstWire` lifts the neutral pre-FIRE path, performs the genuine
global C FIRE and appends its exact Bport2 wire token. Only the already-issued
token is framed into the retained post-FIRE path by `HybridNeutralFutureFrame`.
The original sender flow is cut at H=F+delay(F), and an actual arrival consumes
that occurrence. B has prepared coordinates at q=0.1 and fresh port2 RAW at H;
A remains prepared at q=0.1 with RAW absent. C retains the same actual FAST
cut, including all coordinates, modes, raw state and energy path, plus its
remaining execution. The receipt window straddles the source652 raw expiry
at653; the cut retains the actual raw state in either case. No all-cells-prepared or all-RAW-absent endpoint is asserted.

`HybridBirthCadenceFirstWire` connects this receipt to the original birth
construction: cumulative **A38/B43/C15**, `CompleteThrough` at H in(652.7,653.3),
and exactly 21 Cport0 sources656..736 pending. Apart from Cport0's weak gain1.8,
all gains and every recovery remain as at639.9, measured from the same own births.

### Constructed first C→B→A wave

`HybridCadenceStrongSlowSpan` constructs the first C FIRE's actual FAST exit
and subsequent SLOW flow through656. It uses C's own recovery near0.18 and
three-dose gain at most1.9, derived from the same warmup coordinates. Its
`fromCut` resumes the very flow retained at the first wire receipt, preserving
the true energy and charge paths. The source656 token remains pending.

`HybridCadenceFirstRelayWire` constructs B's short learned response from the
actual first receipt. B's real FIRE issues an Aport2 token at its own sampled
backward delay. Neutral products weave B's pre-FIRE and FAST prefixes with
the retained C path and quiet A. The framed post-FIRE queue is identified with
the true global FIRE result, then an actual arrival consumes the exact A token
at H_A in(653.4,654.4). A is then prepared at q=0.1 with fresh RAW; B/C keep
their actual cuts and remaining executions. Own gains/recovery and the21-source
C queue are preserved.

`HybridCadenceFirstAFire` constructs A's actual learned FIRE from that receipt
and its own retained port2 gain. `HybridNeutralHeadExecutionProduct` weaves
A's pre-FIRE path with the same B/C continuations without requiring A to be
quiet. A genuine global FIRE at cell0 ends the first wave; its cadence route
is empty. `HybridBirthCadenceFirstWave` composes the original births, both
actual wires and all three FIREs: cumulative **A39/B44/C15**, endpoint F_A
in(653.8,655.1), `CompleteThrough` and exactly 21 C656..736 sources pending.
A is FAST at q=1. B/C remain at their actual cuts, with modes, raw state,
energy and continuations retained. The wave adds no ERROR or MARK: all gains
remain as at the first C-to-B receipt and each recovery remains its own birth
value+0.1. Cport0's earlier weak ERROR1.8 is retained.

### Constructed first protected MARK return at660

`HybridCadenceFirstMarkSource` retains A/B's actual continuations and resumes
the same C SLOW span to656. Its neutral products keep the exact global source
queue and all physical residue. A real arrival consumes C656, leaving20 C
sources660..736, while C remains SLOW at charge in[37/250,1/4], with READY
resting auxiliaries and fresh RAW656. A/B are kept at their own actual cuts;
no common prepared section is imposed.

`FirstCadenceMarkReturn` and `first_cadence_mark_return_exists` compose C's
actual protected MARK, guarded SLOW return and C660 arrival alongside those
same A/B paths. C is READY at q=0.1 with fresh RAW660, recovery equal to its
own newborn value+0.2 and unchanged own port0 log-gain+1.8. The suffix adds
MARK0.1 on Cport0, no ERROR anywhere and no emission. A/B retain their actual
cuts, modes, raw state, energy and continuations; their gains and recoveries
are unchanged. A joint prepared endpoint is not required.

`HybridBirthCadenceFirstMarkReturn` connects this suffix to the original births
through `birth_protocol_cadence_first_mark_return_exists`: cumulative A39/B44/C15,
exactly 19 C664..736 sources, physical bounds, raw validity and
`CompleteThrough660`, including the actual source due at660.

### Constructed autonomous C through789.9 and its leaf packet

`c.local_c_full_exists hb` in
[HybridBirthCadenceLocalC](KernelR/HybridBirthCadenceLocalC.lean) constructs
`ConstructedCadenceLocalC c` from the actual original-birth witness at660 and
its physical parameter box. No reaching local execution or desired calendar is
supplied. `HybridAutonomousCellProjection` projects C's actual639.9→660 global
execution because the cadence router has no incoming contact to C. It retains
C's exact coordinates, modes, RAW origins, energy, selected source queue and
actual ERROR/MARK, delivery and emission observations. Irrelevant other-cell
jumps are omitted; the projection is an actual one-cell execution with empty
routing, rather than an operation that deletes any global queue.

`HybridBirthCadenceLocalCTail` attaches `HybridLocalCadenceTail` to that exact
660 C endpoint. The tail constructs the second strong response to664, the
mixed protected MARK/ERROR response to668, and `HybridLocalCadenceHighTrain`
through the final source736 and READY return740. A true quiet flow reaches789.9.
`HybridCadenceHighCompletion` exposes its actual READY-return prefix, RAW,
memory and ledger observations; no charge or energy reset is used.

The full local execution consumes exactly the 25 Cport0 sources640..736 and
emits exactly 20 cadence signals. With the 14 prior teaching signals, C's
cumulative count is34. At789.9 it is READY with q=0.1, no RAW and an empty local
queue, with physical bounds and `CompleteThrough`. Its port0 log-gain is its
own newborn value+2.4, its recovery is its own newborn value+0.3, and its other
gains retain their teaching values. This is a C endpoint, not a later A/B/C
network endpoint.

`HybridConstructedCadenceLeafPacket` defines `full.leafPacket : Packet 3 17 0`
and proves its 20 actual dates equal `full.execution.emissionTimes 0`. The
three prefix dates are the actual first strong, second strong and first
high-gain FIREs; the 17-date tail uses C's own fixed high-gain latency.
For any delay function in[0.3,0.4], `full.receivedLeafPacket` has type
`Packet 3 17 (1/20)` and each date is F+delay(F), sampled at that actual FIRE.
`leafTokens` gives the corresponding Bport2 token labels with real emission
provenance. It does not preload the global queue or assert later global
arrivals. `issued_leaf_tokens` identifies actual issuance only for a supplied
global execution preserving that calendar and the declared routing.

### Projected one-cell learned-domain bridge

`HybridBirthLearnedRest` proves that Aport2/Bport2 coordinate projections of
the actual639.9 endpoint satisfy `LearnedRest`. Exact q=0.1, READY modes,
RAW absence, sensor bands, reserve/caps and recovery come from the constructed
endpoint. Their own birth gains+1.8 yield the narrower active range[1.8,1.9].
Cport1's learned gain near2.18 is outside that range and has no such wrapper.
The resulting actual isolated `PulseContract`s settle in7.5 and give complete
prefixes at every finite future horizon with newly supplied isolated sources.
The empty analysis queues do not physically remove any global C source token;
this is domain membership of projections, not a network continuation theorem.

### Constructed global C→B→A cascade

`HybridConstructedCadenceBC` consumes the ledger-derived C packet
P(3,17,1/20) with a physical B receiver. B emits exactly18 signals, whose real
ledger yields P(5,13,1/20). The next bounded wire gives A's packet
P(5,13,1/10), and its physical receiver emits exactly16 signals.
`HybridCausalHeadQueue`, `HybridCausalHeadJump`, `HybridCausalHeadExecution`,
`HybridCausalHeadBalance`, `HybridCausalHeadComplete` and `HybridCausalHeadSignals`
weave these isolated witnesses into genuine routed executions. The global
initial queue contains only C's 25 external source occurrences, and each
receiving token is issued by its sender's actual FIRE. The isolated receiver
queues are matched by conservation; they are not preloaded global wire tokens.

`HybridConstructedCadenceCascade` returns the complete global639.9→789.9 trace
with cadence counts A16/B18/C20, all READY/q=0.1, RAW absent, physical/raw
invariants, an empty global queue and `CompleteThrough789.9`.
`HybridBirthCadenceCascade` connects this to the original births and derives
cumulative A54/B61/C34. Active own log-gains A2/B2/C0 each gain2.4 and own recoveries
each gain0.3; other gains preserve their639.9 values.

`HybridEmissionRouterTransport` retargets an actual trace when the routed token
lists agree at each real FIRE, preserving both endpoints, complete ledger and
deliveries. `HybridTeachingCadenceRouter` combines the B→C teaching gate
[480,630) and C→B/B→A cadence gates[640,780) in one fixed three-cell router.
`HybridBirthCadenceProtocol` retains the same actual C birth and joins the
teaching/cadence phases as its `staged.after` under that fixed law. Its
`betweenBirths` joins the true two-cell execution after B160 to C480, while
the earlier A phase and B birth remain in the retained original staged witness.
The protocol's cumulative54/61/34 theorems count this actual staged execution,
with the ledger and delivered occurrences preserved by retargeting.

### Current boundary

The declared physical N=3 cadence is constructed. The general trace-based
analytic APIs below still accept executions, while the concrete factory now
supplies one for this birth/source family. The common-birth every-N program now
also has universal physical outcomes for the fixed finite-complete class.
The common-birth program also has [finite and maximal-run progress](PROGRESS.md).
Finer operational robustness, retained probes and settings copies remain open.
The finite-chain construction is tracked in [EVERY_N_PLAN.md](EVERY_N_PLAN.md).

## Checked implications

| Module | Consequence proved from the operational equations | Boundary |
|---|---|---|
| [HybridMaximalProgress](KernelR/HybridMaximalProgress.lean) | A bounded infinite presentation extends through its final flow limit with exact path agreement. Every semantically maximal run of the constructed chain progresses past each finite horizon. | Fixed finite-source chain in the physical parameter box. |
| `HybridFlowUniqueness` | Physical integral paths agree on every overlapping flow interval, including capped gain/recovery gates and actual energy | Fixed parameter family, common starting snapshot, physical invariant |
| `HybridJumpLocalDiamond`, `HybridJumpStripping` | Enabled instantaneous jumps commute or coincide observationally, and can be stripped from a competing complete finite execution | Pending-list order may differ; no imposed priority |
| `HybridUniversalExecution` | Complete finite executions through the same T have equal physical observations and exact ordered per-cell FIRE lists | Same fixed router and initial state, `PhysicalBox` and initial `PhysicalInvariant`; no maximal/infinite-run progress claim |
| `HybridCrossingExecution` / `HybridCellOrbitExistence` | Model FIRE/MARK use the actual left history and a genuine full-cell right ODE germ, including plasticity, energy and caps | Weak READY guards permit ≤1; terminal crossing completion excludes exactly jumps satisfying both crossing guards |
| `HybridWeakNativeRefinement` / `HybridCrossingCorrespondence` / `CrossingChainHeadline` | Complete model histories refine to exact native paths/jumps and inherit the finite-chain outcomes; native completions have crossing representatives with equal observations/FIRE lists | Declared common-birth chain, unchanged birth/box/source/delay/budget inputs; no syntactic identity of all simultaneous native linearizations |
| `HybridCrossingProgress` | Every finite weak prefix refines exactly to native moves; every finite model prefix extends to any later finite horizon while retaining history | Infinite/maximal-run results retain native `InfiniteExecution`; indefinitely responding networks remain separate |
| `HybridUniversalBirthCadenceChain`, `UniversalChainHeadline` | Transfer terminal state, own memories, actual counts and prescribed errors to every complete finite trace of the constructed common-birth program | Indexed order ∀ data/errors ∃ fixed router/witness ∀ complete traces; preparation FIREs excluded from FAST indices |
| `HybridUniversalChainPreparation` | Derive relay/leaf preparation at actual128 prefixes of arbitrary larger-network executions from source queues | Contacts closed through128, exact source family and physical box; other-cell interleavings retained |
| `Refinement` | Exact per-port ERROR and MARK integrals; telescoped gain/recovery balances; recovery equals the sum of all MARK contributions; queue conservation; actual emissions | Quantifies over finite admissible executions |
| `HybridDoseCounting` | Exact whole-execution memory increments from unique natural-number counts of complete exposed ERROR and protected MARK sections; recovery sums all ports, including overlapping sections | Actual-trace section covers are hypotheses; the birth specialization retains READY auxiliary boundaries, positive energy and strictly open caps. `HybridFiniteChainDoseCounting` supplies the finite-chain witness covers under its original physical hypotheses. |
| [`HybridFiniteChainDoseCounting`](KernelR/HybridFiniteChainDoseCounting.lean) | `ConstructedBirthCadenceChain.sectionCovered` constructs whole-witness covers; `exact_section_counts` proves four exposed ERROR sections on each active port and three protected MARK sections summed over every cell's ports | Original constructed common-birth protocol and physical box; the leaf additionally has one preparation ERROR on port1. Covers for competing complete traces are not asserted by universal endpoint comparison |
| `HybridDoseCountingTools` | Construct covers by concatenating covered actual executions or by proving structural inactivity; concatenation adds their section counts | A memory or ledger equality is never a premise for constructing a cover |
| `HybridDoseCountingTransport` / `HybridSectionRouterCopy` | Port relabeling and exact-move router copies preserve real entries, exposed spans, exits and counts; router copies also preserve section runs and contact transversality | The transported execution and its physical move correspondence are constructed explicitly; equal endpoint memories alone do not establish correspondence |
| `HybridDoseCountingQueueTransport` | Future-queue framing and source restriction construct copied physical traces with the same actual flow paths and transport every port's ERROR/MARK covers | Empty routing and the stated future/cutoff conditions; source restriction is an analysis construction, not deletion of live network tokens |
| `HybridUniformSectionCovers` / `HybridSectionCoverSplice` | Reconstruct complete sections from uniform physical modes and embed already-covered phases in their actual surrounding trace | Splicing uses open-gate positivity to prove surrounding moves structurally inactive; a dose equality alone never replaces the counted phase cover |
| `HybridBirthPreparationSectionCovers` / `HybridLeafPreparationSectionCovers` | Construct low-port and leaf preparation covers from birth, including the leaf's weak ERROR and protected MARK on port1 | Original physical birth inputs; final headroom derives learning gates |
| `HybridCadenceWeakSectionCovers` / `HybridCadenceSectionCovers` / `HybridCadenceTailSectionCovers` / `HybridLeafSectionCovers` | Construct actual weak, MARK-only, mixed and terminal cadence covers before whole-chain composition | Retain genuine phase boundaries, carried state, queue framing and source occurrences |
| `HybridSectionRuns` | Open-section automata retain phase boundaries across concatenation; a closed run is equivalent to a complete-section cover with the same natural count | The open/closed state and mode validity are checked on the actual trace; a flow subdivision is not a new learning section |
| `HybridCausalSectionRuns` / `HybridCausalHeadExecution` | Causal weaving preserves head and tail section runs through physical flow cuts and interleaved foreign jumps, with unchanged counts | Local section runs must first be established; the finite-chain application composes this transport with the local cover constructors |
| `HybridErrorSectionCovers` / `HybridMarkSectionCovers` / `HybridProtocolErrorSectionCovers` / `HybridProtocolMarkSectionCovers` | Construct local complete-section covers from actual sensor entries, phase spans and departures, including weak ERROR learning and protected MARK learning | Each result retains its own mode-exposure, physical-invariant, headroom and raw-input hypotheses; the finite-chain application composes these local constructions into whole-witness covers |
| `HybridFlow` | Scalar ODE uniqueness derived from integral equations; FAST and protected-auxiliary exponential solutions; SLOW uses the integral of actual varying recovery | Observed mode spans must still be selected from the execution |
| `HybridFlow` | Exponential solutions compose across legal zero-time interleavings; observed jumps supply phase endpoints; FAST duration is 1; MARK/SILENT/ERROR durations use actual rates; SLOW returns at accumulated recovery log(5/2) | Does not establish the supplied protocol's ordering of these phases |
| `HybridFlow` | A FAST flow cannot pass its first physical exit section; zero-input READY relaxation and gate-implied constant gains/recovery | No general extension/progress theorem |
| `HybridReady` | Main and auxiliary READY responses to one active canonical input, including residual charge and attenuation from the real pulse origin; first threshold contacts agree with the analytic response | Main input gain is frozen by local absence of ERROR; variable-gain overlap and multi-input cases remain separate |
| `HybridInvariants` | Integral cap barriers; gains and recovery cannot overshoot their caps, and are nondecreasing in the fabrication family; birth-state memory bounds | Strict cap inactivity during a required complete dose is not automatic |
| `HybridBounds` | Coarse bounds on actual real log/exp expressions and independent fabrication parameters | Does not certify every stored certificate enclosure |
| `HybridRegion` | Main charge upper bound and mode-dependent auxiliary upper bounds, including m<=0.1 in ERROR, preserved from birth across flows and jumps | Port-separation/protocol-calendar results are not asserted |
| `HybridWork` | Actual work is nonnegative and <=500, derived before assuming positive reserve; reserve stays in [50,100] for every finite admissible execution from the declared family, and throughout each reachable flow | Does not supply existence of those protocol executions |
| `HybridWork` | Energy exposure in ERROR/MARK lemmas follows from reachability and the reserve invariant | Required main/auxiliary chronology and strict cap inactivity remain premises |
| `HybridEvents` | Emission dates are chronological and inside the actual execution interval; causal wiring preserves future delivery dates; FAST potential telescopes across all legal interleavings; per-cell firing count is at most T+1 from birth | A due token is allowed at the current date; port availability and progress remain separate |
| `HybridAuxEvents` | Protected SILENT decay supplies a clock; a discrete rank counts all four auxiliary transitions; at most 8T+10 auxiliary jumps per cell and port from birth, including residual ERROR | This is a coarse event budget, not a prescribed pulse-case sequence or full-dose conclusion |
| `HybridEventBudget` | Every jump is partitioned into main, auxiliary, arrival or raw-end events; queue and raw-current balances give a uniform natural budget for all finite prefixes ending by T | Requires an explicit routing fanout bound; no continuation or complete protocol execution is constructed |
| `HybridEnvelope` | READY comparison with variable physical gains, every active port and attenuation from each actual raw origin | Comparison gain bounds remain explicit; monotonicity and caps supply a general physical instance |
| `HybridClipping` | ERROR gain increase is at most eight times actual auxiliary charge loss; per-port MARK dose is at most half the loss, including closed gates; strict cap exposure follows from remaining-charge headroom | Complete dose still requires actual main-mode chronology; a real headroom lemma does not establish a dose count |
| `HybridPrefix` and `HybridPulseSpans` | Cut an actual execution using its existing flow path; preserve observed flow modes; retain raw origins; compose exact READY sensor responses across legal events | Prefixes of given executions, not future continuation constructions |
| `HybridPhases` | Select the first actual mode-changing jump and reconstruct the original execution; extract complete FAST and protected auxiliary phases | Requires starting mode/charge and a sufficiently long actual execution; existence is not asserted |
| `HybridAuxCycle` | From actual MARK entry at m=1, extract MARK, SILENT, ERROR and the READY successor, with real protected duration in [123/110,41/30] | Main-cell interactions and subsequent inputs remain separate |
| `HybridResponseBounds` | Real response bounds, including response<=3/4 in the raw window and a positive lower bound at 9/10 | Selected coarse analytic bounds, not soundness of every stored enclosure |
| `HybridSensor` | A received pulse at a READY sensor in its rest band forces MARK in (t+1/100,t+1/40); ERROR starts after t+99/100; READY returns after t+1 and before t+419/300 | Given an execution reaching that horizon; no phase word is supplied; main-cell consequences are supplied by the later pulse modules |
| `HybridInputs` | Queue and delivery provenance from actual sources/emissions; actual delivery dates; input isolation from queue/routing dates; raw validity, persistence and expiry | Concrete source queue and wiring must still be instantiated |
| `HybridExecutionTools` | Flow and snapshot predicates, cuts inside actual flows, first changing jumps, and all discrete READY states including the terminal snapshot | Does not construct future continuations |
| `HybridSensorGain` | Actual log-gain is frozen before t+99/100 and can increase by at most 11/125 during the raw window, using the extracted sensor cycle and ERROR speed bound | Allows ERROR overlap near the raw end; does not freeze the entire input |
| `HybridInputBalance` | Exact multiset queue/delivery/routing conservation with duplicate tokens retained; actual arrival chronology; exact source-date lists when complete and all source tokens are due | Exact source exhaustion requires empty routing and terminal saturation |
| `HybridMainBounds` | Global response<=3/4, silent charge bound, learned-gain interval [9/5,2], and real firing comparisons at 3/10 and 9/10 | Selected coarse real bounds; fine latency enclosures remain open |
| `HybridMainComparison` | READY upper/lower comparisons across actual flows and jumps, using smooth comparison currents and the original pulse date | Requires actual drive bounds and READY flow spans |
| `HybridSilent` | An isolated low-gain input has no main emissions, total ERROR dose 3/5, log-gain increase 3/5, and unchanged recovery | Declared charge/gain/rest section, reachable birth state, no new arrivals, and an actual execution reaching t+419/300 |
| `HybridFiring` | An isolated learned input's first actual main firing lies in (t+3/10,t+9/10); its entry contributes exactly one emission and every earlier same-cell emission is excluded | First-departure extraction; does not construct the input execution |
| `HybridSingleOutput` | The learned isolated input emits exactly once; after FAST the raw current is gone before SLOW can reopen, and zero-input READY cannot fire again | Does not assert execution existence |
| `HybridSlowProtection` | Actual recovery-cap integral bounds give SLOW duration >4/5 and at least 9/5 protection after firing; the entire learned ERROR span is protected and its total dose is zero | Fixed fabrication semantics and the declared input/gain/rest section |
| `HybridReadyReturn` | A sufficiently long actual learned-input trace contains its FAST and SLOW exits and a READY return before t+6.990787, with q=1/10 and no raw input | Requires initial recovery >=17999/100000 and an actual trace reaching t+7.5 |
| `HybridStableMemory` | MARK ends before t+1/20, hence before main firing; no receiving-port MARK dose is delivered; READY other ports stay quiescent and recovery is unchanged | Other ports must initially be READY in their rest bands with no raw current or later arrivals |
| `HybridPulseSection` | The actual isolated learned-pulse case restores the prepared section, exact resting main charge, no raw inputs, unchanged memories, zero ERROR/MARK doses on every port, and exactly one emission | Prepared-section reachability and full source calendars are not supplied |
| `HybridPulseRoot` | The actual first firing satisfies the real threshold equation with its original residual charge; the response root is unique in the firing window; positive residual advances the first firing relative to its rest reference | Fine latency enclosure membership remains to be proved |
| `HybridPulseBounds` | A direct real bound response<=16/25, nominal raw-gain headroom and early-time comparisons for gains through 12/5 | Does not assume stored exp/log certificate enclosures |
| `HybridNominalSilent` | No emission and total ERROR dose 3/5 for inputs with q<=7/50 and log-gain<=log(6/5)+1/1000, at any reachable recovery | Receiving sensor must be READY in its rest band, input isolated, and the actual trace long enough |
| `HybridSilentReturn` | At a gap >=7.5 the silent input restores READY charge/sensor bands, consumes its raw current, changes only the receiving gain by 3/5 and leaves recovery unchanged | No prepared-recovery premise; source/route instantiation and existence remain separate |
| `HybridMidGainInput` | First firing and the prepared learned-input case hold for actual gains in [9/5,12/5], covering both training gain regimes | The first firing alone does not establish a low-recovery cell's later MARK bootstrap |
| `HybridRecoveryTrace` | Nondecreasing recovery bounds every intermediate point; equal endpoint recovery freezes it throughout; exact constant-rate accumulated integrals and a SLOW no-departure budget | Only actual execution segments are compared |
| `HybridLowRecovery` | The first strong low-recovery input emits once, preserves every gain and recovery, has zero ERROR/MARK doses, and is still SLOW at a successor gap in [7.5,8.5], with q in [7/50,1/4] and READY sensors | The next protected input is handled separately by `HybridProtectedPulse` |
| `HybridMarkBudget` | A single sensor cycle adds at most 1/10 to recovery, including clipped or closed gates; this bound precedes proof of main protection or full MARK exposure | An upper budget does not imply a full dose |
| `HybridProtectedWindow` | The unconditional recovery budget keeps the actual main state SLOW through the whole sensor cycle | Requires the derived `MarkEntry`, a single canonical input and no new arrivals |
| `HybridProtectedMark` | Actual birth-reachable MARK gates are open throughout its selected phase; total MARK is 1/10 and total ERROR is zero | No full-dose or main-mode word is assumed |
| `HybridProtectedReturn` | The gained recovery forces an actual SLOW-to-READY return before t+6.990787, with all raw currents gone | Quantifies over an actual execution reaching t+7.5 |
| `HybridProtectedPulse` | No emissions, MARK 1/10 on the receiving port and zero on others, ERROR zero everywhere, all gains unchanged, recovery increased by 1/10, prepared section restored at exact q=1/10 | Concrete source calendars and birth-to-entry chronology remain separate |
| `HybridArrivals` | Select the first actual delivered token and reconstruct the execution; derive its due date, fresh raw origin and unchanged modes; a complete single-slot source queue has the exact chronological delivery list | Empty routing and all source tokens due by the horizon for queue-to-list transfer; no existence claim |
| `HybridPreparedTrain` | An actual period-eight train after preparation has exactly one emission per input, unchanged memories, zero ERROR/MARK doses and prepared-section restoration | Receiving gain in [1.8,2.4]; actual source-delivery list and final quiet horizon |
| `HybridBirthInput` | Select source zero from a READY birth, preserving its physical coordinates across all legal zero-time interleavings | Receiving cell's auxiliaries must be READY, as in the written entry theorem |
| `HybridWarmup` | Extract the first three low-port silent spans, with total ERROR 1.8, no emissions or MARK, unchanged recovery and the actual next strong-entry snapshot | Actual period-eight sources; no case word or reset |
| `HybridBirthSourceTrain` | From the exact sixteen-token low-port queue, an actual complete execution reaches the prepared section with 12 emissions, ERROR 1.8 and MARK 0.1 | Empty routing, READY-born receiving cell and T>=128; does not cover B's staged birth or later routed phases |
| `HybridCellInputs` | Extract the next actual arrival at one cell while retaining every other-cell arrival and event in the original execution | Isolation is local to the receiving cell, not global deletion of traffic |
| `HybridCellPreparedTrain` | An actual receiving-cell input calendar with variable gaps >=7.5 emits once per prepared input, preserves memories and restores preparation | Initial strong-gain/section bounds and a quiet final horizon; does not infer wire-delay bounds |
| `HybridCellSources` | Cell-specific source conservation and exact chronological source lists allow outgoing routes, other-cell arrivals and future tokens at other cells | No route targets the receiving cell during this trace; its initial source tokens are due by the complete horizon |
| `HybridPhysicalInvariant` | Propagate current charge/sensor bounds, gain/recovery caps and reserve [50,100]; derive positive power throughout actual flows and ERROR exposure from charge headroom | Current physical bounds and fabrication box, at any start date; raw validity is supplied separately where needed |
| `HybridStagedBirth` | A fresh READY birth changes n to n+1 at the current date; old coordinates, modes, currents, source tokens and parameters are retained; physical/raw/pending invariants and old/new memory balances compose across both actual phases | Routes, birth date and phase executions are supplied; the complete routed protocol and progress remain separate |


| `HybridFlowCuts` | Reuse the original flow path after a cut; every actual prefix has a remaining execution retaining all deliveries and emissions and additive ERROR/recovery balances | No extension beyond the given execution; split flows need not have identical constructor syntax |
| `HybridDueSources` | Strictly past sources have all been delivered; exact ordered prefixes and remaining pending multisets retain later source tokens | Empty routing and a future terminal queue; a source due exactly now may remain pending |
| `HybridBoundaryIdle` | A prepared cell at exact resting charge stays prepared through input-free time and terminal-date deliveries; zero-time guards exclude spurious departures or emissions | Actual execution and arrivals only at its terminal date |
| `HybridBirthPreparation` | With both 16-token source trains already queued, derive preparation at 128, twelve emissions and exact doses through 160, then transfer the prepared state and acquired memories across a birth at 160 | Actual executions, READY receiving auxiliaries, empty pre-birth routing and the birth date are premises of this module; later factories above supply the current constructed prefix |
| `HybridPreparedCalendar` | Derive a unique real rest-started firing latency in (0.3,0.9), identify actual learned-output dates and translate an entire separated input calendar by that one latency | Exact initial q=0.1, strong-gain and current-invariant bounds, actual receiving-cell calendar and return horizon; fresh wire jitter remains separate |
| `HybridCellDueSources` | Exact strictly past receiving-cell source prefix and retained later queue, with other-cell traffic present | Filtered initial queue, no incoming route at actual emissions, future terminal queue and strict source-date separation |
| `HybridRoutedInputs` | Actual receiving-cell deliveries equal the ordered issued wire tokens while future external sources remain pending | Issued tokens strictly before the endpoint, external sources strictly after it and a future terminal queue |
| `HybridContact` | Causal half-open gated wire with fanout at most one; actual routed tokens extracted from actual sending emissions | The target projection of routing at actual emissions is fixed to the declared contact |
| `HybridPreparedContact` | Derive actual wire inputs from a prepared sender's queue and ODE; specialize to sixteen B arrivals with fresh jitter and dates in (160.6,281.3) | A input 160 is already active; fifteen pending successors, current bounds, no return route to A and B sources at 320 or later; B output classification and the staged boundary are supplied by the subsequent teaching modules |
| `HybridRestingInput` | A READY cell retains its coordinate bands and memories through the quiet prefix before its first actual received input | Other-cell traffic is retained; initially absent raw inputs and READY bands |
| `HybridBirthQueueBridge` | Couple source160 raw absence/activity to the exact remaining queue, and preserve it across birth | Actual first phase with both initial source trains, empty pre-birth routing and birth at 160 |
| `HybridBTeachingPhase` / `HybridBTeachingCalendar` | Derive B14, ERROR0.6, MARK0.1 and prepared return from actual sixteen-input wire dates, including the quiet pre-input prefix | Fresh READY/current bounds, low birth recovery and the derived separated calendar |
| `HybridTeachingActivation` / `HybridTeachingBoundaryPhase` | Select the pending source160 after birth without changing physical coordinates or losing future B tokens; cover both legal boundary orders | Given execution reaching 319.9 and the proved raw/queue alternatives |
| `HybridTeachingActivePhase` | Compose the actual A16 source train and B14 wire-response phase with memory preservation | Current physical bounds and the source/route state, discharged by the staged theorem |
| `HybridEntryRouter` / `HybridStagedTeaching` | Instantiate forward/reverse contacts and derive cumulative A28/B14 plus prepared memories across B's actual birth | READY A birth, given staged executions at 160/319.9, B sources due from320 and bounded independent wire delays; no existence/progress claim |
| `HybridTeachingQueueClosure` | At319.9 A has no pending source and B retains exactly its future external birth queue | Actual queue conservation, routing windows and causal terminal future queue; no supplied output count |
| `HybridResidualLatency` / `HybridResidualPreparedCalendar` | Positive READY residual cannot delay the actual first firing; later outputs share the same-gain rest-root latency | Initial q>=0.1, prepared gain/section and actual separated input calendar |
| `HybridPreparedLearningTrain` | Three actual low-gain silent inputs give ERROR 1.8/MARK0, then a prepared learned train emits once per input | Current prepared section, nominal low gain, real receiving-cell dates with minimum gap 7.5 and final quiet horizon |
| `HybridFeedbackWeakEntry` | Construct the real B320/328/336 weak cycles and B344 source activation; derive ERROR1.8, A28/B14, own memories, the true B residual and28 future sources | Current prepared319.9 endpoint and exact B source queue; the original-birth factory discharges these without a reaching-execution premise |
| `HybridFeedbackFirstFire` | Construct the actual B FIRE in (344.3,344.9), its reverse Aport2 token, A28/B15 and29 pending tokens; bound its residual latency by the own rest reference | This factory ends before receipt; bounded backward delay supplies saturation at the FIRE cut, and the next factories construct the continuation |
| `HybridIntervalClosedExecutionProduct` | Weave either emitting cell with a neutral partner using contact closure only on the actual execution interval; retain every genuine FIRE and its exact emission ledger | No arrivals in the woven interval, a fixed future global queue and equal initial/final clocks; not an open-contact routing product |
| `HybridPortFastCompletion` / `HybridFeedbackFireProjection` / `HybridFeedbackSenderFastEnd` | Complete the actual projected B FAST/SILENT path, original RAW expiry and FAST exit at F+1, retaining own memories | Current physical clocks come from the actual global FIRE; no incoming continuation is assumed |
| `HybridPrefixStableMemory` | A real prefix of a memory-preserving path preserves the same own gains/recovery | Physical monotonicity on both the actual prefix and its retained suffix |
| `HybridQuietLeftWireArrival` / `HybridFirstReverseWiredArrival` | Consume the actual issued reverse wire at H in(344.7,345.3), retaining B's true cut and28 sources | Maximal sender cut and bounded backward delay; no event-priority or preloaded-wire assumption |
| `HybridFeedbackSenderReturn` | Construct B's real SLOW return/reopen and quiet prepared endpoint352 at q=0.1 | Actual FAST endpoint, own prepared recovery and first latency below0.9 |
| `HybridFirstReverseInterleavedPair` / `HybridFirstReverseInterleavedMemory` | Weave A's weak cut with B's true return and consume B352; derive27 sources, Aport2 ERROR0.6, zero ERROR elsewhere and zero total recovery | A's exact cut and later H+7.5 continuation are kept; no A PreparedSection or charge reset at352 |
| `HybridBirthFirstReverseArrival` / `HybridBirthFirstReverseInterleavedPair` | Construct original birth-to-receipt and birth-to352 traces, A28/B15 and own Aport2+0.6/Bport2+1.8 | Historical checkpoints retained as the source of the complete reciprocal construction |
| `HybridPortWeakCut` / `HybridFirstReverseNextWire` / `HybridReverseWeakStep` / `HybridReverseWeakNextWire` | Construct actual weak responses, cuts, next B sources and reverse receipts; derive the later prepared band from the retained weak path | Current physical bounds and exact source queue; no prepared charge reset at an intermediate cut |
| `HybridReverseEntryCompletion` / `HybridReverseLearnedReturn` | Construct three total weak A inputs, its first learned output and common prepared source376 | Actual own residual, source/token provenance and independent root clocks are retained |
| `HybridReverseCoupledLearnedCycle` / `HybridReverseCoupledLearnedTrain` / `HybridReverseLearnedEpoch` | Construct nine learned cycles for B376..440, prepared section448 and quiet continuation459.9 | Active source plus eight queued successors; exact sixteen later B sources retained |
| `HybridReverseTeachingCompletion` / `HybridBirthReverseTeaching` | Construct original birth-to459.9, cumulative A38/B27, own memories and CompleteThrough | READY birth/source family, independent B newborn and bounded actual contact delays; this historical checkpoint is extended through C teaching above |
| `HybridFeedbackSender` / `HybridFeedbackInitialSource` | Select direct B sources 320..440 and derive thirteen actual B outputs, retaining the first residual latency and later source tokens | B's actual initial queue, current prepared nominal return port and no incoming B route |
| `HybridFeedbackCalendar` / `HybridFeedbackReceiver` | Derive thirteen actual A return arrivals with fresh delays, then three silent inputs and ten learned outputs | Real B output calendar, initially empty A queue and concrete return contact; current prepared A bounds |
| `HybridFeedbackEpoch` / `HybridReciprocalEntry` | Derive A38/B27 and own port gains/recovery at459.9 from the physical execution | These analytic APIs take staged teaching and continuing executions; the original-birth construction above now supplies this prefix |
| `HybridFeedbackQueueClosure` | Empty A queue and exact remaining future B sources at 459.9, with multiplicities | Real B sender outputs, source conservation and future terminal queue |
| `HybridFastTeachingCalendar` / `HybridPreparedSourceContact` | Generic sixteen-input physical sender/contact and fresh receiver teaching at arbitrary cells and epochs | Actual source queue, current physical bounds, gated contact and a complete supplied execution |
| `HybridSourceActivation` / `HybridCIntroductionBoundary` | Old cells remain prepared through 480; the source due at birth is either pending or already fresh | Actual reciprocal prefix and exact remaining B sources; no event-priority assumption |
| `HybridCTeachingRouter` / `HybridCIntroductionActivePhase` / `HybridCIntroductionBoundaryPhase` | Actual B16/C14 and quiet A across both legal birth/source orders | B-to-C port-1 contact [480,630), current bounds and C's own READY birth data |
| `HybridCIntroductionQueueClosure` / `HybridStagedCIntroduction` / `HybridCEntry` | Physical cumulative A38/B43/C14 at 639.9; own memories and future C source queue retained | Analytic APIs accept supplied executions/births; the original-birth constructor above now supplies this specific C teaching prefix |
| `HybridConstructedCBirth` / `HybridCBirthActivePair` / `HybridQuietHeadExecutionProduct` | Construct independent C480 birth and B480 arrival, preserving A/B; lift the active B/C pair alongside quiet A | Current constructed reciprocal endpoint and independent C newborn; no copied memories |
| `HybridReadyWeakCut` / `HybridPortSourceWire` / `HybridPortWeakStep` / `HybridCWeakEntry` | Construct C's weak receipt, ERROR0.6 and actual488 source handoff, retaining the weak continuation | READY newborn recovery near0.08, actual carried charge and arbitrary receiving port |
| `HybridGuardedPortSourceWire` / `HybridCSecondWire` / `HybridPortFirstLearnedCut` / `HybridCFirstLearnedBoundary` | Construct C's first learned response and retain its true SLOW path at496 | The next contact uses that same physical path and exact queue |
| `HybridLowRecoverySlowSpanExtension` / `HybridPortSlowWire` / `HybridPortProtectedReturn` / `HybridCPreparedPair` | Extend the real SLOW flow, consume the next wire, derive protected MARK0.1 and common prepared504 | No state clamp, injected recovery or assumed prepared newborn |
| `HybridPortCoupledLearnedCycle` / `HybridPortCoupledLearnedTrain` / `HybridCLearnedEpoch` | Construct13 arbitrary-port learned cycles504..600, prepared608 and quiet639.9, preserving own memories and actual wire provenance | Fixed physical parameters, sender gain[1.8,2], receiver gain[1.8,2.2], bounded actual delays and explicit contact windows |
| `HybridCTeachingPair` / `HybridBirthCTeaching` | Construct original birth-to639.9 with both genuine births, A38/B43/C14, own memories, exact25 pending C sources and CompleteThrough | Later cadence is constructed separately; the common-birth every-N family uses its own preparation |
| `HybridQuietHeadNeutralProduct` / `HybridConstructedCadenceStart` / `HybridCadenceWeakStepExistence` / `HybridConstructedCadenceWeakWarmup` / `HybridBirthCadenceWeakWarmup` | Construct actual C640/644/648 weak responses and fresh652 under open global routing, with quiet A/B, ERROR1.8 and21 future sources | Actual non-emitting paths, independent own memories and carried charge; no global route-closure premise |
| `HybridCadenceResidualRootBounds` / `HybridResponseMarginInput` / `HybridCadenceFirstStrongFireExistence` | Derive strict first-FIRE margin through0.4 from residual q≤0.3, then construct F in652+(0.4,0.9) | Actual three-dose gain[1.8,1.9]; no assumed firing date |
| `HybridNeutralFutureFrame` / `HybridCadenceFirstWire` / `HybridBirthCadenceFirstWire` | Construct the genuine C FIRE, retain its same FAST cut, consume the exact C-to-B token and derive A38/B43/C15 with21 future C sources | Historical receipt H in(652.7,653.3), B prepared/fresh RAW and C actual FAST; extended by the first-wave construction above |
| `HybridCadenceStrongSlowSpan` / `HybridCadenceFirstRelayWire` | Continue the same C path, construct B's actual FIRE and consume the Aport2 relay wire at H_A in(653.4,654.4) | B actual FAST cut, C actual path and both retained continuations; no preloaded A wire |
| `HybridNeutralHeadExecutionProduct` / `HybridCadenceFirstAFire` / `HybridBirthCadenceFirstWave` | Construct A's actual FIRE and original birth-to-first-wave A39/B44/C15, with21 C sources and CompleteThrough | Historical A FAST/q=1 and B/C actual cuts; extended through the C660 return above |
| `HybridCadenceMarkOnlyExistence` | Construct a local protected SLOW MARK-only response and actual guarded return, retaining charge/recovery/energy clocks | Current physical section and isolated canonical input; instantiated at the actual C656 source by the global constructor above |
| `HybridCadenceFirstMarkSource` / `HybridCadenceFirstMarkReturn` / `HybridBirthCadenceFirstMarkReturn` | Construct the actual C656 protected source, MARK0.1, READY return and C660 arrival from the original births; A39/B44/C15 and19 future C sources | C READY/q=0.1/RAW660, own recovery+0.2; A/B actual cuts retained; historical witness alongside the complete N=3 factory |
| `HybridCadenceSecondStrongSlowSpan` / `HybridCadenceSecondStrongResponse` | Construct a local second strong pulse, SLOW carry and next actual source at period4 with unchanged memories | Exact-rest source and own recovery near0.28; later routed network responses remain separate |
| `HybridCadenceMixedPrefix` / `HybridCadenceMixedReopen` / `HybridReadySilentErrorStart` / `HybridCadenceMixedResponse` / `HybridCadenceMixedNextSource` | Construct local protected MARK, real reopening, remaining-RAW ERROR and next source with recovery+0.1/gain+0.6 | Actual SLOW entry/charge bands and future queue; No supplied reaching trace; local component instantiated by the complete N=3 cascade |
| `HybridAutonomousCellProjection` / `HybridBirthCadenceLocalCTail` / `HybridBirthCadenceLocalC` | Project actual C639.9→660 and construct its local tail to789.9; 20 cadence emissions, cumulative C34, all25 sources consumed | C-only component, now woven with actual B/A executions in the global cascade |
| `HybridLocalCadenceHighTrain` / `HybridLocalCadenceTail` / `HybridConstructedCadenceLeafPacket` | Actual high train and terminal C return; ledger-derived P(3,17,0) and bounded-delay labels P(3,17,1/20) | Token labels acquire global issuance only under the explicit same-calendar/routing hypotheses |
| `HybridCadenceHighFireExistence` / `HybridCadenceHighCompletion` | Construct high-gain FIRE in(0.16,0.26) and its actual protected completion across FAST exit | Own four-dose gain/current-state hypotheses and isolated future queue; no universal network continuation |
| `HybridLocalCadenceReceiver` / `HybridLocalCadenceReceiverPacket` / `HybridConstructedCadenceBC` | Physical B response to C packet;18 outputs and actual B packet | Concrete cadence domains and bounded packet jitter |
| `HybridCausalHeadQueue` / `HybridCausalHeadJump` / `HybridCausalHeadExecution` / `HybridCausalHeadBalance` / `HybridCausalHeadComplete` / `HybridCausalHeadSignals` | Genuine routed causal weaving with exact queue balance, emissions, deliveries and terminal completion | Sender/receiver traces and actual contact correspondence are retained |
| `HybridConstructedCadenceCascade` / `HybridBirthCadenceCascade` | Construct complete three-cell cadence789.9 from original birth premises, A54/B61/C34 and empty queue | Declared staged N=3 family; distinct common-birth every-N construction above; universal guarantees across staged-birth operations remain separate |
| `HybridEmissionRouterTransport` / `HybridTeachingCadenceRouter` / `HybridBirthCadenceProtocol` | Preserve actual ledger/deliveries under router retargeting; join teaching and cadence under one fixed gated router and retain both births through789.9 | Same physical source/birth family; no settings-copy, drift or arbitrary-N claim |
| `HybridBirthLearnedRest` | Derive Aport2/Bport2 learned-domain membership and isolated one-cell future contracts from the639.9 endpoint | Empty analysis queues do not erase the global queue; Cport1 and network routing are outside this bridge |
| `HybridCadenceRouter` / `HybridCadenceQuiet` / `HybridCadencePrelude` | Actual C-to-B-to-A contacts; three weak C cases through fresh source652 with ERROR 1.8, quiet A/B and twenty-one future C tokens | Actual execution reaching 789.9, initial prepared states and C's declared twenty-five sources; no complete cadence count claim |
| `HybridCadenceSilent` / `HybridCadenceWeakStages` / `HybridCadenceWeakWarmup` | Real four-period weak inputs with charge caps 0.1→0.15→0.2→0.3 | Current physical invariants and actual receiving-cell cuts; no reset or inherited period-eight cap |
| `HybridHighGainTrigger` / `HybridHighGainReturn` / `HybridCadenceHighTrain` | Real firing at high gain and residual charge; one output per 3.8-separated learned input with unchanged memories | Explicit current charge/gain/recovery bands and no additional receiving-cell arrivals within each pulse segment |
| `HybridMarkRecoveryIntegral` / `HybridSlowMarkWindow` / `HybridSlowMarkReturn` | Finite real MARK ramp, exact SLOW clock, and selected return before ERROR from current bounds | Physical cap/protection and current SLOW charge; global trace existence remains supplied |
| `HybridRawTailNoFire` / `HybridCadenceMixedPulse` | MARK0.1 plus ERROR0.6, no output, with the remaining raw tail and its final charge retained | Current SLOW charge [0.122,0.14], recovery near0.28, own three-dose gain and isolated horizon at least3.8 |
| `HybridCadenceRestRoot` / `HybridCadenceStrongPulse` / `HybridCadenceMarkOnly` | Direct three-dose rest root (0.65,0.66), strong-to-SLOW charge bounds and the MARK-only physical case | Explicit current-state and gap bounds; their actual cascade placement is composed below |
| `HybridHighGainCalendar` / `HybridCadenceHighTiming` | Own high-gain resting root, residual-aware calendars, first latency above0.16 at charge at most0.32 and resting reference below0.26 | Actual firing equation and proved state/gain bounds; high/low references and different devices remain distinct |
| `HybridSparseLearnedPulse` / `HybridCadenceSparsePrefix` / `HybridCadenceRelayPhase` | Seven-unit sparse settling, real dense transient cuts and generic relay counts/calendars | Physical incoming dates and gap bounds, discharged by the actual contact geometry |
| `HybridCadenceCPhase` / `HybridCadenceForwardGeometry` / `HybridCadenceReturnGeometry` | C20 with its exact physical output calendar; independent-jitter receiving geometry for B/A | True phase witnesses and separate own-gain latency references |
| `HybridCadenceWireCalendar` / `HybridCadenceBPhase` / `HybridCadenceAPhase` | Actual C outputs determine B20 inputs/B18 outputs, then A18 inputs/A16 outputs | Empty initial A/B queues and concrete contacts; no supplied B/A output count or received calendar |
| `HybridCadenceCascade` / `HybridCadenceEntry` | Cumulative A54/B61/C34, own memories/recovery, all cells at rest with no raw and an empty queue at789.9 | Generic trace-based interface with physical birth/source data and bounded delays; concrete N=3 existence is constructed separately |


The real coarse bounds used for work are a in (1,1.4), C<=5, Lm<=14, Ls<=3,
Le<=11 and M<=60. The sensor response at 1/50 is proved >=1/55 using real
exponential inequalities. These are proofs about the actual real expressions;
no stored rational endpoints or Python arithmetic implementation are assumed.
They suffice for the work invariant but do not close the other certificate bounds.

The reserve proof uses an integral barrier rather than differentiability at all
cap contacts. A density that points inward on the wrong side of a boundary cannot
move a continuous integral solution outside that boundary. This covers the work
discontinuities caused by actuator clipping and energy gates.

## Doses and clipping

Actual actuation is always integrated without rounding. For an openly exposed
ERROR span, the dose is `8*(m_start-m_end)`; for MARK it is
`(m_start-m_end)/2` per port. Actual legal entry/exit jumps yield the endpoints
for full doses of 3/5 and 1/10. Other-port contributions remain in recovery.
A partial dose such as `8*(0.07-0.025)=0.36` stays partial.

The global cap theorem permits clipping. A complete ERROR phase at an already
closed gain cap does not receive a full dose. `ErrorOpen`, `MarkOpen` and the
span exposure predicates still require the relevant mode chronology and strict
cap inactivity. For a flow reached from the declared birth family, the energy
part is now derived by `reachable_power_gate_open`, rather than postulated.

The clipped ERROR budget bounds `z+8*m` across an ERROR span regardless of
gate closures. Thus a strict inequality on the initial `z+8*(m-1/40)` proves
gain-cap inactivity throughout that span. Together with a reachable reserve
and actual READY main-mode spans, `error_exposed_of_headroom` derives the
complete exposure predicate across legal intervening events. The real low-gain
headroom estimate covers an increase of 12/5 above the low nominal log-gain;
it does not establish that the protocol has produced that increase.

`HybridSilent` now derives the READY chronology, strict headroom and positive
reserve for the isolated low-gain case. Its total ERROR dose follows from the
actual sensor cycle and the absence of later arrivals, including the post-cycle
READY sensor span. The isolated protected case is proved below. The combined case and the pulse
cases’ occurrence in the certified protocol remain separate obligations.

## Actual sensor cycle

`Execution.sensor_cycle` starts immediately after a canonical input has been
received: its active raw origin is the current date, the sensor is READY and
its charge lies in the declared rest band. The initial physical upper region
and independent fabrication box are required. The theorem takes an actual
execution reaching at least t+419/300.

It extracts the first READY-to-MARK jump, then the three protected auxiliary
phases and their actual outgoing jumps. Every decomposition reconstructs the
given execution. Trigger and protected durations follow from integral equations,
physical guards and proved real exponential inequalities; no recorded phase
word, desired count or stored root enclosure is assumed. Other cells, ports
and main-mode switches may interleave freely.

ERROR starts after t+99/100 and may overlap the last part of the raw pulse,
which is retained by the variable-gain comparison lemmas. READY returns after
the raw end t+1 and before t+419/300. Times are in the model's time units.
Silent learning and the first learned firing are now derived as described below;
the prepared-section case below also derives protection and return. The theorem
does not construct its input execution or exclude later inputs. `HybridInputs` supplies provenance and
isolation lemmas to discharge source and routing obligations separately.

## Isolated main inputs

`Execution.silent_input_dose` starts immediately after an actual canonical input
arrival. The main cell is READY with q<=3/25; the receiving sensor is READY in
the 1/40 +/- 1/100000 rest band; its log-gain is at most
log(3/10)+6/5+1/100000. Other ports have no raw current. No new arrival at this
cell occurs during the given execution, which must reach t+419/300. The initial
state is reached by an actual execution from `BirthState`.

These section assumptions imply that every actual discrete main state remains
READY, including simultaneous jumps and the terminal snapshot. The actual
emission list is empty. The total receiving-port ERROR integral is exactly 3/5,
the final log-gain increases by 3/5, and recovery is unchanged. The proof derives
ERROR exposure from reachable reserve and the remaining-charge cap budget. It
also proves that the sensor stays READY after its extracted cycle, so the total
dose does not hide a later contribution. It does not supply the training input
list or assert that the protocol reaches this section.

The raw-window gain increase is bounded by 11/125 using ERROR start after
t+99/100 and Le<=11. Gain is constant before that date as a consequence of the
selected sensor phases. The main READY comparison retains the late variable-gain
part and bounds it by a smooth exponential upper current. The direct real bound
response<=3/4 holds for every nonnegative age, so extending this comparison tail
after the physical cutoff cannot create a false silent conclusion.

`Execution.learned_input_trigger` instead takes log-gain in
log(3/10)+9/5 +/- 1/100000 and q in [1/10-1/100000,7/50], with the same sensor,
raw-input, isolation and execution-horizon conditions. Its first main departure
is an actual firing at a date strictly between t+3/10 and t+9/10. The returned
`MainTrigger` reconstructs the given execution, proves there was no earlier
same-cell emission, and identifies its first actual emission and a positive
output count. `Execution.learned_input_single_emission` strengthens this to an
exact singleton emission list and count one. Any first FAST departure occurs one
time unit after firing, hence after the raw cutoff. A later SLOW-to-READY departure
reopens at q=1/10 with no raw input and cannot create an extra firing. The proof
also covers executions ending in an incomplete FAST or SLOW phase. The modules
below supply ERROR protection and the prepared-section return.

`PreparedSection` declares READY main mode, q in [1/10-1/100000,7/50],
recovery in [17999/100000,18001/100000], and every auxiliary port READY in its
rest band. It does not assert that training has reached this section, and it
does not change the prescribed birth recovery near 2/25. The arrival raw tag
is specified separately.

`Execution.learned_pulse` takes this section, the same learned-gain interval and
isolation conditions, reachability from `BirthState`, and an actual execution
reaching t+7.5. The actual recovery cap gives SLOW duration greater than 4/5;
together with the one-unit FAST phase this keeps ERROR protected. Its total
ERROR dose is zero. The sensor MARK phase ends before t+1/20, when the main
cell is still READY, so its MARK gate remains closed. Other initially READY
ports without inputs stay quiescent. All gain coordinates and recovery are
therefore unchanged, with zero ERROR and MARK ledgers on every port.

Accumulated recovery, rather than a frozen SLOW rate, gives the READY return
before t+6.990787. The selected return jump and its prefix/suffix reconstruct
the actual execution. The main charge is exactly 1/10 afterwards, all raw
currents are gone, and the final state belongs to `PreparedSection` again.
This proves this isolated learned-input case with its exact emission count;
it does not prove the other protected/combined cases or the training word.

`MainTrigger.firing_equation` identifies the actual threshold with
`readyPulse initial_charge exp(initial_log_gain) input_date firing_date = 1`.
Gain freezing before ERROR is derived from the sensor cycle. The actual initial
charge is retained. Direct real derivative bounds prove strict monotonicity and
root uniqueness in the firing window. A positive residual can advance a first
firing relative to a rest-started reference; no physical pulse is retimed and
no equality of first and steady firing latencies is asserted.

The broader `Execution.silent_pulse` case uses `ReadyCoordinates`: READY main
and auxiliary modes, q in [1/10-1/100000,7/50], and the auxiliary rest bands.
It requires no high-recovery premise. With receiving log-gain at most
log(6/5)+1/1000, an isolated canonical input, birth reachability and a given
trace reaching t+7.5, it proves no emission, exactly one receiving-port ERROR
dose of 3/5, zero MARK doses on every port, unchanged other gains and recovery,
no remaining raw current, and the same READY coordinate bands at the end.
Silent relaxation is an actual exponential flow, not a reset to q=1/10.
If the cell was already in `PreparedSection`, that section is preserved too.

The uniform real response bound 16/25 and raw-window gain budget suffice to
cover both the three low-port silent training levels and the nominal fast-port
silent input. The tolerance here is a stated input-section bound, not a proof
of birth-to-section reachability. `Execution.learned_mid_pulse` handles the
prepared emitting case for actual initial gains in [9/5,12/5], without fixing a
nominal gain formula. This includes the low-port gain after three ERROR doses
and the fast-port gain after one.

`Execution.first_strong_low_recovery` now covers the first strong input before
recovery has been prepared. The initial READY coordinate bands and gain range
are as above, but b is in [0.07999,0.08001], and the given isolated trace ends
at a gap in [7.5,8.5]. Its actual firing, FAST exit, SLOW suffix and reconstruction
are returned. There is exactly one emission, no ERROR or MARK dose on any port,
and every gain and b are unchanged. The accumulated SLOW recovery stays below
log(5/2), so the main cell is still SLOW at the next input, with q in [7/50,1/4].
All auxiliaries are READY in their rest bands and raw currents are gone. These
are the proved `MarkEntry` conditions for the following input.

`Execution.protected_pulse` now closes the following isolated protected input.
It takes the derived `MarkEntry`, an isolated canonical input at a READY sensor,
birth reachability and an actual execution reaching t+7.5. First the unconditional
one-input MARK budget bounds recovery by 0.18001. If SLOW exited within the sensor
window, its exact charge equation and the actual recovery integral upper bound
would contradict initial q>=7/50. Thus the cell stays SLOW through t+419/300,
without assuming a full MARK dose.

MARK ends before t+1/20. The proved main protection, strict recovery headroom and
birth-family reserve invariant open its actual gates throughout the selected
MARK phase. The physical charge endpoints give exactly 1/10. The same main
protection makes ERROR zero. All other ports remain quiescent; every gain is
unchanged and recovery increases by exactly 1/10, into [0.17999,0.18001].

Starting at the actual MARK end, SLOW has charge in [1/10,1/4] and recovery at
least 0.17999. Its integral comparison forces a selected READY return before
t+6.990787. Protection excludes a return before the raw pulse has ended, and
zero-input READY relaxation then holds q exactly at 1/10. The whole input has
no emissions, no remaining raw current, READY sensors in their rest bands and
ends in `PreparedSection`. Neither a phase word nor the desired dose/count is
supplied. The first low-port source phase is proved below. Later routed source chronology
and the later C/cadence phases remain separate obligations. The first
two-cell teaching and return epochs are proved below.

## First actual birth-to-preparation source phase

`Execution.birth_low_source_queue` takes a `BirthState`, READY auxiliaries in
the receiving cell, the independent `PhysicalBox`, empty routing and exactly
the sixteen source tokens 0,8,...,120 on a low port (port 0 or 2). For any given
execution `CompleteThrough` a horizon T>=128, including the written phase end
159.9, it derives the complete first phase. The full later reciprocal protocol
is not asserted.

Exact multiset conservation and chronological delivery establish the ordered
source list, retaining every occurrence. `DeliveryStep` then selects actual
arrival jumps and their isolated prefixes. Source zero preserves birth
coordinates across legal zero-time interleavings. Three actual silent spans
give log-gain increase 1.8 with unchanged recovery. The input at 24 emits once
and leaves the derived SLOW entry at 32. The protected input at 32 gives MARK
0.1, no emission and no ERROR, then restores preparation before 40. Actual
arrival cuts and induction handle the remaining eleven learned inputs through
120. There are exactly twelve main emissions in total.

At the horizon the receiving cell’s modes are READY, q is exactly 0.1, sensors are in their rest
bands and no raw current remains. The receiving log-gain equals its birth value
plus 1.8, all other gains are unchanged, and recovery equals its birth value
plus 0.1. The total receiving ERROR and MARK ledgers are 1.8 and 0.1, with zero
contributions on other ports. These conclusions follow from the original
execution; no recorded case labels, desired counters or latency boxes are
premises. General birth-family cap, work and reserve bounds remain available.

`CompleteThrough` is a premise of this full-queue corollary. The separate
constructive factories above now supply the first preparation and teaching epochs. The first phase covers the written READY birth family,
not immediate input into an ERROR-born receiving sensor. The prefix refinement
below retains later sources and connects the state at 160 to a scheduled birth.
The A-to-B teaching and B-to-A return routes are instantiated below. The C/cadence analyses below retain their conditional signatures; the new original-birth factory supplies the C teaching prefix through639.9.


## Receiving-cell calendars inside a multicell execution

`Execution.first_cell_delivery` selects the first actual arrival at one cell.
Its isolated prefix can contain arbitrarily many arrivals and legal events at
other cells. It reconstructs the same global execution and derives the selected
jump's due date, fresh raw origin and unchanged main/sensor modes. No global
traffic is discarded.

`prepared_cell_train` accepts any finite receiving-cell calendar whose gaps,
including the gap from its current input to the next, are at least 7.5. The final
input also has a quiet horizon of at least 7.5. Actual arrival cuts and induction
produce exactly one emission per input, zero ERROR/MARK doses, preserved gains
and recovery, and the prepared section at exact resting charge. Other-cell
arrivals may interleave throughout. A short cadence gap cannot reuse this case.

`Execution.cell_sources_exact` derives such a receiving-cell source list from
token conservation and chronological delivery when routes do not target that
cell during the observed execution interval, its initial tokens are due by the
complete horizon and those tokens use one ordered receiving port. Outgoing
routes and other cells' traffic and future pending tokens remain unrestricted.
This discharges source isolation without requiring globally empty routing; it
does not yet derive the later incoming wire calendars or instantiate the birth schedule.


The `*_of_valid` prepared-input and return theorems take `UpperRegion` and
`RawValid` at the current starting snapshot directly. The current prepared
section and strong-gain bounds, actual received pulse, arrival isolation and
return horizon remain explicit. This also applies to `prepared_cell_train_of_valid`
with variable gaps. Each arrival advances the physical-region/raw-validity
invariants through its actual prefix; the induction preserves the same global
execution. The former birth-reachable statements are corollaries of these
variants, with unchanged signatures.

These local statements apply at arbitrary starting times and do not require all
cells' current memories to be nominal birth memories. They provide the prepared
case needed after a staged birth once the current invariants are established.
Positive-dose silent/protected cases retain their reserve and exposure proofs.


`PhysicalInvariant` packages the current upper physical region, actual per-port
gain caps, recovery cap and reserve in [50,100]. It is preserved by every actual
execution. The reserve proof still derives work <=500 before using positivity.
Current-state flow bounds therefore open the energy gates throughout complete
ERROR/MARK phases; strict cap exposure is derived from the same charge budgets
and headroom as before.

The `*_of_invariant` silent and protected-input theorems now use these current
physical bounds and raw validity directly. The first strong low-recovery case
also has an `*_of_valid` variant. Actual sensor cycles, phase protection, full
doses, counts, return and memory balances remain conclusions, with the same
input separation and charge/gain/recovery bands. Earlier birth-family theorems
remain corollaries with their original signatures. These results provide the
local dose cases for a later staged-birth composition; its introduction event
and complete routed protocol are not established by this invariant alone.


## An explicit staged-birth event

`Newborn` carries the declared READY birth-coordinate family, including nominal
per-port log-gain bands, low recovery, auxiliary rest bands and reserve anywhere
in [50,100]. Its nominal member is constructed and checked. A `BirthStep` places
that fresh cell at the current execution date and appends it after the existing
cell indices. `Newborn.snapshot` witnesses the coordinate family at zero; the
birth event itself uses the shared current date.

Every existing coordinate, main/sensor mode and raw origin is retained exactly.
The old queue is mapped to the extended index type without changing ports,
dates, order or multiplicities. Additional source tokens are explicit, target
only the new cell and cannot be past due. The new cell has READY modes, no raw
current, nominal gain bands and its own low-recovery band. Existing parameters
are preserved; the added cell's parameters are independent members of the same
fabrication family.

`StagedExecution` joins a real n-cell phase, this birth event and a real (n+1)-cell
phase. It preserves physical bounds and reserve, raw validity, causal pending
queues and the shared time order. Old gain/recovery balances retain contributions
from both phases. The fresh cell's balances start from its own birth coordinates
and use its post-birth ledger. The step provides no reset or learning dose to an
existing cell.

This defines the birth boundary needed for B at 160 and later introductions.
The next section connects the first source phase to a birth at 160 while
retaining the legal boundary-source alternatives. The complete A-to-B epoch is
now connected below, followed by the physical B-to-A return epoch. These
analytic interfaces take a one-birth execution; the original-birth factories
now construct the two-cell prefix through459.9 and add the genuine C birth
and teaching through639.9, followed by the complete constructed N=3 cadence
through789.9. Both actual births and the fixed three-cell routing law are retained.


## Preparation at the actual birth boundary

`Flow.suffix` reuses an existing flow path from an intermediate date through its
original endpoint. The integral equation follows by subtracting the two original
integral equations; all modes, raw inputs, pending tokens and guards are retained.
Every `Execution.IsPrefix` therefore has a genuine remaining execution, including
when the cut is inside a flow. Actual delivery and emission lists concatenate,
and ERROR/recovery balances add across the cut. A split flow need not have the
same constructor representation as its original, so no syntactic reconstruction
of the full execution is asserted.

`Execution.deliveries_before_perm_sources` derives exactly the multiset of
sources strictly before the terminal date for empty routing and a terminal
`PendingFuture` queue. A source due exactly at that date may still be pending.
An ordered one-slot prefix is fixed by chronology even when later sources were
already present in the original queue. A second conservation lemma retains all
later pending tokens, with their multiplicities.

`Execution.birth_low_two_trains_prefix` now applies the physical first-phase
proof inside the queue containing both 0,8,...,120 and 160,168,...,280. Any given
execution reaching 128 has a prefix at exactly 128 with twelve emissions,
receiving ERROR 1.8, MARK 0.1 and the prepared state at exact resting charge.
Pending urgency, rather than an assumed arrival list or `CompleteThrough`,
forces the first sixteen sources to have arrived. The remaining execution and
the full future queue are retained.

`Execution.birth_prepared_at_second_train` extends this result to an actual
endpoint at 160. All possible remaining arrivals through that endpoint are due
exactly at 160. Before their first arrival the prepared cell remains at rest;
after it, all remaining events have zero duration. The actual guards exclude
main or sensor departures from their READY rest values during those jumps.
The complete prefix still has twelve emissions, ERROR 1.8, MARK 0.1, acquired
log-gain 1.8 and recovery gain 0.1. Its receiving raw input is either absent or
fresh at 160; other raw inputs are absent. Both legal boundary orders are kept.

`StagedExecution.preparation_at_birth` transfers these conclusions across a
birth whose pre-birth endpoint is 160. Existing coordinates, modes and raw
origins are preserved by the birth step. The new cell retains its independent
nominal birth family. This connects the first physical phase to the introduction
boundary; it does not yet classify the post-birth A-to-B train, establish the
later wire calendars or construct a complete execution. The actual executions
and the birth at 160 are still premises.


`HybridInputBalance` retains every routed token in a multiset conservation law.
For empty routing, an execution complete after all supplied source dates has an
actual delivery list permuting the initial source queue. Filtering by cell/port
and chronological sorting gives the exact source-date list, including duplicate
tokens. This result remains conditional on a complete execution; it does not
establish source availability, port separation or progress.


## A common latency derived from the physical response

`HybridPreparedCalendar` proves existence and uniqueness of a rest-started
threshold root for every actual gain in [1.8,2.4]. The intermediate value theorem
uses direct real response bounds at 0.3 and 0.9; monotonicity gives uniqueness.
`restLatency` selects this mathematical root and its specification proves
0.3 < latency < 0.9 and the real threshold equation. It is not a supplied
certificate enclosure or a protocol event date.

`LearnedPulse.emission_at_rest` identifies an actual output with input date plus
that root. Its firing equation comes from the original execution and the
selected sensor cycle. The starting charge must be exactly 0.1; a general
prepared charge band does not give the same latency.

`prepared_cell_calendar_of_valid` extends this to a finite receiving-cell train:
the actual emission list is exactly the input-date list translated by one
latency at the initial physical gain. Each actual pulse preserves that gain and
restores exact resting charge before the next input, so root uniqueness applies
again. The initially active input and every later receiving-cell arrival are
retained, and other-cell traffic remains unrestricted. Current physical/raw
bounds, separated inputs with gaps at least 7.5, and the final quiet horizon
remain premises. Fresh per-pulse wire delays still need their own bounds; this
result does not make routed input dates periodic or instantiate the A-to-B queue.


## Actual routed calendars and gated contacts

`HybridCellDueSources` extends strict-past source conservation to one receiving
cell. Its initial filtered queue may be any permutation of a past prefix and
later tokens. If actual routes do not target that cell, pending urgency and
chronology determine the exact delivered prefix at a shared port. The terminal
filtered queue retains every later token with multiplicity. All other cells'
queues, arrivals and routed traffic remain in the execution.

`HybridRoutedInputs` supplies the complementary case: the receiving cell's
external sources are all strictly later than the terminal date, while every
routed token to that cell is strictly past. The actual deliveries then permute
exactly the actual issued tokens to that cell. A future terminal queue is
sufficient; no `CompleteThrough` or arrival calendar is assumed. Chronological
one-port issued tokens fix the full ordered delivery list. Strictness matters:
a routed token due exactly at the terminal date may still be pending.

A `Contact` fixes source, target, receiving port, a half-open firing gate and a
per-emission delay function. Its router is causal for nonnegative delays and has
fanout at most one. `issuedTo_contact` extracts its tokens from actual sending
emissions. Its routing premise fixes only the receiving-cell projection and
only at actual emissions; other destinations remain unrestricted.

`prepared_contact_calendar_of_valid` combines the physical common-latency
calendar with token conservation. The sender's input port and the contact's
receiving port are separate data. Prepared return, gate containment and fresh
wire delays in [0.3,0.4] imply that every emitted token is received in order by
the terminal date. Other-cell traffic and later external sources are retained.

For the declared A-to-B contact, `teaching_contact_sources` starts at 160 with
A's input already active, exact prepared resting charge and its fifteen pending
successors 168,176,...,280. The reverse contact is closed to A throughout this
trace, the A-to-B firing gate is [160,310), B's external sources are due at 320
or later, and the actual execution ends at 319.9. It derives exactly sixteen
B deliveries from the source queue and ODE, without assuming A's outputs or B's
arrival list. Their dates are 160+8k+latency+delay(160+8k+latency), strictly
between 160.6 and 281.3. Successive dates have gaps in [7.9,8.1]: the common
latency cancels while both fresh wire delays remain.

The standalone calendar theorem takes the initial active input, pending A
queue and current bounds as premises. The staged teaching result below now
discharges them in both birth-boundary alternatives and derives B's fourteen
outputs. This conditional API itself supplies no execution; the declared
staged N=3 and common-birth every-N factories are described above.


## Complete physical teaching across B's birth

`StagedExecution.reciprocal_teaching_epoch` connects the first two source epochs
in the declared one-cell-to-two-cell semantics. A starts in `BirthState`, with
READY auxiliaries and the complete source queue 0,8,...,120 and 160,168,...,280
on port 0. B is introduced by a real `BirthStep` at 160, with its own independent
nominal READY coordinate family and fabrication parameters. New B sources must
be due at 320 or later. The supplied post-birth execution ends at 319.9.

`HybridBirthQueueBridge` proves the exact raw/queue dichotomy at 160: the source
is either pending with the full second train, or active with exactly its fifteen
successors left. Multiplicity conservation excludes a duplicate consumption.
The actual birth preserves this relation under index extension. If the source
is still pending, `HybridTeachingActivation` selects its real post-birth arrival.
The intervening trace has zero duration; physical guards exclude outputs from
both cells, coordinates stay unchanged and B's future tokens are retained.
No event-priority rule or reset is introduced.

`HybridRestingInput` carries the freshly born B cell through its actual quiet
prefix to the first received wire pulse. `HybridBTeachingPhase` then derives
one silent input, the first strong input, the protected input and thirteen
learned inputs from the actual variable-gap trace. `HybridBTeachingCalendar`
proves the required gaps, first-strong upper gap and final quiet horizon from
the real wire dates, retaining all A traffic. `HybridTeachingActivePhase` and
`HybridTeachingBoundaryPhase` compose this with the sixteen learned A inputs
in both legal source/birth orders.

`reciprocalEntryRouter` declares the forward [160,310) contact on B port 1 and
the reverse [320,470) contact on A port 2, with independent per-emission delays
in [0.3,0.4]. Actual emission-time bounds keep the reverse route closed during
teaching and discharge the target-routing premises. Invariants, raw validity,
causal future queues, received calendars, pulse cases and counts are all derived.

At 319.9 the conclusions are:

| Quantity | A, relative to its birth | B, relative to its own fresh birth |
|---|---|---|
| Actual emissions | 12 before B's birth plus 16 after, total 28 | 14 |
| Receiving log-gain increase | 1.8 on port 0 | 0.6 on port 1 |
| Receiving ERROR / MARK | 1.8 / 0.1 cumulatively | 0.6 / 0.1 |
| Recovery increase | 0.1 | 0.1 |
| Terminal section | Prepared READY, q exactly 0.1, no raw current | Prepared READY, q exactly 0.1, no raw current |

Every other gain is preserved. B's memories are measured from its independent
newborn data; no acquisition from A is copied. `StagedTeaching` retains the
actual before/after phase witnesses and these cumulative balances.

This is a conditional physical protocol theorem. The two executions, birth at
160 and terminal date are supplied; their existence/progress is not constructed.
B's exact source list for the return phase is not fixed by this teaching-only
statement. The reciprocal-entry theorem below fixes it and covers459.9.
The C/cadence analyses retain conditional signatures; separate factories now
construct the specific birth-to789.9 N=3 protocol. Probes, remaining
enclosure membership and broader protocol families remain open; the separate
common-birth chain is constructed for every finite N.
Parameters are fixed members of the stated fabrication boxes, with canonical
pulse amplitudes; noise and drift require their separate extensions.


## Physical reciprocal entry through 459.9

`StagedExecution.reciprocal_entry` composes the teaching witness with a genuine
continuing two-cell execution, sharing the exact snapshot at 319.9. B's birth
queue now contains the sixteen port-2 sources 320,328,...,440 plus later tokens
strictly after 459.9. `reciprocal_entry_two_trains` fixes those later tokens to
the next declared source train 480,488,...,600, retaining it in the same queue.
There is no reset at the phase boundary.

`HybridTeachingQueueClosure` proves that A's pending queue is empty at 319.9
and B's queue still permutes exactly its own external birth sources. Delivered
wire tokens cancel their actual issued multiset; all future source occurrences
are retained. The concrete router has no incoming route to B after 310. Strict
source conservation therefore selects exactly the sixteen direct B arrivals
through 440 while later tokens remain in the physical execution.

`HybridPreparedLearningTrain` derives three silent inputs and then the learned
remainder from the current prepared section and an initially nominal low gain.
The silent inputs supply receiving ERROR 1.8, zero MARK and unchanged recovery.
Their final entry is a real selected arrival, not a supplied case endpoint.
Nonnegative drive keeps READY charge at or above exact rest when it starts
there, so the first learned input retains its nonnegative residual.

`HybridResidualLatency` and `HybridResidualPreparedCalendar` identify the first
actual firing with its own residual-dependent latency in (0.3,0.9), no greater
than the same-gain rest reference. Only later learned inputs share the exact
rest-started latency. `HybridFeedbackSender` and `HybridFeedbackInitialSource`
then derive B's thirteen outputs: the first at 344+first, followed by the twelve
outputs at 352+8k+restLatency. The first latency is not forced to equal the rest
reference.

`HybridFeedbackCalendar` extracts the actual return tokens from these actual
B emissions through [320,470), keeping every independent wire delay. The common
latency cancels only for regular successors. The first wire gap is at least
7.9 and has the coarse upper bound 8.7; the later gaps lie in [7.9,8.1]. The
prepared receiving case needs only the minimum gap 7.5. All thirteen A arrivals
lie strictly between 344.6 and 441.3. `HybridFeedbackReceiver` derives three
silent A inputs and ten learned outputs, including its original quiet prefix.
No desired output word, received calendar or dose counter is a top-level premise.

The concrete `HybridFeedbackEpoch` and `HybridReciprocalEntry` composition gives:

| Quantity at 459.9 | A | B |
|---|---|---|
| Cumulative actual emissions | 28+10=38 | 14+13=27 |
| Initial teaching gain | Port 0: birth log-gain +1.8 | Port 1: own newborn log-gain +0.6 |
| Return learning gain | Port 2: birth log-gain +1.8 | Port 2: own newborn log-gain +1.8 |
| Other gain | Port 1 preserved | Port 0 preserved |
| Recovery | Birth recovery +0.1 | Own newborn recovery +0.1 |
| Return-epoch ERROR / MARK | 1.8 / 0 | 1.8 / 0 |
| Terminal section | Prepared READY, q exactly 0.1, no raw | Prepared READY, q exactly 0.1, no raw |

The final physical invariant includes all gain/recovery caps and reserve in
[50,100], and raw validity is propagated. The analytic APIs above quantify
over actual executions reaching160,319.9 and459.9 with the genuine B birth
at160. `birth_protocol_reverse_teaching_exists` now constructs this complete
prefix from the original birth assumptions. A's initial auxiliaries remain
READY; this is not an ERROR-born generalization. The later C introduction
and cadence analytic APIs below still accept executions and a C birth; the
separate concrete factories supply these for the declared N=3 protocol.
Probes, remaining fine enclosures, general extension/progress and broader
protocol families remain open. The separate common-birth chain is constructed
for every finite N. Fixed fabrication parameters and canonical pulse
amplitudes remain the scope; noise and drift need separate extensions.

## Conditional physical C introduction through 639.9

`HybridFeedbackQueueClosure` exposes the reciprocal handoff: A's queue is empty,
while B retains exactly the future part of its own newborn source queue. This
is a multiset equality expressed by `List.Perm`; every occurrence is retained,
without claiming that the physical queue has a particular ordering.
`ReciprocalEntry` also records this handoff and terminal `PendingFuture`.
For the concrete two B trains, its remaining queue is exactly 480,488,...,600
on port 2.

`HybridCIntroductionBoundary` follows the actual old-cell execution from 459.9
to 480. Both cells preserve their prepared section, exact resting charge,
all log-gains and recovery, with no emissions. At 480 B has either no raw and
all sixteen source tokens, or a fresh raw on port 2 and the fifteen successors
488,...,600. The two states are coupled by token conservation, not a chosen
priority. `BirthStep` then appends the independent READY newborn C without
resetting either old cell or losing a pending token.

`HybridSourceActivation` handles the pending alternative using the actual first
receiving-cell delivery. The preceding zero-time interleavings cannot reach a
READY firing or sensor threshold; coordinates, other raw inputs and source
provenance are preserved. The active alternative uses the same physical phase
directly. `HybridPreparedSourceContact` derives B's sixteen physical outputs and
the actual C arrivals through `cTeachingContact`, B-to-C on port 1 during
[480,630). The latter lie strictly in (480.6,601.3); common sender latency
cancels between successive inputs while each fresh wire delay remains.

`HybridFastTeachingCalendar` derives C's one silent, first strong, protected and
learned cases from those real dates. It gives C fourteen outputs, ERROR 0.6,
MARK 0.1 and a prepared return. These are conclusions, not a supplied case word.
A receives nothing and remains idle in the same three-cell trace.

`StagedExecution.reciprocal_c_entry` composes the entire physical prefix:

| Quantity at 639.9 | A | B | C |
|---|---|---|---|
| Cumulative actual emissions | 38 | 43 | 14 |
| New emissions during C introduction | 0 | 16 | 14 |
| Log-gain changes from own birth | Ports 0 and 2: +1.8 each; port 1 preserved | Port 1: +0.6; port 2: +1.8; port 0 preserved | Port 1: +0.6; other ports preserved |
| Recovery from own birth | +0.1 | +0.1 | +0.1 |
| Terminal section | Prepared READY, q=0.1, no raw | Prepared READY, q=0.1, no raw | Prepared READY, q=0.1, no raw |
| Pending queue | Empty | Empty | Exactly C's external newborn sources, up to permutation |

The physical gain/recovery caps, reserve in [50,100], raw validity and future
queue property propagate through both births. `CEntry.cadence_sources` retains
the twenty-five C port-0 tokens 640,644,...,736 if they were declared at C's
birth. It proves their conservation, not the subsequent period-four responses.
The general theorem only requires C sources due at 640 or later.

This analytic API takes staged traces and births as premises. The independent
original-birth factory above now constructs both genuine births and the complete
teaching execution through639.9. The later sections instantiate the cadence
contacts, prove the local combined MARK/ERROR case and compose the entire
finite cascade. Fixed fabrication parameters, canonical
pulse amplitudes and initial READY auxiliaries on A remain explicit scope.

## Physical cadence initiation and local cases

`cadenceRouter` contains C-to-B on port 2 and B-to-A on port 2 during [640,780).
Its fanout is one, its receiving projections are exact, and it routes nothing
to C. Actual token conservation therefore derives all twenty-five C port-0
inputs 640,644,...,736 from its preserved birth queue. The two wire delays
remain independent functions of their own actual emission dates.

`CadencePrelude` reaches the fresh source at 652 from those actual inputs.
The first three physical weak cases give ERROR 1.8, MARK0 and no C output.
The main charge is retained quantitatively: the four-unit relaxation bounds
are 0.1→0.15→0.2→0.3. The source at 652 is already delivered, so four tokens
have been consumed but only three ERROR cycles completed. All twenty-one
tokens 656,660,...,736 remain pending, and the continuation retains that exact
receiving calendar. C's silence closes the actual C-to-B route; B's derived
silence then closes B-to-A. Both old cells retain their own prepared memories,
exact resting charge and empty queues, without discarding other-cell events.
The physical invariant, raw validity and future-queue property reach this
prefix. `CEntry.cadence_prelude` supplies these premises from the preceding
physical theorem and each cell's own birth data.

The standalone prelude needs only an upper bound on C's initial low gain. Its
fourth input is described as fresh, not assumed to fire. The lower nominal
gain at that entry comes from C's own birth when composing the next pulse.
This standalone analytic prelude accepts a later cadence execution and does
not by itself prove its output counts. The separate constructive factories
above now supply the declared three-cell execution through789.9.

The following local pulse cases are proved from physical state inequalities,
guarded phases and actual isolated receiving-cell spans:

| Local case | Current input conditions | Derived behavior |
|---|---|---|
| Weak C stages | Own low-port gain with zero, one or two ERROR doses; four-unit gaps and the distinct charge caps above | No output, ERROR0.6 per input, no MARK, next real charge bound and no remaining raw |
| Strong before MARK | READY charge at most0.3, own three-dose gain, recovery at most0.28001, gap in[3.8,4.2] | One output, no ERROR/MARK, preserved memories and actual SLOW charge at the next input |
| First strong at recovery near0.18 | Same strong case with the current recovery band | Next SLOW charge at least0.148 |
| Second strong at recovery near0.28 | Rest-started same-gain case | Next SLOW charge in[0.122,0.14], using the real response root |
| Protected MARK-only input | SLOW charge in[0.148,0.25], recovery near0.18, isolated horizon at least3.8 | No output or ERROR; full MARK0.1; READY return before3.8, q exactly0.1, raw absent |
| Mixed MARK then ERROR | SLOW charge in[0.122,0.14], recovery near0.28, own three-dose gain, isolated horizon at least3.8 | No output, full MARK0.1 and ERROR0.6; own gain +0.6 and recovery +0.1; READY with actual charge in[0.1,0.32], raw absent |
| High-gain learned input/train | Gain in[3.2,3.5], recovery at least0.37999, READY charge in[0.09999,0.5], gaps at least3.8 | Exactly one output per input; no additional learning or recovery; settling before3.8 at exact resting charge |

The high-gain trigger uses a proved lower firing time 0.1 rather than reusing
the previous 0.3 bound. Its firing equation retains the initial residual.
At gains at least3.2 the actual firing is before0.3. A same-gain comparison
does not identify a first residual-dependent latency with a resting one.
The separate three-dose reference has the directly proved real enclosure
(0.65,0.66); this reference must not be applied to the four-dose high gain.

The mixed case is a physical case theorem, not a recorded case-word check.
Its first SLOW return is selected between input+0.5 and input+0.99. During
MARK, the actual recovery profile is exponential, and its accumulated clock
contains the full `markDeficit` correction. Other auxiliary modes and physical
cap opening are derived under the stated current-state hypotheses.
On reopening, the still-active raw input keeps its original origin. A real
gain bound during raw, allowing ERROR growth, bounds its remaining charge
by 0.1+G/4<1. The actual raw-end event is selected; the final charge then
relaxes from that real endpoint. No artificial raw deletion or resting reset
is used. READY on the actual ERROR span supplies the full positive ERROR dose.

The next section composes these local cases from the actual routed dates.
The local case statements themselves do not assume a global case word or
the desired cascade counts.

## Complete conditional cadence through 789.9

`HybridCadenceCPhase` selects the actual C inputs at652,656,660,664 and668
from the prelude continuation. The physical first strong, MARK-only, second
strong and mixed cases feed the eighteen remaining learned responses. The
complete C phase has twenty emissions, ERROR2.4 and MARK0.2 on port 0, with
all other gains preserved. Its own resting references are used only after
exact returns to rest; the two first residual latencies remain separate.

`HybridCadenceWireCalendar` extracts the actual B arrivals from those C
emissions through the real forward contact. The sparse prefix needs gaps
at least7, which permits the actual offsets below7.5. Generic relay cases
select every later strong/MARK/mixed/high phase from receiving-cell cuts.
B has eighteen outputs, ERROR0.6 and MARK0.2 on its own port2. Its emitted
calendar retains its own low/high references and its own first high residue.
The actual return contact then derives A's eighteen arrivals, and the same
generic relay composition gives A sixteen outputs with ERROR0.6/MARK0.2.
No B/A receiving calendar, case word or output count is a top-level premise.

The two wire functions are evaluated independently at the true sending dates.
Their effects are preserved in the gap proofs. In particular the first dense
gap at A may exceed4.2; the rest-started first-strong proof permits4.5 there.
The later dense pairs retain bounds [3.8,4.2]. The sharper high-gain timing
uses the mixed pulse's actual carried charge at most0.32, not a resting reset.
No equality between the gains or latency roots of distinct cells is used.

`Execution.cadence_cascade` derives the new block from current physical states.
`CEntry.cadence_entry` connects it to each original birth. Finally
`StagedExecution.reciprocal_cadence_entry` derives all intermediate packages
from the source queues, fresh births and supplied executions:

| Quantity at789.9 | A | B | C |
|---|---|---|---|
| New cadence emissions | 16 | 18 | 20 |
| Cumulative emissions | 54 | 61 | 34 |
| Cadence ERROR on active port | 0.6 | 0.6 | 2.4 |
| Cadence MARK on active port | 0.2 | 0.2 | 0.2 |
| Active log-gain from own birth | Port2: +2.4 | Port2: +2.4 | Port0: +2.4 |
| Other acquired memory | Port0: +1.8; port1 preserved | Port1: +0.6; port 0 preserved | Port1: +0.6; port2 preserved |
| Recovery from own birth | +0.3 | +0.3 | +0.3 |
| Terminal state | READY, q=0.1, auxiliaries in rest bands, no raw | Same | Same |

The final queue is empty by actual conservation: all initial tokens are due
by736 and every routed token is due before780.4, strictly before789.9.
Causal `PendingFuture` excludes any such token remaining at the endpoint.
Gain/recovery caps, reserve in[50,100] and raw validity also propagate.

This analytic interface remains conditional on actual traces through160,
319.9,459.9,480,639.9 and789.9. Separately, the constructive factory now supplies
the declared three-cell cadence and both genuine births, deriving the same
counts and own-memory endpoint from the initial source/birth data. A starts
with READY auxiliaries, an explicit subfamily of `BirthState`. Fabrication
parameters are fixed independent box members; initial coordinate perturbations
and bounded fresh wire delays are retained. No probabilistic independence,
operational drift, dynamic noise or device fault model is asserted. Frozen
probes, cuts/copies and maximal/infinite-run progress remain separate obligations.
The distinct common-birth arbitrary-N composition is now constructed above.

## Physical event budget

For a network of n cells born at zero, let Q be the length of its actual initial
pending queue and suppose each firing routes at most F delivery tokens
(`FanoutBound`). Every finite admissible prefix ending by T satisfies

```
physical jumps <= n*(27*T + 33) + 2*(Q + F*n*(T + 1)).
```

All nine `Jump` constructors are counted, including events exactly at T and
arbitrary compatible zero-time interleavings. No supplied firing count or event
word is used. The bound is deliberately coarse:

- A FAST logarithmic potential gains one at a real firing and decreases by the
  elapsed FAST time. Its terminal value is at most one, so an incomplete final
  phase is retained. Each cell fires at most T+1 times, and has at most 3T+3 main
  mode changes. A newly entered FAST phase cannot be left before one time unit,
  even across intervening other-cell or auxiliary events.
- On each port, a SILENT logarithmic potential decreases at the actual rate
  Ls/log(8), proved at most two in both fabrication families. A mode rank relates
  the number of all auxiliary changes to SILENT entries, giving 8T+10 changes.
  These clocks are proof potentials, not added physical coordinates.
- Every arrival consumes an initial or routed token. Every raw end consumes a
  current created by an arrival; raw currents are absent at birth. The initial
  queue and actual routed fanout therefore remain in the global bound.

`finite_prefix_event_budget` converts this real bound to one natural budget
shared by every finite admissible prefix with the same birth state and horizon.
Thus physical jump counts cannot grow without bound at bounded times. Splitting
a continuous flow into arbitrarily many pieces is not counted as a physical
event. This settles the uniform finite-prefix event-count obligation under
bounded fanout; it does not establish existence of a future flow, availability
of an occupied destination port, or terminal saturation. For an arbitrary-chain application, the concrete protocol wiring and source
queue must still instantiate these hypotheses.

## Connection to finite-chain composition

`Execution.signal` extracts a `Chain.Signal` from actual fire jumps, retaining
the exact number of emissions. `hasPacket_of_emission_witness` exposes both
outstanding packet obligations: exact event count and every actual emission date.
The concrete autonomous C result supplies its leaf packet from a real ledger.
The new common-birth factory also constructs its variable-K leaf, each physical
full-budget receiver and the global causal weave for arbitrary finite depth.
It uses `HybridCadencePacketRelay` with directly proved high bounds[0.16,0.26].
The older `Chain.Refinement.RelayLaw` still requires narrower bounds; it remains
an explicit premise of that older API and is not assumed by the new factory.

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
[EVERY_N_PLAN.md](EVERY_N_PLAN.md). The validated baseline figures above remain
those of the N=3 commit; current finite-chain validation and checkpoint
history are recorded there.

Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Fresh CI status
is reported separately on the PR.
