# The constructed protocol checkpoint

Part of [physical execution semantics](../HYBRID_EXECUTION.md).

## Constructed protocol checkpoint

The current original-birth protocol factory is
[`birth_protocol_complete_cadence_exists`](../KernelR/HybridBirthCadenceProtocol.lean).
It returns `ConstructedBirthCadenceProtocol`, retaining both actual births,
the two-cell phase between them and a complete three-cell phase480→789.9. Its premises are A's READY birth/source family, independent READY B/C newborns, fixed independent physical
parameters and five bounded delay functions. There is no reaching execution,
received calendar, prescribed dose/count or assumed firing date. Earlier
factories remain available independently.

| Constructed checkpoint | Derived state and traffic | Public factory / source |
|---|---|---|
| Initial preparation, 128 | A12; prepared READY, q=0.1, no RAW; ERROR1.8/MARK0.1; sixteen future A sources retained | `birth_protocol_preparation_exists` in [HybridBirthPreparationExists](../KernelR/HybridBirthPreparationExists.lean) |
| B birth and A160 delivery | A's acquired memories retained; B has its own independent newborn coordinates; 47 future external sources | `birth_protocol_b_birth_complete_exists` in [HybridConstructedBBirth](../KernelR/HybridConstructedBBirth.lean) |
| First B output, (169.1,170.2) | Actual interleaved A/B execution; B's output retained under the closed reverse contact | `birth_protocol_first_receiver_fire_exists` in [HybridConstructedReceiverFire](../KernelR/HybridConstructedReceiverFire.lean) |
| Common prepared section, 184 | Both q=0.1; B has full MARK0.1; fresh A184 RAW; 44 external sources | `birth_protocol_first_coupled_prepared_pair_exists` in [HybridFirstCoupledPreparedPair](../KernelR/HybridFirstCoupledPreparedPair.lean) |
| Complete first teaching, 319.9 | Cumulative A28/B14; both prepared, no RAW; all 32 B sources retained | `birth_protocol_first_coupled_teaching_exists` in [HybridFirstCoupledTeaching](../KernelR/HybridFirstCoupledTeaching.lean) |
| Fresh reciprocal input, 344 | Three actual Bport2 weak cycles, ERROR1.8, no new output/MARK; B's true q>=0.1; 28 future sources | `birth_protocol_feedback_weak_entry_exists` in [HybridFeedbackWeakEntry](../KernelR/HybridFeedbackWeakEntry.lean) |
| First reverse FIRE, F in (344.3,344.9) | Cumulative A28/B15; A remains at q=0.1; reverse Aport2 token due at F+backward(F); 29 pending tokens | `birth_protocol_feedback_first_fire_exists` in [HybridFeedbackFirstFire](../KernelR/HybridFeedbackFirstFire.lean) |
| First reverse receipt, H in (344.7,345.3) | The actual B-issued Aport2 wire is consumed; A has fresh RAW at H; B's true sender cut is retained; A28/B15 and28 external sources | `birth_protocol_first_reverse_wired_arrival_exists` in [HybridBirthFirstReverseArrival](../KernelR/HybridBirthFirstReverseArrival.lean) |
| Interleaved source handoff, 352 | Real A weak response and B FAST/SLOW return; actual B352 source consumed; A28/B15, own Aport2+0.6/Bport2+1.8 and27 sources | `birth_protocol_first_reverse_interleaved_pair_exists` in [HybridBirthFirstReverseInterleavedPair](../KernelR/HybridBirthFirstReverseInterleavedPair.lean) |
| Complete reciprocal epoch, 459.9 | Cumulative A38/B27; both prepared/q=0.1, RAW absent; own Aport2/Bport2+1.8 and sixteen B480..600 sources retained | `birth_protocol_reverse_teaching_exists` in [HybridBirthReverseTeaching](../KernelR/HybridBirthReverseTeaching.lean) |
| Genuine C birth and B480 delivery | Independent C newborn; A/B coordinates retained;41 tokens after birth,40 after actual B480 arrival | `constructed_c_birth_exists` in [HybridConstructedCBirth](../KernelR/HybridConstructedCBirth.lean) |
| First C weak response, 488 | Own Cport1+0.6, recovery unchanged; true weak cut and continuation retained; actual B488 delivered,39 sources | `c_weak_entry_exists` in [HybridCWeakEntry](../KernelR/HybridCWeakEntry.lean) |
| First C learned response, 496 | Real C FIRE and low-recovery SLOW path retained; B496 fresh,38 sources | `c_first_learned_boundary_exists` in [HybridCFirstLearnedBoundary](../KernelR/HybridCFirstLearnedBoundary.lean) |
| Common B/C prepared section, 504 | Protected C MARK0.1, own gain retained; both prepared, fresh B504,37 sources | `c_prepared_pair_exists` in [HybridCPreparedPair](../KernelR/HybridCPreparedPair.lean) |
| Complete C teaching, 639.9 | Cumulative A38/B43/C14; all prepared/q=0.1, no RAW; exact25 C640..736 sources | `birth_protocol_c_teaching_exists` in [HybridBirthCTeaching](../KernelR/HybridBirthCTeaching.lean) |
| Fresh cadence source, 652 | Three actual period-four weak C inputs; own Cport0+1.8, no MARK, carried q in[0.1,0.3]; A/B quiet and21 future C sources | `constructed_cadence_warmup_exists` in [HybridBirthCadenceWeakWarmup](../KernelR/HybridBirthCadenceWeakWarmup.lean) |
| First cadence wire, H in(652.7,653.3) | Actual C FIRE and C-to-Bport2 arrival; cumulative A38/B43/C15, B fresh RAW, exact C FAST cut and21 C656..736 sources | `birth_protocol_cadence_first_wire_exists` in [HybridBirthCadenceFirstWire](../KernelR/HybridBirthCadenceFirstWire.lean) |
| First relay receipt, H_A in(653.4,654.4) | Actual B FIRE issues the Aport2 token, actual arrival consumes it; A prepared/fresh RAW, B/C retained physical cuts, exact21 C sources | `first_cadence_relay_wire_exists` in [HybridCadenceFirstRelayWire](../KernelR/HybridCadenceFirstRelayWire.lean) |
| First cadence wave, F_A in(653.8,655.1) | Actual A FIRE; cumulative A39/B44/C15; A FAST/q=1, B/C actual cuts and continuations, exact21 C656..736 sources | `birth_protocol_cadence_first_wave_exists` in [HybridBirthCadenceFirstWave](../KernelR/HybridBirthCadenceFirstWave.lean) |
| First protected source, 656 | Actual C656 arrival; C remains SLOW with its true charge, A/B actual cuts and20 future C sources | `first_cadence_mark_source_exists` in [HybridCadenceFirstMarkSource](../KernelR/HybridCadenceFirstMarkSource.lean) |
| First protected MARK return, 660 | A39/B44/C15; C READY/q=0.1/RAW660, own recovery+0.2 and port0 log-gain+1.8; A/B retained cuts and19 C664..736 sources | `birth_protocol_cadence_first_mark_return_exists` in [HybridBirthCadenceFirstMarkReturn](../KernelR/HybridBirthCadenceFirstMarkReturn.lean) |
| Complete three-cell cadence, 789.9 | Cumulative A54/B61/C34; cadence A16/B18/C20; all READY/q=0.1, RAW absent, global queue empty; own active log-gains+2.4 and recoveries+0.3 | `birth_protocol_complete_cadence_exists` in [HybridBirthCadenceProtocol](../KernelR/HybridBirthCadenceProtocol.lean) |

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
[HybridBirthCadenceLocalC](../KernelR/HybridBirthCadenceLocalC.lean) constructs
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
The common-birth program also has [finite and maximal-run progress](../PROGRESS.md).
Finer operational robustness, retained probes and settings copies remain open.
The finite-chain construction is tracked in [finite-chain construction](../../../docs/FINITE_CHAIN_CONSTRUCTION.md).
