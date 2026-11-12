# Routed calendars, teaching and cadence

Part of [physical execution semantics](../HYBRID_EXECUTION.md).

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
