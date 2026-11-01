# Physical execution semantics and analytic refinement

The complete protocol-to-abstraction theorem remains open. The modules below
prove physical flow and invariant results needed for that theorem. The
complete conditional three-cell prefix is derived below; its reaching traces
are still supplied. Constructive source-driven existence now reaches the
complete first-train preparation at128 from the original A birth queue. They now derive an isolated silent input's absence of
emissions and total ERROR dose, and extract the first firing of an isolated
learned input and its exact single-emission count. From the declared prepared
section the learned-input case now returns and preserves all memories. Sensor
triggering and the protected auxiliary cycle are also extracted from actual
executions.

## Physical definitions

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
source-driven construction below covers every READY A birth through its
first three weak inputs and the first actual output in (24.3,24.9).
Its FAST/SLOW continuation and the protected input now return to READY and
consume source40. The subsequent learned-source iteration now reaches128;
the second source train and later network continuation remain open.

## Constructive first-source existence

`birth_protocol_first_mark_exists` has no incoming `Execution` premise. Its
inputs are A's `BirthState`, its `PhysicalBox`, initially READY auxiliaries,
and the exact queue
`sourceTrain 0 0 0 8 16 ++ sourceTrain 0 0 160 8 16`.

It constructs a real `Jump.arrive` for the token at zero, an explicit positive
`Flow`, and a real `Jump.mark` at the first sensor threshold. The terminal date
lies strictly between 0.01 and 0.025. `CompleteThrough` holds at that date:
all instantaneous events due at this endpoint have been discharged. There are
no emissions. The final queue is definitionally exactly the fifteen sources
at 8..120 followed by the sixteen at 160..280, hence thirty-one tokens.
All log-gains and recovery retain the own birth values. `PhysicalInvariant`
and `RawValid` hold, including reserve in [50,100]. The active raw origin
survives MARK; neither the pulse nor the main charge is reset.

The construction separates these obligations:

- `HybridQuietFlowExistence` constructs zero-current READY relaxation for
  arbitrary initial coordinates, memories and reserve. Queues may contain
  future sources; the flow cannot pass their earliest deadline. Strictly
  future sources give a saturated horizon. Every READY birth member is covered.
- `HybridSourceProgress` extracts an actual earliest queued token and constructs
  an eligible arrival, removing one occurrence. Finite simultaneous batches
  are executable when their raw slots are free and pairwise distinct. Remaining
  occurrences retain their multiplicity, and the first protocol successor has
  its exact thirty-one-token queue.
- `HybridScalarFirstCrossing` constructs the first crossing of a continuous
  scalar response by compactness and the intermediate value theorem. Strict
  preguards hold before that root; no monotonicity or observed event is assumed.
  The physical sensor response yields a root in (0.01,0.025).
- `HybridBirthPulseGain` derives the own birth-gain bound and the first main
  response's absence of firing directly from the declared birth family.
- `HybridReadyFlowExistence` constructs every coordinate and the exact energy
  response to one fresh pulse. Its energy work includes both the main input
  drive and the auxiliary input work. The integral equations, guards, raw
  support and pending urgency are proved, rather than supplied as a trajectory.
- `HybridGuardNoJump` derives terminal saturation from strict mode guards,
  strictly future raw expiries and strictly future delivery dates.
- `HybridFirstInputMark` discharges the two active analytic preguards using
  physical bounds and the first-crossing theorem, then composes the real moves.

The generic input constructor is limited to an all-READY span before raw
expiry. Its guard bounds and queue deadlines are explicit; the birth-level
factory discharges them from the actual initial source queue. General progress
cannot follow from queue causality alone: simultaneous arrivals to the same
occupied raw slot can deadlock. Port availability must therefore be derived
from the constructed protocol schedule. No global priority is imposed on
compatible simultaneous events.

This gives non-vacuity for the first MARK of the written training protocol.
The next construction extends it through the complete first weak cycle.

## Constructed complete first weak cycle

`birth_protocol_first_weak_cycle_exists` assumes only the original A birth,
its physical fabrication box, initially READY auxiliaries and the exact
thirty-two-source queue. It constructs a `BirthFirstWeakCycle`; no execution,
threshold date, case word or desired dose is an input.

The object's actual `execution` starts at that birth, delivers exactly source at 0,
and reaches time 7.5 with `CompleteThrough`. There is no output. Its actual
ERROR ledger is 0.6 on port 0, all MARK ledgers are zero, port 0's own birth
log-gain increases by 0.6, the other birth gains and recovery are unchanged,
and all main/auxiliary modes are READY. Raw is absent. The queue is exactly
`sourceTrain 0 0 8 8 15 ++ sourceTrain 0 0 160 8 16`, retaining all thirty-one
future tokens. `PhysicalInvariant` and `RawValid` hold. Main charge follows its
real pulse response and subsequent relaxation; no exact resting reset is made.

`HybridFirstInputSilent` extends the constructed first MARK through its real
exponential decay and SILENT entry before 0.05. `HybridFirstCycleSchedule`
derives ERROR entry in (0.99,1.23) and complete auxiliary return after 1 and
before 419/300 directly from the physical rate boxes.

`HybridFirstInputError` constructs SILENT continuation in all three cases:
ERROR starts before raw expiry at 1, at the same date, or after it. A SILENT flow
is split at expiry when necessary, the real `Jump.rawEnd` removes only the raw
tag, and the actual sensor charge continues across that cut. At a simultaneous
expiry/ERROR boundary both orders are legal; the constructed witness chooses
one without imposing a priority on the semantics. Queue, charge, energy and
own memories are preserved at every instantaneous transition.

`HybridErrorTailFlowExistence` constructs ERROR with optional old raw and an
arbitrary current sensor charge in (0.025,0.1]. It uses an integrating-factor
convolution for main charge and energy, including the changing gain in the
remaining raw current. The energy cost includes auxiliary drain, ERROR learning
and actual input drive. Positive reserve and open headroom are proved from
initial physical bounds; they are not supplied as a trajectory. The formulas
also cover coincident exponential rates without division by their difference.
An integral flow may end exactly at raw expiry; the field equality on the open
interval suffices, and a separate real rawEnd is still required.

`HybridErrorCompletion` constructs the whole remaining ERROR phase and its
auxiliary READY jump. For early ERROR it first constructs the raw-bearing part,
executes rawEnd at 1, then starts the no-raw suffix from its actual intermediate
sensor charge and gain. The cut preserves both the original completion date
and the budget `z + 8*(m-0.025)`. Its remaining dose is `8*(m-0.025)`, so the
suffix does not incorrectly restart a full 0.6 dose. The first-cycle schedule
proves completion strictly after raw expiry; this is an explicit caller proof.

`HybridBirthFirstWeakCycle` composes these moves and constructs a quiet suffix
to 7.5. Only then does the existing `Execution.silent_pulse` theorem classify
that already constructed execution and derive its doses, READY coordinates
and memories. No existence assumption is hidden in this reuse. Saturation is
claimed at 7.5, strictly before the pending source at 8; it is not claimed at 8
without delivering that source.

Both physical fabrication boxes and every READY member of A's perturbed birth
family are covered. Routing is arbitrary here because the constructed weak
prefix never fires. The next section extends the first weak input through the other two weak
inputs and the first actual firing. Preparation, later births and the trace
reaching 789.9 remain to be constructed. In particular, source at 8 must retain the real residual charge; its main
charge cannot simply reuse the original narrow birth band. Physical every-N
existence/progress remains open.

## Constructed first firing from the birth queue

`birth_protocol_first_fire_exists` takes only A's READY birth family,
`PhysicalBox`, initially READY auxiliaries and the full original thirty-two
sources. It constructs a `BirthFirstFire` and its actual birth execution.
There is exactly one main emission, at a date strictly in (24.3,24.9). Its
first firing equation uses the real residual charge, not a resting-reference
latency or an assumed output date. Both fabrication boxes are covered.

The weak prefix is constructed first:

- The complete first cycle ends at 7.5. A real quiet flow then reaches8 and a
  real `Jump.arrive` consumes exactly its head token. The queue tail is kept
  in its original order, including every future occurrence.
- `HybridWeakInputErrorExistence` proves the main-response margin for current
  READY charge up to 0.14 and actual weak gain up to 7/6. It uses the existing
  ERROR-entry record and all three raw-expiry branches; it does not impose the
  original narrow birth-charge bound at the later sources.
- `HybridWeakInputCycleExistence` constructs a whole isolated weak cycle for
  arbitrary cell/port and source origin, from current physical invariants,
  READY coordinates, a single fresh raw input and future tokens at least8
  later. Its horizon is source time plus 7.5, and its pending queue is unchanged.
- `HybridQuietSourceArrival` constructs waiting and exact head delivery with
  the real relaxed q/m values. It preserves READY bands, physical invariants,
  raw validity, gains and recovery. Saturation after delivery requires any
  remaining simultaneous tokens to be strictly future.
- `HybridBirthWeakSources` discharges both weak-gain bounds from the cell's
  own birth log-gain plus its earlier actual ERROR doses. `HybridBirthWeakPrefix`
  assembles inputs0,8,16 and fresh input 24, with no previous execution supplied.

At24 the main cell is still READY. Four source tokens have been consumed,
but only three ERROR cycles have completed: the actual ERROR ledger is1.8,
port 0's own birth log-gain has increased by1.8, and recovery is unchanged.
The fourth pulse remains fresh, the pending queue is exactly the twelve
sources32..120 followed by sixteen sources160..280, and the actual gain lies
in [1.8,2]. The true carried q/m values remain in their READY bands.

`HybridFirstLearnedFireExistence` constructs the receiving sensor's first
MARK and SILENT spans for this learned gain. It constructs the first main
threshold root in (0.3,0.9), proves the main guard strictly before that root,
and constructs the real SILENT-mode flow followed by `Jump.fire`. The
auxiliary SILENT charge remains strictly above 0.1 at firing. It does not
reuse the low-gain nominal-silence bound for this learned input.

`HybridBirthFirstFire` composes the weak prefix and this firing. The main is
FAST at q=1, the original raw origin24 is preserved, its own gain remains
birth plus 1.8 and its own recovery is unchanged. No fourth ERROR dose or
protected MARK dose is invented. All twenty-eight future source tokens
remain, followed by every token returned by `route 0 actualFireTime`.
No token filtering or multiplicity loss occurs.

For a generic supplied router, saturation after FIRE requires its newly
issued tokens to be strictly future. The actual closed contact before B's
birth satisfies this, and `birth_protocol_first_fire_complete_exists`
constructs the saturated first-output prefix with the empty router. It does
not claim saturation for an immediately due routed delivery without executing
that arrival. `PhysicalInvariant` and `RawValid` hold at the firing state.

The state after FIRE is FAST with raw still active and the trained auxiliary
still SILENT. The next construction reaches the actual FAST exit and the
protected MARK at 32. Completing its later return and preparation train remains
open. After a later birth,
other cells may already be active: the all-READY single-input constructors
alone do not yet supply those concurrent network flows. Global existence,
the trace reaching 789.9 and the physical every-N result remain open.

## Constructed FAST exit and protected MARK at 32

`birth_protocol_protected_mark_exists` assumes only the original one-cell
READY birth, its physical fabrication box, initially READY auxiliaries and
exact thirty-two-source queue. The contact is closed before B's birth.
It constructs the actual first output, FAST exit, SLOW arrival at 32 and the
full protected MARK, without an incoming execution, case word, expected dose
or event date. Both fabrication boxes and all READY birth perturbations hold.

`HybridProtectedMainFlowExistence` constructs FAST/SLOW with auxiliary
READY/SILENT/ERROR. Current gain and recovery remain fixed: ERROR learning
is closed while the main is protected, and there is no active MARK in these
pieces. Energy includes the true main work and auxiliary input/drain. Old RAW
origins are retained, expiry may be a flow endpoint and a real rawEnd is still
required. Coincident exponential rates are covered.

`HybridFirstFireSchedule` derives the sharper first FIRE bound after24.4:
READY charge up to.14 and learned gain up to2 stay below1 through.4. This
orders the auxiliary return strictly before FAST end. `HybridFastAuxLeg` and
`HybridBirthFirstFastEnd` construct the real SILENT/ERROR/READY phases across
raw expiry25 in all three boundary orders. The last FAST flow reaches q=.25
at actual FIRE+1, followed by the real fastEnd jump into SLOW. Nothing resets
q to.1 or changes the own birth recovery.

`HybridFirstSlowSource` transports q=.25 by its own recovery near.08 to32,
then consumes the real head source. The main is still SLOW, with q strictly
in (0.14,0.16); its trained auxiliary is READY at.025. Source32 is delivery five,
and the queue retains exactly eleven sources40..120 plus sixteen160..280.

`HybridSlowInputMarkExistence` constructs the first real sensor threshold,
SLOW/READY flow and MARK jump. `HybridSlowProtectedMarkFlowExistence` then
constructs m(t)=m0*exp(-lm*elapsed), b(t)=b0+(m0-m(t))/2 and q using the integral
of this changing b. The true energy work is 1.1+1.5*lm*m(t), including MARK
activity. Positive power and open recovery headroom are proved analytically
from the current physical coordinates. Full MARK ends at m=.8 with b increased
by.1; its real SILENT jump preserves all coordinates. No instantaneous recovery
jump is substituted into the main ODE.

`HybridBirthProtectedMark` composes the moves from birth to a real endpoint
in(32.01,32.05). The actual execution has five deliveries0,8,16,24,32, one
emission at the earlier first FIRE, ERROR 1.8 and MARK 0.1. Own z00 remains birth
plus1.8, own b becomes perturbed birth plus.1 rather than nominal.18. The MARK
ledger follows from the actual recovery balance and per-port MARK sum; other
ports have zero MARK because their real input calendars are empty. The small
proof-only source cast aligns definitionally equal snapshot names and preserves
ledger/deliveries; it introduces no path or coordinate change.

At the endpoint main is still SLOW, q is in[.136,.16], auxiliary0 is SILENT at.8,
and raw retains its original source32 origin. All27 future tokens are retained.
`CompleteThrough` holds: main/aux guards are strict, raw expiry33 is future and
pending sources are all at least40. Physical invariants and raw validity hold.
The following construction completes the auxiliary cycle, SLOW reopening and
prepared entry40. The remaining preparation train, later births/concurrent
cells, full789.9 trace and every-N existence remain open. No READY state is
substituted at 32 or after its short MARK.

## Constructed protected return and prepared source40

`birth_protocol_prepared40_exists` has only the original BirthState,
PhysicalBox, initially READY auxiliaries and full thirty-two-source queue as
premises. It extends the constructed protected MARK through genuine guarded
returns, a quiet waiting flow and the actual sixth delivery at40.

`HybridSlowAuxLeg` retains the current charge clock q0*exp(-b*elapsed).
The carried q0 is at least0.136 and the own acquired b is at most0.18001.
Through the remaining auxiliary duration at most41/30, the charge stays
strictly above0.1025 and hence above the SLOW return guard. Its sensor clocks,
energy, gains and recovery use the actual current coordinates.

`HybridProtectedAuxReturn` constructs SILENT, ERROR and auxReady jumps,
including all three possible orders of RAW expiry33 against ERROR entry.
The auxiliary return occurs strictly between33.11 and33.417, with raw absent,
trained sensor at0.025, all auxiliaries READY and main still SLOW. Protected
ERROR changes no gain. Queue, gains and recovery are preserved.

`HybridSlowReopenExistence` constructs the raw-free SLOW flow up to its own
root log(q/0.1)/b. This duration is positive and less than4; the real reopen
jump occurs before38 at charge exactly0.1. The quiet waiting flow preserves
this exact charge until the actual source40 head delivery.

`HybridBirthPrepared40` composes these physical executions from birth. At40,
main and auxiliaries are READY, the prepared recovery band holds, q=0.1 and
RAW has fresh origin40. Exactly six sources0,8,16,24,32,40 were delivered and
exactly one main output occurred at the first FIRE. The ledger gives ERROR1.8
and MARK0.1; own birth gain+1.8 and own birth recovery+0.1 are retained.
Exactly26 future sources remain: ten at48..120 and sixteen at160..280.
PhysicalInvariant, RawValid and CompleteThrough at40 hold. The raw-free
reopen state and the fresh-source endpoint are distinct actual snapshots;
no raw-free assertion is made at the source40 endpoint.

The following construction extends these learned preparation inputs through
the first complete train. Subsequent births/network flows, full789.9 and
every-N existence remain open.

## Constructed complete initial preparation

`birth_protocol_preparation_exists` assumes only the original one-cell
BirthState, PhysicalBox, initially READY auxiliaries and exact full
thirty-two-source queue. It constructs an execution through128 and derives
its complete `BirthSourceTrain` outcome. No reaching execution, output
count, desired dose, pulse word or firing calendar is supplied.

`HybridLearnedFastEnd` generalizes the earlier actual FAST continuation to
the current source time. Its first firing is derived in(source+0.4,source+0.9).
The auxiliary return and RAW expiry occur before actual FIRE+1; the real
fastEnd jump enters SLOW at q=0.25, preserving own gains and recovery.

`HybridPreparedSlowReturn` uses the current acquired recovery in its true
root log(2.5)/b. The positive duration is below5.6. Combined with the actual
firing latency and FAST duration, the real reopen occurs before source+7.5.
A quiet flow then reaches that section with all modes READY, q=0.1 and raw
absent. This is a built execution, not selection of a return from a trace.

`HybridPreparedLearnedCycle` composes these witnesses. Each current learned
pulse gives one actual emission, no delivery and unchanged memories.
`HybridPreparedLearnedTrainExistence` recurses over the future source queue:
the current raw is already delivered, so count future tokens give count+1
pulses. Each step constructs the cycle, a waiting flow and exactly the next
head delivery at source+8, then recurses with all current coordinates intact.
The arbitrary later queue is retained exactly.

From the fresh source40 entry, ten future sources48..120 yield eleven
learned emissions through127.5. `HybridBirthPreparationExists` then builds
a quiet flow to128 and joins this actual execution to the earlier birth
prefix. It proves the complete delivery calendar0,8,...,120 before applying
the existing analytical `birth_low_train` theorem to that constructed trace.

At128 the outcome is twelve total outputs, ERROR1.8, MARK0.1, own birth
gain+1.8 and own birth recovery+0.1. Other own memories are preserved.
Main and auxiliaries are READY, q is exactly0.1, raw is absent, physical
invariants and raw validity hold, and `CompleteThrough` holds at128.
All sixteen second-train sources160,168,...,280 remain queued. Actual
later births, simultaneous active cells and global progress are still to be
constructed; this does not establish the full789.9 or every-N theorem.

## Checked implications

| Module | Consequence proved from the operational equations | Boundary |
|---|---|---|
| `Refinement` | Exact per-port ERROR and MARK integrals; telescoped gain/recovery balances; recovery equals the sum of all MARK contributions; queue conservation; actual emissions | Quantifies over finite admissible executions |
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
| `HybridBirthPreparation` | With both 16-token source trains already queued, derive preparation at 128, twelve emissions and exact doses through 160, then transfer the prepared state and acquired memories across a birth at 160 | Actual executions, READY receiving auxiliaries, empty pre-birth routing and the birth date are supplied; post-birth calendars and existence remain open |
| `HybridPreparedCalendar` | Derive a unique real rest-started firing latency in (0.3,0.9), identify actual learned-output dates and translate an entire separated input calendar by that one latency | Exact initial q=0.1, strong-gain and current-invariant bounds, actual receiving-cell calendar and return horizon; fresh wire jitter remains separate |
| `HybridCellDueSources` | Exact strictly past receiving-cell source prefix and retained later queue, with other-cell traffic present | Filtered initial queue, no incoming route at actual emissions, future terminal queue and strict source-date separation |
| `HybridRoutedInputs` | Actual receiving-cell deliveries equal the ordered issued wire tokens while future external sources remain pending | Issued tokens strictly before the endpoint, external sources strictly after it and a future terminal queue |
| `HybridContact` | Causal half-open gated wire with fanout at most one; actual routed tokens extracted from actual sending emissions | The target projection of routing at actual emissions is fixed to the declared contact |
| `HybridPreparedContact` | Derive actual wire inputs from a prepared sender's queue and ODE; specialize to sixteen B arrivals with fresh jitter and dates in (160.6,281.3) | A input 160 is already active; fifteen pending successors, current bounds, no return route to A and B sources at 320 or later; B output classification and staged-boundary queue connection remain open |
| `HybridRestingInput` | A READY cell retains its coordinate bands and memories through the quiet prefix before its first actual received input | Other-cell traffic is retained; initially absent raw inputs and READY bands |
| `HybridBirthQueueBridge` | Couple source160 raw absence/activity to the exact remaining queue, and preserve it across birth | Actual first phase with both initial source trains, empty pre-birth routing and birth at 160 |
| `HybridBTeachingPhase` / `HybridBTeachingCalendar` | Derive B14, ERROR0.6, MARK0.1 and prepared return from actual sixteen-input wire dates, including the quiet pre-input prefix | Fresh READY/current bounds, low birth recovery and the derived separated calendar |
| `HybridTeachingActivation` / `HybridTeachingBoundaryPhase` | Select the pending source160 after birth without changing physical coordinates or losing future B tokens; cover both legal boundary orders | Given execution reaching 319.9 and the proved raw/queue alternatives |
| `HybridTeachingActivePhase` | Compose the actual A16 source train and B14 wire-response phase with memory preservation | Current physical bounds and the source/route state, discharged by the staged theorem |
| `HybridEntryRouter` / `HybridStagedTeaching` | Instantiate forward/reverse contacts and derive cumulative A28/B14 plus prepared memories across B's actual birth | READY A birth, given staged executions at 160/319.9, B sources due from320 and bounded independent wire delays; no existence/progress claim |
| `HybridTeachingQueueClosure` | At319.9 A has no pending source and B retains exactly its future external birth queue | Actual queue conservation, routing windows and causal terminal future queue; no supplied output count |
| `HybridResidualLatency` / `HybridResidualPreparedCalendar` | Positive READY residual cannot delay the actual first firing; later outputs share the same-gain rest-root latency | Initial q>=0.1, prepared gain/section and actual separated input calendar |
| `HybridPreparedLearningTrain` | Three actual low-gain silent inputs give ERROR 1.8/MARK0, then a prepared learned train emits once per input | Current prepared section, nominal low gain, real receiving-cell dates with minimum gap 7.5 and final quiet horizon |
| `HybridFeedbackSender` / `HybridFeedbackInitialSource` | Select direct B sources 320..440 and derive thirteen actual B outputs, retaining the first residual latency and later source tokens | B's actual initial queue, current prepared nominal return port and no incoming B route |
| `HybridFeedbackCalendar` / `HybridFeedbackReceiver` | Derive thirteen actual A return arrivals with fresh delays, then three silent inputs and ten learned outputs | Real B output calendar, initially empty A queue and concrete return contact; current prepared A bounds |
| `HybridFeedbackEpoch` / `HybridReciprocalEntry` | Physical A38/B27 and derived port gains/recovery at 459.9, with terminal preparation, raw validity and reserve | Given staged teaching and continuing executions, fresh birth160, exact source queues/contact windows; no global existence/progress claim |
| `HybridFeedbackQueueClosure` | Empty A queue and exact remaining future B sources at 459.9, with multiplicities | Real B sender outputs, source conservation and future terminal queue |
| `HybridFastTeachingCalendar` / `HybridPreparedSourceContact` | Generic sixteen-input physical sender/contact and fresh receiver teaching at arbitrary cells and epochs | Actual source queue, current physical bounds, gated contact and a complete supplied execution |
| `HybridSourceActivation` / `HybridCIntroductionBoundary` | Old cells remain prepared through 480; the source due at birth is either pending or already fresh | Actual reciprocal prefix and exact remaining B sources; no event-priority assumption |
| `HybridCTeachingRouter` / `HybridCIntroductionActivePhase` / `HybridCIntroductionBoundaryPhase` | Actual B16/C14 and quiet A across both legal birth/source orders | B-to-C port-1 contact [480,630), current bounds and C's own READY birth data |
| `HybridCIntroductionQueueClosure` / `HybridStagedCIntroduction` / `HybridCEntry` | Physical cumulative A38/B43/C14 at 639.9; own memories and future C source queue retained | Actual executions and births supplied, independent device parameters and wire delays; continuation is composed below, existence remains open |
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
| `HybridCadenceCascade` / `HybridCadenceEntry` | Cumulative A54/B61/C34, own memories/recovery, all cells at rest with no raw and an empty queue at789.9 | Original source programs, physical birth family, actual traces/births and independently bounded wire functions; existence/progress still not constructed |


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

`CompleteThrough` is a premise of this full-queue corollary, so existence and
progress remain open. The first phase covers the written READY birth family,
not immediate input into an ERROR-born receiving sensor. The prefix refinement
below retains later sources and connects the state at 160 to a scheduled birth.
The A-to-B teaching and B-to-A return routes are instantiated below. Later
C/cadence protocols still require their physical proofs.


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
now connected below, followed by the physical B-to-A return epoch. Later C
introductions, cadence, complete protocol counts and execution existence still
need their proofs. A one-birth execution is supplied to these theorems; it
is not a construction of the whole reciprocal trajectory.


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
outputs. Protocol-specific execution existence remains open.


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
statement. The reciprocal-entry theorem below fixes it and covers 459.9. Later
C/cadence, probes, remaining enclosure membership and full-chain physical
refinement remain open.
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
[50,100], and raw validity is propagated. This remains conditional on actual
executions reaching 160,319.9 and459.9 and the genuine fresh birth at 160. A's
initial auxiliaries are READY; this is not an ERROR-born generalization.
The C introduction and cadence initiation described below extend this prefix.
The composed period-four cascade below extends this result. Probes,
remaining fine enclosures, global existence/progress and physical every-N
refinement are still open. Fixed fabrication parameters and canonical pulse
amplitudes remain the scope; noise and drift need separate extensions.

## Physical C introduction through 639.9

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

This is still a conditional physical prefix: actual executions reaching the
listed endpoints and fresh births at 160 and 480 are supplied. It does not
construct existence/progress. The later sections instantiate the cadence
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
The actual complete cadence execution through 789.9 remains a premise; the
prelude does not prove its later output counts or construct its existence.

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

This is a complete conditional three-cell protocol prefix, not a construction
of global existence/progress. Actual traces reaching160,319.9,459.9,480,639.9
and789.9, with fresh births at160/480, are supplied. A starts with READY
auxiliaries, an explicit subfamily of `BirthState`. Fabrication parameters
are fixed independent box members; initial coordinate perturbations and
bounded fresh wire delays are retained. There is no probabilistic
independence assertion, additive dynamic noise, drift or device fault model.
Frozen probes, later cuts/copies and physical refinement for arbitrary N
remain distinct obligations.

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
of an occupied destination port, or terminal saturation. Concrete protocol
wiring and initial queue adequacy still need to be proved.

## Connection to finite-chain composition

`Execution.signal` extracts a `Chain.Signal` from actual fire jumps, retaining
the exact number of emissions. `hasPacket_of_emission_witness` exposes both
outstanding packet obligations: exact event count and every actual emission date.
It connects to PR #6's interface but does not supply its leaf or `RelayLaw` witness.

## Remaining obligations for the complete theorem

1. Extend the checked physical A38/B27 reciprocal entry through 459.9 to C's
   later introduction and the remaining protocols, including their source
   queues, contacts and port separation. Both source/birth orders at 160 and
   the concrete two-cell teaching/return contacts are connected.
2. Prove the main/auxiliary interactions in each actual pulse case, including
   combined MARK/ERROR, strict cap inactivity and absence of extra firings.
   The isolated silent input and its total dose are proved with variable-gain
   raw-tail overlap. The prepared learned-input case now has an exact single
   emission, zero ERROR/MARK doses, preserved memories and an actual READY
   return. The combined case and the pulse cases’ protocol occurrence
   remain open.
3. Establish sound real enclosure membership for the remaining root, calendar,
   recovery and residual-tail expressions in the certificates. Exact comparisons
   of stored endpoints alone remain insufficient.
4. Prove protocol-specific execution existence, extension/progress and terminal
   saturation for all compatible event orders. Instantiate the checked uniform
   finite-prefix event budget with the concrete source queue and routing fanout.
5. Lift the resulting physical case theorem through preparation, the cadence
   cascade, retained probes and the packet induction for every finite chain.

Certificates, manifests, recordings and the pinned prototype ZIP retain their
existing identities and scope. No theorem asserts the complete physical result,
assumes a recorded pulse-case word, or treats finite counter replay as a trajectory
proof. The partial-dose calculation is not a reachable training counterexample.

## Validation

Use the pinned Lean/Mathlib versions and the standard project workflow:

```sh
lake build
lake build Audit
python scripts/check_audit_negative.py
python scripts/check_sources.py
python scripts/generate_evidence.py --check
python scripts/check_negative.py
python scripts/check_hybrid_negative.py
python scripts/check_hybrid_analytic_negative.py
python scripts/check_hybrid_event_negative.py
python scripts/check_hybrid_phase_negative.py
python scripts/check_hybrid_pulse_negative.py
python scripts/check_hybrid_return_negative.py
python scripts/check_hybrid_training_negative.py
python scripts/check_hybrid_bootstrap_negative.py
python scripts/check_hybrid_protected_negative.py
python scripts/check_hybrid_source_negative.py
python scripts/check_hybrid_cell_negative.py
python scripts/check_hybrid_local_negative.py
python scripts/check_hybrid_invariant_negative.py
python scripts/check_hybrid_staged_negative.py
python scripts/check_hybrid_boundary_negative.py
python scripts/check_hybrid_calendar_negative.py
python scripts/check_hybrid_routed_negative.py
python scripts/check_hybrid_teaching_negative.py
python scripts/check_hybrid_reciprocal_negative.py
```

Every negative check first compiles its positive control. Existing physical
checks reject under-threshold firing, nonconsuming delivery, closed-gate positive
actuation, a rounded partial dose and an omitted raw current. Analytic controls
reject altered FAST/MARK durations, an invalid reserve floor and removal of the
attenuation of a raw tail. The axiom audit imports all new modules through KernelR.
Event controls reject removal of the unfinished-FAST allowance, altered FAST
departure and auxiliary bounds, strict future dating of a token due now, and
omission of routed fanout from the published global budget.

Phase controls reject an absent received input, altered sensor/error/return
dates, a shortened protected cycle, freezing a variable gain, an incorrect
clipped-dose coefficient, a retained expired raw current, and omission of
routed tokens from delivery provenance.

Protected-input controls reject a missing MARK dose, two recovery increments,
a positive ERROR dose, an extra emission, changed gains, a missing READY return
and an altered resting charge. Each changed claim must fail with a Lean diagnostic.

Source controls reject a missing source token, changed delivery date/raw origin,
wrong isolation segment, altered prepared-train counts or MARK dose, altered
warmup doses/outputs, fabricated preparation at source zero, and changed first
source-phase output/dose/memory conclusions.

Multicell controls reject erasing other-cell arrivals or future pending tokens,
replacing cell-specific conservation with a global claim, altered arrival dates,
extra prepared outputs, omission of the first gap and weakened gap/final-horizon
requirements.

Local-invariant controls exercise the prepared pulse and variable-gap train
without a common-birth history argument, and reject a protected-input
substitution, a receiving-gain increase, an extra output and a missing firing.

Current-invariant controls reject a strengthened reserve floor, loss of possible
cap contact, a missing silent ERROR dose, a missing protected MARK dose, doubled
recovery gain and removal of the actual first strong emission.

Staged-birth controls reject changes to old gains/recovery or the clock, loss of
old pending tokens, fabricated preparation or inherited gains in the fresh cell,
source injection into an existing cell, changed due-date bounds, omitted old
learning, invented pre-birth learning in the new cell and an altered reserve
floor. Nominal fresh coordinates and an empty-source birth are also constructed.

Boundary controls reject replacing the strict source cutoff by a non-strict one,
losing deliveries or learning across a flow cut, deleting future pending tokens,
using the wrong READY threshold, forcing a terminal source to have arrived,
changing preparation counts or resting charge, resetting the old gain at birth,
and moving the 160 contract to 168. A zero-duration trace with a source due now
still pending is also constructed.

Calendar controls reject a strengthened latency bracket, an altered firing
threshold, a shifted supposedly unique root, omission of the actual input
origin or initially active input, and replacement of exact resting charge by
the broader prepared band. A real root for gain 2 is constructed independently
of any assumed execution.

Routed controls reject changing the contact's half-open endpoints, erasing
fresh wire jitter, using the receiving cell's emissions as the sender, mixing
sender and receiver ports, deleting other-cell traffic or future pending
queues, forcing delivery at the terminal date, changing the derived sixteen
B deliveries, and replacing the proved coarse date bracket by a sharper
unproved certificate bound. A causal contact with fanout one is constructed.

Teaching controls compile the full concrete staged-epoch contract and reject a
missing source160, early B external sources, a shifted birth date, altered A/B
counts or B doses, extra A learning, inherited recovery in B, an incorrect
terminal mode, instantaneous learning during source activation, lost future
B tokens, inconsistent raw/queue alternatives and closure of the reverse gate
at its actual opening date.

Reciprocal controls compile the full source-queue/contact contract and reject
missing B novelty sources, the wrong receiving port, a premature endpoint,
altered cumulative38/27 counts, missing return ERROR or extra MARK, extra gain
or recovery, forcing the first residual latency to equal the rest reference,
reusing the regular upper wire-gap bound for the first gap, and loss of the
later external B queue.

Cadence controls compile the actual source-to-prelude and physical mixed-pulse
contracts. They reject a missing C source, treating the fourth arrival as a
fourth completed ERROR, losing a future token, reusing the period-eight charge
cap, erasing the fresh raw, an invented early B output, weakened mixed-input
bounds, missing mixed ERROR/MARK, an extra recovery dose or a fictitious reset
of residual charge. They also check the MARK-only case, required high-gain
recovery, exact learned count, firing/return bounds, the three-dose real root,
the finite MARK-ramp correction and absence of extra high-gain train outputs.

Complete-cascade controls compile the full original birth/source/contact
contract and reject a missing C source, premature final endpoint, weakened
wire bound, altered cumulative54/61/34 or new-block16/18/20 counts, wrong own
recovery/gain, cross-cell inherited C memory, a nonempty terminal queue,
missing additional ERROR/MARK and an altered final resting charge.

Constructive-existence controls compile the original birth/source factory
without any incoming execution. They reject missing initial sources, altered
first-crossing bounds, an incorrect MARK charge, invented gain/recovery doses,
extra deliveries or outputs, erased raw origins, lost future tokens, a reset
reserve, non-strict delivery deadlines for saturation and omitted input work.

Complete-weak-existence controls compile the full original birth/source
factory without an incoming execution, for every declared fabrication choice.
They reject a missing source, a premature or unsaturated endpoint, a wrong
source token, invented output, double ERROR, protected MARK during READY,
wrong own memories/recovery, lost future trains, retained raw, incorrect
terminal modes, a full-dose restart after an intermediate cut, a shifted ERROR
completion date and omitted ERROR energy work.

First-firing controls compile the complete birth-to-output existence factory
without an incoming execution. They reject missing initial sources, non-strict
routed deadlines for saturation, wrong weak-prefix dates/doses/delivery counts,
lost future sources, erased fourth raw, a premature FAST state, discarded
relaxation, weakened weak-gain bounds, a horizon detached from its origin,
wrong firing bounds, missing output, wrong main mode/charge, lost issued tokens,
a reset raw origin, an invented fourth ERROR and an extra recovery dose.

Protected-MARK controls compile the full birth-to-MARK at 32 factory without an
incoming execution. They reject altered FAST duration/mode/quarter charge,
unexpired old raw, fictitious READY at 32, misplaced recovery learning,
missing MARK or extra ERROR, copied nominal recovery, premature READY after
MARK, wrong SILENT floor, reset raw origin, lost future tokens, missing fifth
delivery, a second output, constant-b main charge during changing recovery
and omitted protected MARK energy work.

Prepared40 controls compile the full birth factory without a continuation.
They reject missing initial sources, wrong endpoint/saturation clocks,
premature main/aux modes, wrong reopen charge, stale RAW32, lost future tokens,
wrong sixth delivery, invented output or ERROR, missing MARK, copied nominal
recovery, altered suffix events, gain learning under SLOW protection and a
reopen clock that discards the current cell's own recovery.

Complete-preparation controls compile the original birth factory and the
learned iteration without a continuation. They reject changed initial or
remaining source counts, wrong horizon/saturation/calendar, stale raw,
wrong total outputs/doses, copied birth memories, wrong main mode, double
counting the current raw, discarded later queues and altered learned return
or FAST clocks.
