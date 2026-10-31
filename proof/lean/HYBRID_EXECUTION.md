# Physical execution semantics and analytic refinement

The complete protocol-to-abstraction theorem remains open. The modules below
prove physical flow and invariant results needed for that theorem. They do not
yet derive all four main-cell pulse cases or the full training calendars from
complete executions. They now derive an isolated silent input's absence of
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

Sources must be in the initial pending queue. `CausalRouter` states causality of
the supplied wiring; generic ledger identities do not require that extra premise.
There is no staged-birth or settings-copy operation. Those protocols need a
separate semantic extension or a proved reduction.

`Execution` retains arbitrary legal zero-time interleavings without a total event
priority. `simultaneous_fire_mark_orders` constructs both compatible orders for
simultaneous main-fire and auxiliary-MARK guards. It does not establish global
confluence or simulator coverage of all simultaneous events.

`CompleteThrough` requires reaching the horizon and discharging enabled jumps
and due deliveries, including events exactly at the horizon. `Flow.prefix`
constructs a valid shorter prefix of an existing flow; it does not construct a
future continuation. `birth_resting_complete_exists` exhibits a complete
positive-duration silent execution from a nominal READY state and proves that
this state belongs to `BirthState`, with the prescribed nominal log-gains and
an empty source queue. This is one concrete birth-family witness, not existence
for every initial state or for the training protocols; those remain unproved.

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
and the complete two-cell birth-to-preparation theorem remain separate obligations.

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

`CompleteThrough` is a premise, so existence and progress remain open. The first
phase covers the written READY birth family, not immediate input into an
ERROR-born receiving sensor. Later A-to-B/B-to-A routing and B's staged birth
still require their own semantic realization and calendar proofs.


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
does not yet derive the later incoming wire calendars or realize staged births.


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


`HybridInputBalance` retains every routed token in a multiset conservation law.
For empty routing, an execution complete after all supplied source dates has an
actual delivery list permuting the initial source queue. Filtering by cell/port
and chronological sorting gives the exact source-date list, including duplicate
tokens. This result remains conditional on a complete execution; it does not
establish source availability, port separation or progress.

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

1. Instantiate and review the semantics with the supplied protocols, including
   staged births where relevant, and prove routing adequacy and port separation.
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
