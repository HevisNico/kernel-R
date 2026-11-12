# Doses, the sensor cycle and isolated inputs

Part of [physical execution semantics](../HYBRID_EXECUTION.md).

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
