# Birth, preparation and the common latency

Part of [physical execution semantics](../HYBRID_EXECUTION.md).

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
