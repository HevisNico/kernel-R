# Phase-aware guarded admission

An occurrence carries its due date and its physical input. The calendar
fixes the phase as a function of the input address and due date. The lifted MARK
model chooses the bias, recovery coefficient and write footprint for
that phase. The dated trace consumes one earliest pending occurrence,
records its decision, and inserts its routed descendants. A causal
router gives a chronological decision word. In a native admission
calendar the full contact key also retains the port.

## Guarantees and timing

`PhaseAdmission.network_memory` transports the MARK bounds, strict rail
headroom, stabilization, nominal error invariance, FIFO continuation
fairness, fair-limit uniqueness and ranked terminal uniqueness. Every
certified dated trace also admits a zero-error replay with the same
decision word and endpoint. A strict rank bounds the length of every
dated prefix by the initial queue potential. The
reserve and rank include the issued children. The same-cell diamond
still requires exclusivity or margins for the entire competing
footprint. The constants Q, d, B, rail, W and eta are explicit before N.

Two distinct earliest occurrences can be processed in either order
when their phases are fixed and the MARK diamond applies. Causality
keeps the second occurrence eligible in each order. Thus the fixed
calendar itself needs no positive gap between tied pending dates.
The FIFO and fair-limit clauses refer to the underlying MARK
scheduler. A FIFO queue need not select the earliest due date, and an
unbounded stream can prevent an earliest-date scheduler from serving
some pending occurrences.

When the mode is mutable, a reopening and a probe due at the same
date can race. `coincident_reopening_different_memory` proves two
short, zero-error executions with different recovery counts. Choosing
a deterministic priority or separating the admission window from its
mode boundary removes that particular race. `phase_window` checks the
latter against a fixed reopening date. It does not constrain changes
to the reopening date itself under altered routing or timings.

## Native reciprocal instance

`nativeAdmissions` extracts every arrival's native mode from the
actual jump. `admission_cut` identifies that jump in the exact
execution. The admission words before and after birth preserve all
ordered delivery occurrences. On each port the unit raw-window
separation makes lookup by cell, port and date unambiguous.
`recordedMode_recovers_admission` proves that lookup returns the mode
witnessed by the arrival. This is a calendar reconstructed from one
execution. Its stability across perturbed executions is a separate
obligation.

The protected B pair exercises the dated model using the actual READY
and SLOW receipt dates. Its local trace certifies FIRE, then silence
with one recovery dose. The memory theorem gives the same local
terminal counts for all certified dated orders. This slice uses
abstract read margins and uses no routed descendants of its own.
It excludes the intervening activity at A.

The prepared-train induction retains a certificate at each same-cell cut.
It covers the 13 A sources in the learned forward train and the nine B
sources in the learned reverse suffix, including native FIRE dates and
zero gain and recovery doses at each cut.

The complete bridge still needs the remaining per-occurrence dose and guard
certificate tied to the corresponding flow intervals, with the
native FIREs and routed children attached to those same occurrences.
The full admission projection does not supply these branch
certificates, and the local MARK instantiation does not make the
entire reciprocal history a certified guarded run.
