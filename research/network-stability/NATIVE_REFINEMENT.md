# Native reciprocal replay and its refinement obligations

The nominal history begins with A's first train, adds B at time 160,
and ends at 459.9. `nominal_full_dated_replay` replays both portions
against the dated queue. It checks each issued contact and each
consumed occurrence in execution order, including multiplicities. The
birth step carries A's existing occurrences into the two-cell queue
and adds B's sources. The two FIRE projections are the original native
words, including real timestamps. The sixteen B sources beginning at
480 stay in the final queue.

`nominal_staged_dose_balance` accounts for all six coordinate totals
against the native flow ledgers across birth. It uses the native
coordinate units of 3/5 for gain and 1/10 for recovery. These are
whole-epoch identities. The protected-receipt certificate also
identifies an individual B response with exactly one recovery dose,
zero gain dose, and no B FIRE.

## The two forward contacts on B

`nominal_protected_receipt` retains actual cuts of a complete
milestone-3 construction. B's second forward reception starts in
READY, fires, and enters FAST. B remains outside READY from that
FIRE through its third reception. Its input gap is at least 7.9,
and it is already in SLOW when the third contact lands. The third
contact supplies a full MARK dose and B is READY with cleared raw
inputs at the time-184 cut.

The cell-level test in `AllowsSettledTransactions` requires every
new arrival to follow the preceding FIRE's return to READY.
`nominal_settled_exclusivity_fails` gives a counterexample on the
actual witness. Unit raw-window separation still holds because raw
expiry and main recovery are different physical events.

The two B reads use the same physical port with equal gain and
recovery at the two admission cuts. With a fixed bias and fixed
recovery coefficient for that port, a MARK model scores the two cuts
identically. `ProtectedReceipt.no_fixed_input_replay` proves that this
read law cannot realize both nominal decisions. A larger error margin
around that same score cannot certify both outcomes. The native
decision also depends on the main mode.

`ProtectedReceipt.certified_pair` uses the actual READY and SLOW
admissions to certify the two B decisions and their dose in a local
MARK run. It compares B's single FIRE at the actual date, and the
unchanged gain and one recovery dose at completion. Its integer error
interval is a certificate for the abstract run.

## Scope of the bridge

The dated queue replay, dose accounting and overlap result are checked
on native execution evidence. A complete guarded refinement still
requires an admission rule for phase-specific probe types and a
per-transaction certificate for the remaining dose and guard cuts.
A timed admission rule must also distinguish future source tokens
from enabled probes. Loading all same-cell sources into the MARK
initial queue violates its cell exclusivity immediately. Alternatively,
a phase-aware read law would need sufficient interleaving margins
on every reachable abstract configuration. This draft does not
instantiate `MarkFeedback.network_memory` for the native history.
