# Earliest-date network memory

`dated_network_memory` checks the competing write footprints only for
occurrences eligible at the same cut. Each eligible occurrence has a
minimum due date in the pending queue. In a linear time order, two
eligible occurrences have the same due date. The phase remains fixed
by the occurrence's calendar, so the condition concerns the whole
MARK footprint, including recovery. Wider admissible windows are not
used in this theorem.

For distinct choices, causal routing keeps the other choice eligible
after the first move. The two possible orders join after one residual
move on each side, modulo queue permutation. Identical occurrence
keys give equivalent successors directly. The resulting strong
diamond joins finite dated continuations without a rank. A rank still
bounds processed events and forces drainage for a run reaching the
rank bound. The reserve gives per-coordinate and total write bounds,
strict rail headroom and eventual memory stabilization.
`dated_noisy_safe` proves those bounds for arbitrary read errors.
Certified margins preserve the zero-error decision word and endpoint.

For perpetual traffic, a scheduler that clears every date visible
at a cut eventually matches the writes of any finite dated
continuation. Two such schedules have the same limit memory.
The compared continuations respect due dates, so this statement does
not imply fairness against arbitrary MARK orders. Local finiteness
of service and the prior sublevel budget supply date clearance.

The earlier global theorem is unchanged. `TieAdmissible.of_global`
restricts its admissibility premise to dated choices.
`training_dates_replay` checks the 0, 8, 16, 24 control with decision
word silence, silence, silence, FIRE. `training_rejects_global` shows
that the write at 16 changes the score of the pending occurrence at 24,
so the global diamond fails on the same model. The mutation removes
the last weak write and the assertion that date 24 fires becomes false.
The dated theorem also gives a memory certificate for this training
prefix, compared with the actual native A gain at its first FIRE.

## Reciprocal witness

The physical send gates keep the two active ports on each cell in
disjoint date bands. This proves the tie premise for the reciprocal
seed and every route following the native gate, even for alternative
dated choices. With FIRE clocks within one unit of admission, a
routed probe cannot issue a further routed probe across the two
windows. The resulting constants for this witness are Q = 256,
W = 64 and eta = 1, with rail d times 256 plus one in the normalized
model.

The new native certificates retain the individual A weak inputs at
0, 8 and 16, B weak inputs at 320, 328 and 336, the first weak
receipts in both directions, the protected A write at 32, the three A
forward source FIREs and B's source FIRE at 344. The reverse entry
construction also exposes the three transmitting B sources, their
exact routed receipts, the two A gain writes and the first A reverse
FIRE. Native cuts retain the actual queue and physical coordinates.

The complete guarded replay remains open. The checked local rows
and the prepared blocks still need to be assembled into one
`TransactionReplay` with a single score calendar, actual emitted
children and matching write boundaries at every cut. The conditional
`reciprocal_replay_network` discharges the global tie, reserve and
terminal coordinate comparison once that replay and its counts are
supplied. It does not establish the existence of the full replay.
