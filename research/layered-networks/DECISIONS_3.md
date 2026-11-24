# Owner decisions on the layered calibration, continued (relayed by the coordinator)

DECISIONS.md and DECISIONS_2.md are pushed and are not modified (owner rule); later decisions are recorded here.

| Date (UTC) | Decision |
|---|---|
| 2026-11-24 08:19 | **The either cell's testError follows the one-port rule**: the larger of its two lines' one-port read budgets, at [n_p], + H + H_drift + H_D4. This is campaign (a)'s family rule for c. |

**This supersedes** the decision of 2026-11-23 11:12 in DECISIONS.md: "the max rule … No rule change after a failure is
seen". The max rule is no longer the rule for the claims. It is kept as a declared comparison that counts for nothing
(below).

**Reason.**
- The Lean premises need only the one-port budget. In `LayeredMonotoneTarget.lean`, testError enters only four
  places:
  - `Cell.Valid`'s silent masks: for an either gate, only (), whose score is 0;
  - its single-port anchors;
  - `AdditiveSlot` on non-firing reads: only ();
  - `FiringSlot`'s single-port anchor lower bounds.
- Nothing bounds the two-port score (K3_EITHER_ANALYSIS.md §2).
- The rule is campaign (a)'s: the max rule was a departure from it.

**Stated plainly.**
- This was noticed **after the development failures were seen**: XOR3 9803 c2_0, anchor (2,) at K3, −364; ANDOR3 9802
  c2_0. It is a rule change after a failure, which the superseded decision had excluded.
- It is made before the freeze and before any campaign seed is drawn.
- **It makes the test riskier.** More instances get a noisy prediction (room at K3), and each of them has a thinner
  margin: the both-lines term no longer stands between the two-port read and the threshold.

**Conditions (owner).**
1. Implemented as a new, versioned rule, selected by config or flag, with no pushed file modified.
2. 9801, 9802 and 9803 re-gated through the real Lean gate (kernel and mirror). At K3, the report shows where room is
   now claimed, that the recognition theorem's premises close (`layered_inverters_chained` for XOR3), and that the
   kernel agrees with the mirror.
3. For PREDICTION.md:
   - a declared comparison that counts for nothing: room under the old max rule, reported beside the claim counts;
   - an expectation stated in advance: if a K3 run refutes, the either cell's two-port read is the first suspect.
