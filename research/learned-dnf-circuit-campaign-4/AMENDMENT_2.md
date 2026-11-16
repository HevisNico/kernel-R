# Campaign 4, amendment 2: the case P4 of the kernel gate, a control P4′, and the target of every case

Pushed alone on `research/learned-dnf-circuit-campaign-4`, after `PREDICTION.md` (commit `1596b36`) and amendment 1
(`AMENDMENT_1.md`, commit `c14124f`), before the cases of the kernel gate are run again and before any prediction
code is committed to this branch. It is the owner's decision. It redefines the case P4 of the gate on "no" cases
(`PREDICTION.md`, The kernel gate), adds a control case P4′, fixes for every case the condition it must fail and
nothing else, states the latency rule of c's pair reads, writes down how P6 is read, and corrects one figure of
amendment 1's account. Nothing else in `PREDICTION.md` or amendment 1 changes.

**No campaign seed (7501 and up) has been simulated, and nothing here depends on campaign-4 data.** The cases are
built from the nominal cell of phase 0 only (`research/learned-dnf-circuit/CALIBRATION.json`, #172, commit
`49684af`). Section 6 says what was seen before this file was written.

## 1. P4, redefined

P4 is built from P0 in two steps:

1. **A measure change**, as for P1 to P3: the guard-on latency of b's pair read at its need is increased by
   **1/10 unit** (the constant of P5, not a data value). The frozen prediction code recomputes everything from it
   (fits, residual bounds, guarded tuple, room, predicted observation).
2. **Then a change of the observation**: the emission of c's test read on ABCD is placed at the midpoint of its two
   arrivals, **1/20 unit after the first**.

| Case | Change | Expected verdict under `beta_0` |
|---|---|---|
| P4, a FIRE before the last arrival | b's guard-on latency of its pair read at its need + 1/10 unit; then the emission of c's test read on ABCD at the midpoint of its two arrivals | no |

## 2. P4′, a control case

| Case | Change | Expected verdict under `beta_0` |
|---|---|---|
| P4′, the latency change alone | step 1 of P4 only | yes |

P4′ shows that P4's "no" comes from the placed emission and not from the latency change: with the latency change
alone, b's emission stays within its deadline and c's emission on ABCD stays after b's arrival.

## 3. The target of every case

Each "no" case must fail **for its target, and only for it**, in both the Python and Lean. The Lean file decides
the three checkers (`checkCascadeValid`, `checkTrainingSeparation`, `checkCascadeCalibrationOneSided`) **separately
on every case**. The Python reports **the complete list of its failing conditions, read by read**, each condition
named with its read (layer, cell, slot, stage, mask) and its kind (guarded margin, residual, decoder, route,
separation, submask comparison). **The Python's list covers every condition of the three Lean checkers, read by
read**, each condition assigned to the checker that holds it, and **its verdict per checker equals Lean's on every
case**; "and no other" in the table below is checked against that list.

| Case | Lean, `beta_0`: false | Lean, `beta_0`: true | The Python's failing conditions under `beta_0`, and no other |
|---|---|---|---|
| P0 | none | all three | none |
| P1 | `checkCascadeValid` | the other two | the room of a's reads (guarded margins), and of b's through the joint fit of layer 1; no timing condition |
| P2 | `checkCascadeValid` | the other two | the room of a's reads (guarded margins), and of b's through the joint fit of layer 1; no timing condition |
| P3 | `checkCascadeCalibrationOneSided` | the other two | c's submask comparison on its test read of both lines |
| P4 | `checkCascadeCalibrationOneSided` | the other two | `v ≤ t` on c's test read on ABCD |
| P4′ | none | all three | none |
| P5 | `checkCascadeCalibrationOneSided` | the other two | the route of line a in test slot AB |
| P6 | `checkTrainingSeparation` | the other two | the separation of the first test slot from the last lesson |

For P4, the Lean file also decides, as propositions on c's test read on ABCD (start `s`, emission `t`):
`∀ j v, arrival j = some v → v ≤ t` is **false**; `s ≤ t ∧ t ≤ s + deadline` is **true**; and every arrival lies in
`[s, s + skew]` is **true**.

Under `beta_3`, on every case (P4 and P4′ included), the Python and Lean must give the same verdict, with no fixed
expected value.

**The rehearsal rule** of `PREDICTION.md` (The gate on "no" cases) becomes: on each of P0 to P6 and P4′, the Python
and Lean give the expected verdict under `beta_0`, each "no" case fails for its target only, in both, as in the table
above, and the Python and Lean give the same verdict under `beta_3`. Otherwise nothing is launched.

## 4. The latency of c's pair reads

This completes `PREDICTION.md` (The kernel gate, emissions), which does not say which latency of c's pair is used.
The predicted emission of c's test read on both lines is its first arrival plus the guard-on latency of c's pair at
stage `min(n_1, n_2)`: **the aligned pair's latency when the two arrivals are at most 3/20 unit apart, and the
0.3-late pair's latency otherwise**. P4′'s expected "yes" depends on this rule: its arrivals are 1/10 unit apart,
so the aligned latency applies.

## 5. How P6 is read

P6 ("the start of one test read moved earlier, so that it begins before the 22 units of the previous slot end") is
built on **the first test slot of the calendar**, whose previous slot is the last lesson of layer 2: the start of a's
`firstTest` read in that slot is moved 1/100 unit earlier. Only that slot can violate the separation: the kernel's
`TrainingSeparation` (`research/learned-coincidence/MonotoneTarget.lean`) requires every test read to start after
every training slot and lesson ends, but does not order the test slots among themselves ("Tests can replay the
completed checkpoint independently"). The 1/100 unit is below the layer-1 skew bound of 1/50, so the arrivals stay
within the skew and only the separation changes.

## 6. What was seen before this file (2026-11-16)

1. The case builder `cases.py` (P0 to P6 as written in `PREDICTION.md`, with the choices the table leaves open
   written in its docstring) and the correction `heldOut := []` of the gate generator (amendment 1, point 6) were
   pushed to the work branch `research/learned-dnf-circuit-campaign-4-wip` at 14:40:27 UTC (commit `3812038`),
   before any verdict was computed.
2. Then the cases were run (Python), and the generated Lean file was compiled at 14:41:17 UTC (Lean 4.35.0). Lean
   and the Python agreed on all 14 decided instances (P0 to P6, `beta_0` and `beta_3`). Under `beta_0`: P0 yes; P1,
   P2, P3, P5, P6 no, as expected; **P4 yes in both**, where `PREDICTION.md` expects no. Under `beta_3`: no on every
   case (no output of P0 has room at K = 3). The results were pushed to the work branch at 14:43:45 UTC (commit
   `574dae3`). The checkers were then decided only together, and the Python's failing conditions were reported only
   per relevant read of the room and as one timing verdict; the per-checker and per-condition targets of section 3
   were not yet computed.
3. **Why P4 was yes.** In P0, a and b are the same nominal cell, with the same latency at the need (0.88 unit), so
   the two arrivals on c for ABCD are on the same date (39719/50), and c's emission is 0.269 unit after them. The
   midpoint of the two arrivals is then the last arrival itself, which the decoder accepts (`v ≤ t`). P4 as written
   could not produce a FIRE before the last arrival on P0's data. The redefinition of section 1 separates the two
   arrivals by a fixed constant of the case table; it depends on no campaign data.
4. **Correction to amendment 1, section 8, item 5.** It gives `epsilon` = 692 for a. The case builder
   `cases.py` (commit `3812038`) and the independent review's own computation both give **691** for a (and for b, as a and b are the
   same nominal table), which matches the stated margin of +4 units on the last silence (692 would give +3). The
   outgoing director's figure is unexplained. Amendment 1 is not changed; this item corrects its account.
5. **The latency rule of section 4** (the independent review's reconstruction from the outgoing director's
   transcript): the rule was already in the first version of `predicted.py`, written at 13:43:14 UTC, before any
   calibration number was looked at.
