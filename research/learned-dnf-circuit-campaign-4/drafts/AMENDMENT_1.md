# Campaign 4, amendment 1: what the kernel gate needs that PREDICTION.md does not fix

Pushed alone on `research/learned-dnf-circuit-campaign-4`, after `PREDICTION.md` (commit `1596b36`), before the
prediction code is committed and before the Lean gate is run on any calibration numbers. It corrects or completes rules of `PREDICTION.md` that the Lean premise
(`TwoLayerMonotoneRecognitionOneSided`, research/learned-coincidence, `MonotoneTarget.lean`, `TwoLayerTarget.lean`,
`MonotoneOneSidedTarget.lean`) and its checkers (`MonotonePremiseTargets.lean`, proved at `2e586aa`) need, so that the
kernel and the Python can agree. Nothing else in `PREDICTION.md` changes. The seven points are given in the order they were set; section 8 says how.

**No campaign seed (7501 and up) has been simulated, and none of the seven points depends on campaign-4 data.**
How each point was set, and which numbers were looked at, is told in section 8.

## 1. The duration of c's read

`secondTiming` (the kernel's `right`) is `⟨11/10, 11/5, 19⟩`, in place of the duration 22 of `PREDICTION.md`,
The Kernel gate. c's read starts at its first arrival, at least 1.5 units into the slot and at most about 2.6 units
(1.5 plus a layer-1 latency of at most 1.06 and two snaps of 0.02); `TrainingSeparation` requires each read's start
plus its duration to be at most the next slot's start, 22 units after the slot: 22 − 2.6 ≈ 19.4, so 19, and
11/5 < 19 as `SlotTiming.Valid` requires. The Python's own separation check uses 19 as well.

The shorter declared window cannot hide a late FIRE: the Python records every emission of c over the whole physical
slot (22 units), and the gate fails if any of them lies outside [start, start + deadline].

## 2. The rail

`rail` = **1 000 000** (10 × theta) in both layers. It is a non-physical bound: the headroom of the memory is
covered by calibrating every reachable stage (Q ≤ 7), not by the rail. The Python adds the same strict
`gain < rail` check to eligibility and reports the largest gain / rail ratio, so that the two sides cannot part.

## 3. Budgets per cell, grouped by the Lean field

The kernel holds one `trainingError` and one `testingError` per cell. The budgets of `PREDICTION.md` (Needs, the
gain path and the budgets) are per read; each cell's budget is **the largest per-read budget over the reads that the
kernel checks with that field**, for `beta_0` and for `beta_3` alike, with `n` (the writes of each port) per read
inside the maximum:

| Cell | `trainingError`: the largest over | `testingError`: the largest over |
|---|---|---|
| a, b | its `firstTrain` reads | its `teach` reads and its `firstTest` reads |
| c | its lesson reads (`secondTrain`), both lines | its `secondTest` reads |

These per-cell numbers replace the per-read ones **everywhere the Python uses a budget**: eligibility, room at
K = 3 per output, own room and room up to a learning port. Otherwise the equivalence of the gate under `beta_3`
("all three outputs have room") could break.

## 4. The residual bound and the observation it covers

The residual bound `epsilon` of a cell includes **the empty read of each cell, stages 0 to Q**, besides the singles
and aligned pairs (layer 1) or single lines (layer 2).

The predicted observation, as the kernel reads it: **a layer-1 read's input is every active external input of its
slot**, with a guarded gain of 0 on the inputs the cell has no port for. So b's `teach` reads during line a's lessons
(inputs A, B) and a's `firstTest` reads on C and D are physically b's or a's empty reads, and a's `firstTest` read
on, say, A, C, D is physically its single read of port 1; their scores are those of the calibration's empty or
single reads at the cell's trained stage. In `firstTrain`, a cell's input is its target (A, B for a; C, D for b),
as `CascadeCalibrationOneSided` checks it.

## 5. An instance without a need

A measured instance with a cell or line that does not fire up to stage 7 runs **the need-7 calendar of that layer**
(a missing need counts as 7 in `dnf.calendar`), the only calendar whose memory and time limits are rehearsed. Such
an instance is **not eligible**, has **no predicted words**, gets no guarded tuple and no Lean check, and enters
**M2 only**.

## 6. Every field of the kernel's objects, with its source

`heldOut` = **the empty list** (`[]`): `Cascade.check` passes with it in the monotone version, and the recognition
theorem does not use it. `first.tests` = `[]` as well: `Cascade.check` uses `checkConjunctions`, which does not read
it.

| Lean field | Value | Source |
|---|---|---|
| `first.target` | a: {A, B}; b: {C, D} | PREDICTION.md, Ports and lines |
| `first.tests` | `[]` | this amendment, 6 |
| `first.initialGain` | the guarded initial gain of each port; 0 on inputs the cell has no port for | Guarded tuple; this amendment, 4 and 7 |
| `first.help` | the guarded help of each cell | Guarded tuple; this amendment, 7 |
| `first.threshold` | 100 000 | Score |
| `first.trainingError`, `first.testingError` | per cell | this amendment, 3 |
| `first.dose` | the guarded common dose of layer 1 | Guarded tuple; this amendment, 7 |
| `first.maxWrites` | `Q1` | Write budget |
| `first.rail` | 1 000 000 | this amendment, 2 |
| `second.lines` | c: both lines | PREDICTION.md, What is tested (the OR) |
| `second.alwaysFire` | false | idem |
| `second.initialGain`, `second.help`, `second.dose` | the guarded tuple of c | Guarded tuple; this amendment, 7 |
| `second.threshold` | 100 000 | Score |
| `second.trainingError`, `second.testingError` | per cell | this amendment, 3 |
| `second.maxWrites` | `Q2` | Write budget |
| `second.rail` | 1 000 000 | this amendment, 2 |
| `delay` | 3/2 | Routing |
| `heldOut` | `[]` | this amendment, 6 |
| `left` (`firstTiming`) | `⟨1/50, 11/10, 22⟩` | The kernel gate |
| `right` (`secondTiming`) | `⟨11/10, 11/5, 19⟩` | this amendment, 1 |
| `firstTrain r a` | slot `r` of layer 1; input the target of a; its pair score at stage `min(r, need)`; an emission at start + latency if `r ≥ need` | The kernel gate; this amendment, 4 |
| `teach n a` | lesson `n` (line a, then line b, each round); input the target of the lesson's line; the cell's pair or empty read at its trained stage | idem |
| `secondTrain n` | c's read of lesson `n`: the arrival of the line at its upstream emission + 3/2; its single read at the line's writes so far | idem |
| `firstTest x a` | test pattern `x`; input `x`; the cell's empty, single or pair read at its trained stage | idem |
| `secondTest x c` | arrivals from `firstTest` + 3/2; start at the first arrival (or slot + 3/2 if none) | idem |
| `scores x c` | empty mask: c's empty read at `max(n1, n2)`; one line: that line's single read at its writes; both: the lower of the aligned and 0.3-late pair at `min(n1, n2)` | The kernel gate |

## 7. The guarded fit uses exactly the reads its residual bound covers

One rule for the three cells: the guarded tuple (`PREDICTION.md`, Guarded tuple) is fitted, by least squares on
stages 0 to Q, on **exactly the reads that its residual bound `epsilon` covers** (with point 4): for a and b, the
empty read, the singles and the aligned pairs; for c, the empty read and the single lines.

For c this is forced: the written rule fits c on its single lines only, which give the help plus each line's gain and
the dose but never the help apart from the gains, so the rule defines no value (the minimum-norm solution puts the
help at about 57 900 units against an empty read of 10 000). For a and b it is the same rule, for coherence.

It was found from the nominal numbers (section 8). Compared with point 4 alone, it favours a and b: on the
calibration of phase 0 (`CALIBRATION.json`, #172, commit `49684af`) the room of the pair's last silence (stage 3)
under `beta_0` is −406 units with point 4 alone and +4.6 with points 4 and 7 (the owner's computation); the rule as
first written, without points 4 and 7, left them more, +574 units. It is the only version consistent with the
preregistered "yes" of P0.

**The fit range is unchanged**: stages 0 to Q, as written (the owner's decision 3). The alternative of stages 0 to
the need was computed on the nominal numbers (section 8), and it is rejected for that reason.

## 8. How these points were set, and which numbers were looked at (2026-11-16)

1. **Points 1 to 6** were set before any of their numbers were looked at: points 1 to 5 from the Lean definitions
   and the calendar while the prediction code was written, point 6 by the owner's review of points 1 to 5, with the
   owner's precisions on each.
2. Then the two calibration decks of the **nominal cell** (section `tt`, no mismatch seed) were run with the
   implementation in progress, guard on (607 s) and guard off (464 s), and the Python prediction was run on them
   and looked at by the executor. It showed: needs 4 for a, b and both lines of c; Q1 = Q2 = 6; every FIRE bit of
   the guard-on deck equal to the threshold comparison of the guard-off score; `epsilon` of c at about 47 900 units
   under the written rule (the help undefined, point 7); with the empty read in the fit, a's and b's pair at its last
   silence 4 units short of room under `beta_0`; no output with room at K = 3. **The Lean gate was not run.**
3. **Point 7** was found from these numbers. The alternative fit range, stages 0 to the need, was computed on them
   too, and is rejected for that reason (section 7).
4. **The owner's own computation** on `CALIBRATION.json` of #172 (commit `49684af`), the frozen input of P0, with
   the owner's script and not the frozen code: c's guarded tuple undefined by the written rule (minimum-norm help
   57 935 against an empty read of 10 000, `epsilon` about 47 935; with the empty read in the fit, help 10 000 and
   `epsilon` 382); the room of a's and b's last silence under `beta_0`: +574 units under the rule as first written,
   −406 with point 4 alone, +4.6 with points 4 and 7. The −4 units on the nominal decks of item 2 has no
   procedural role: P0 is built from `CALIBRATION.json`, and nothing requires those decks to be eligible.
5. **P0 under the amended rules**, with the executor's code (`predicted.py` and `gate4.py` as they stand when this
   file is pushed; Python only, no Lean): **verdict yes** under `beta_0` (the scores' room and the timing of the
   predicted observation), no under `beta_3`. The room of the pair's last silence under `beta_0` is **+4 units** for
   a and **+4 units** for b (the integer budgets are rounded up; the owner's +4.6 is the same margin without that
   rounding); `epsilon` 692 (a), 691 (b), 382 (c); the largest guarded gain at the need is 0.092 of the rail. P0's
   table from `CALIBRATION.json`: Z rounded to the file's four decimals, in integer units; c's 0.3-late pair, which
   phase 0 did not measure, taken equal to its aligned pair; the dose of a port at stage k the difference of the
   stored voltages of stages k and k + 1 (stage 7: that of stage 6), as the file gives them for port 1.
