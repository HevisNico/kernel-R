# M2: the calibration instrument, validated on NOT1 (9801) and ANDOR3 (9802)

**Development only, nothing preregistered.** One mismatch draw each (`tt_mm`), no noise, 27 °C.

## What is instrumented (new files only; no pushed file changed)

| File | Content |
|---|---|
| `instrument.py` | the deck with one imposed-leak node per port; u_p = mean(vmem) − mean(sum) of every port over the 35 µs before each slot's gate setting, recorded in every slot (`u`) and after the last test (`u_end`); the training path (u(0), D_p from the silent lessons, the measured s of every lesson read); the parallel scans |
| `scores.py` | the score readout of every lesson, replay and test read: the anchors per gate (CALIBRATION_PROPOSAL.md (a)), Z, the decoder check (\|Z − θ\| > H with a disagreeing FIRE bit), question 1 |
| `calibration.json` | the instrument's constants (config.json is unchanged) |
| `lcal.py` | driver: `run SPEC OUT SEED`, `scores SPEC OUT`, `test` |
| `tests/test_cal.py` | 6 tests without a simulator: the deck's leak nodes; the scan state machine against a fake cell (20 draws), with groups in order and a missing bracket; the anchors put θ at s*; the decoder rule; the training path and bracket |

### The scans

- **When.** After the tests, in the same session.
- **Grouping.** One scan per (cell, group). Different cells are scanned in the same slots; an either cell's two lines
  are scanned one after the other.
- **What is kept from campaign 6** (`scan6`): the bisection on the training path, the dose and leak moves, the leak
  gain refined on the run, and the end criterion (hi − lo) · max D ≤ 20 µV.
- **What changed from campaign 6**, each to save slots:
  1. it starts from the training bracket (last silent read, first firing read), with no ascent from s = 0;
  2. the bracket is kept at the **measured** state of each read, not at its target, so the target tolerance is
     10 µV (scan6: 2 µV);
  3. the leak undershoots by 4 % (scan6: 30 µV), with a step of at most 1.5 mV (scan6: 1.2);
  4. a read slot carries the next leak in its tail. The read is gated read-only and the leak source is separate.

  Changes 2 and 3 cut NOT1's scan from 26 slots to 18.
- **Not done in M2:** repeats of disputed states, the one-sided set, and the both-lines check.

## Measured cost (machine-minutes, one core; CPU = wall within 1 %)

| Instance | Setup | Training | Tests | Scans | Total | Scan slots | Before M2 |
|---|---|---|---|---|---|---|---|
| NOT1 | 0.25 | 0.66 | 0.22 | 0.93 | 2.06 | 18 (1 scan) | 1.2 |
| ANDOR3 | 0.27 | 13.4 | 3.8 | 11.7 | 29.4 | 41 (5 scans, parallel) | 16.8 |

The extra cost is 0.9 min for NOT1 and 12.6 min for ANDOR3. Almost all of it is the scans; the per-port u
readout costs a few seconds. The proposal had estimated about 30 and 70 extra slots.

## Scans and scores

| Instance | Cell | Gate | s* (stages) | half bracket | d | H | question 1 |
|---|---|---|---|---|---|---|---|
| NOT1 | c1_0 | copy | 3.5950 | 0.0060 | 11351 | 69 | agrees (4) |
| ANDOR3 | c1_0 | both | 3.9956 | 0.0044 | 12486 | 111 | agrees (4) |
| | c1_1 | copy | 2.9730 | 0.0022 | 9946 | 22 | agrees (3) |
| | c2_0 | either | 3.9544 / 2.7161 | 0.0040 / 0.0057 | 14991 | 86 | agrees (4, 3) |
| | c3_0 | copy | 3.8893 | 0.0041 | 12164 | 50 | agrees (4) |

- **Decoder failures: none.** No read on either instance has its FIRE bit disagreeing with Z ≥ θ outside the band
  ±H: 8 of 8 reads on NOT1, 100 of 100 on ANDOR3.
- **Undecided reads: 16 on ANDOR3** (|Z − θ| ≤ H), all of the both cell c1_0 at its trained state: 14 replays in
  later lessons and 2 tests.
  - Its crossing s* = 3.9956 lies 0.004 stage below its stop stage, 4, so its firing reads score θ + 0 to θ + 111.
  - This is a thin margin, not a disagreement. That cell will have no room at K3 (it needs about 0.16 stage).
  - The other cells' firing reads are 4594 or more above θ, and every silent read at least 6754 below.
- **Training words and outputs** are as in the earlier development runs (same seeds). All 8 ANDOR3 patterns and both
  NOT1 patterns are correct.

## Not done (later milestones)

- The guarded fit, ε, sensitivities and budgets (M3).
- The Lean emission of the calibration checkers (M4).
- XOR3 (9803): not run, as asked.
- The one-sided set and the both-lines check.

The s* values are exact rationals of the measured float voltages; they are long fractions.
