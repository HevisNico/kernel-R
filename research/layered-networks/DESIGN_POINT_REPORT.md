# The family design point in the layered deck: fixes (1)–(3) and the 9801/9802 reruns

**Development only, nothing preregistered.** One mismatch draw per instance (the same seeds as M4), no noise.
Records in `dev/cal5_not1` and `dev/cal5_andor3`; run with `lcal.py run SPEC OUT SEED solo=1`.

## Fix (1): the design point, as config

- `calibration.json` `design_point`: `vhi = 0.7` (2.71 mV per write against 1.35) and `reltol = 1e-5`.
- Sources: `research/learned-dnf-circuit-campaign-7-prep` (b956efe4), `dev/batch2x.py` `PARAMS`, and
  `CAMPAIGN7_PROTOCOL_DRAFT.md` lines 40–42.
- `instrument.deck_text` applies them by the rule of `dosedev.rewrite` / `dosedev_tol.rewrite`: exactly one definition
  each, on its `.param` / `.option` line. No stacked patch; no pushed file changed.
- The 1x deck stays available as `deck_text_1x`.

## Fix (2): junction areas, and the deck-identity test

- Areas are applied as campaign 5's `net.deck(junction="areas")` does: `sky130-supervisor-closure/junction/netlist.py`
  `build` with `areas.csv`. That gives 232 devices per R cell; the flattened deck is checked for exactly 232 × cells.
- Inverter devices get zero areas: no inverter layout exists, and its characterisation had none.
- **`tests/test_deck_identity.py` passes on NOT1, ANDOR3 and XOR3.** For every R cell, it compares the layered deck with
  `network-circuit/net.py` `deck(cells, section="tt_mm", leak_per_port=True)`, given the same two-line rewrite. It
  imports `net` for the comparison only. Result:
  - all 334 element lines of the cell are identical;
  - the cell's stimulus sources (`vinit`, `vks`, `vkr`, `vkp`, `vts`, `vamp`) are identical;
  - the `.lib`, `.param` and `.option` lines are identical.
- **One stated difference.** The per-port leak source `vgl<cell><port>` is a 0 V pulse here (a scan sets its window),
  and `dc 0` in the family deck. Both are 0 V outside a scan. It is a stimulus line, not a cell line, and the test
  asserts exactly this form on both sides.
- Inverter lines are counted only (60 per inverter): `net.py` has no inverter.

## Fix (3): D4 and the both-direction repeats

- `calibration.json` `scan.repeats = true`. Once a group's bracket closes, each end is read once more, approached
  from the other side: L after a FIRE, U after a silence. The bracket is then L = the largest silence and U = the
  smallest FIRE over all reads. A disagreement widens it to the envelope and is recorded (`repeats_agree`).
- Two new tests (`tests/test_cal.py`): the repeats read both ends from both sides; a history shift is caught and widens
  the bracket.
- **The scan cap was raised from 40 to 64 slots** (config). At 2x, the second repeat needs a whole-stage dose and about
  three leak slots back. The first NOT1 attempt closed its bracket and agreed on its first repeat, then ran out at 40.
  That attempt is discarded; it is not in `dev/`.

### Solo against parallel, at 2x (stages of the cell's own 2.71 mV step)

| Cell | Gate | s* parallel | s* solo | \|Δ\| | half brackets (par + solo) | repeats (par / solo) |
|---|---|---|---|---|---|---|
| NOT1 c1_0 | copy | 1.80248 | 1.80242 | 0.00006 | 0.0038 | agree / agree |
| ANDOR3 c1_0 | both | 2.00137 | 1.99930 | 0.00207 | 0.0041 | agree / agree |
| c1_1 | copy | 1.48470 | 1.48469 | 0.00002 | 0.0039 | agree / agree |
| c2_0 line 1 | either | 1.97012 | 1.97066 | 0.00054 | 0.0041 | agree / agree |
| c2_0 line 2 | either | 1.36353 | 1.36116 | 0.00237 | 0.0038 | agree / agree |
| c3_0 | copy | 1.94318 | 1.94723 | **0.00405** | 0.0041 | **U disputed** / agree |

- **Every |Δ| is within the sum of the two half brackets** (at 1x, two were not).
- The largest is 0.00405 stage, about 11 µV. At 1x it was 0.0138 1x stage, which is 0.0069 in 2x stages and 19 µV.
- **9 of 10 repeats agree.** The tenth is c3_0's parallel scan: its U state, 1.94513, fired once and was silent on the
  repeat after a silence. The solo scan puts the crossing at 1.94509–1.94936, so c3_0's crossing sits at about 1.9451,
  and reads there are undecided at the read-to-read level.
- So D4 is the bracket resolution plus a read-to-read spread of a few µV. Nothing larger shows at 1e-5.
- **`d4_stage` fixed at 0.005** (in 2x stages) for runs without their own solo scans: the largest |Δ|, rounded up to the
  next 0.001.

### The crossings are physical: the same in mV at both design points

| | NOT1 | c1_0 | c1_1 | c2_0 l1 | c2_0 l2 | c3_0 |
|---|---|---|---|---|---|---|
| crossing at 1x (M4), mV | 4.856 | 5.360 | 3.973 | 5.300 | 3.638 | 5.261 |
| crossing at 2x, mV | 4.879 | 5.409 | 4.011 | 5.314 | 3.705 | 5.280 |

- The crossings agree within 14–67 µV (0.3–1.8 %), with the 2x deck slightly higher; that is the junction areas and
  the tolerance [I].
- **So the small ANDOR3 margins of DIAGNOSIS.md cause 3 belong to this mismatch draw, not to the dose.**
  - The margins in stages move only by where the integer stages fall.
  - c1_1 gained: 0.039 → 0.515 stage. c3_0 is unchanged: 0.060 → 0.057 in 2x stages. c2_0 line 1 went from 0.020 to
    0.030.
  - **c1_0's crossing is at its stop at both points**: 1.9955 and 2.0014 in 2x stages.

## Verdicts (θ = 100 000), kernel against mirror

| Instance | Cell | Gate | need | ε | H, H_drift, H_D4 | errors K0 (train/test) | K0 | errors K3 | K3 |
|---|---|---|---|---|---|---|---|---|---|
| NOT1 | c1_0 | copy | 2 | 0 | 16, 1, 1 | 108 / 108 | **eligible**, stop margin +1487 | 1324 / 1324 | **room**, +271 |
| ANDOR3 | c1_0 | both | 2 | — | — | — | **not measured** | — | — |
| | c1_1 | copy | 2 | 0 | 16, 1, 1 | 104 / 104 | **eligible**, +3851 | 1263 / 1263 | **room**, +2692 |
| | c2_0 | either | 2, 2 | 3 | 58, 4, 72 | 471 / 802 | **eligible**, anchor (1,) +92 | 5008 / 9844 | no room: stop margin −4114, anchor (1,) −8950 |
| | c3_0 | copy | 2 | 0 | 17, 1, 34 | 144 / 144 | **eligible**, +325 | 1383 / 1383 | no room: stop margin −914 |

- **The budgets in stages are the family's.** NOT1's K0 error is 108/8068 = 0.0134 stage (family median 0.0133). Its
  K3 error is 0.164 stage (family 0.164). At 1x they were 0.027 and 0.33.
- **c1_0 is not measured.**
  - The rule (question 1) wants ⌈s*⌉ equal to the training's first FIRE round. s* = 2.00137 gives 3; the training fired
    at s = 2.00000.
  - Both scans' brackets contain 2.0000: parallel 1.9992–2.0035, solo 1.9973–2.0013. The crossing is at the stop to
    within the bracket resolution.
  - Its stop margin is therefore about 0 ± 0.002 stage, against a both-cell K0 error of about 0.027 stage. It could not
    be eligible under any outcome of the rule.
- **c2_0 at K0 is eligible under the max rule**, by 92. It was −302 at 1x. Under the one-port rule its anchor slack
  would be +423.
  - At K3 the either cell fails on its training budget too: stop margin −4114. So the max rule is not the only binding
    clause there.
- **c3_0 at K3**: margin 0.057 stage, against a K3 error of 0.168 stage.
- Every lesson, replay and test read is within its error. The decoder is exact. Every failure is a room clause of
  `Cell.Valid`.

| Instance | K | checkLayeredValid | training | reads | recognition theorem | kernel |
|---|---|---|---|---|---|---|
| NOT1 (9801) | K0 | true | true | true | **proved** | accepted (8.5 s), agrees |
| | K3 | true | true | true | **proved** | accepted (1.3 s), agrees |
| ANDOR3 (9802) | K0, K3 | — | — | — | not emitted: c1_0 not measured | — |

- `tests/check_leancal.py` holds on both NOT1 files:
  - `computes` uses only propext, Classical.choice and Quot.sound;
  - a lesson score raised by 10 000 is rejected;
  - testError 99999 is rejected.
- The per-cell files (`FitNOT1.lean`, `FitANDOR3.lean`: `Checker.cellValid` and `Cell.stop` of every measured cell at
  K0 and K3) are accepted and agree with the mirror.

**Per instance.**
- NOT1 is eligible at K0 and has room at K3, with the recognition theorem proved at both.
- ANDOR3 is not measured (c1_0). Its three measured cells are eligible at K0, and two of them have no room at K3.

## Cost at the design point (CPU minutes, one core; CPU equals wall here)

| Instance | Setup | Training | Tests | Parallel scans | Solo scans | **Total** | **Without solo** | at 1x (M4): total / without |
|---|---|---|---|---|---|---|---|---|
| NOT1 | 0.27 | 0.95 (4 slots) | 0.43 | 2.71 (37 slots) | 0.68 (8 slots) | **5.0** | **4.4** | 3.0 / 2.3 |
| ANDOR3 | 0.32 | 18.2 (16 slots) | 7.3 | 33.8 (79 slots) | 45.3 (146 slots) | **104.9** | **59.6** | 43.8 / 31.2 |

- **A slot costs about 2.1–2.6× more at 1e-5 with areas**: about 69 s per ANDOR3 lesson slot, against 33 s at 1x.
  - Training needs fewer rounds (16 lesson slots against 23), but not enough to make up for it.
  - The repeats add about 10–15 slots per group.
- **Net ×1.9 without solo, against DIAGNOSIS.md's guess of ×1.0–1.5 [G]. That guess was low.**

## The inverter instances' options

- `research/inverter-instances`, tip 280c6f6. `d25ee8e` is not an object in the history fetched; if it is on another
  branch it was not checked.
- `invinst/cell.py` has:
  - `.option reltol=1e-4 abstol=1e-13 vntol=1e-7 chgtol=1e-17`, `.option gmin=1e-16`, `.option scale=1e-6`, temp 27;
  - **no junction areas**;
  - max steps 5 ns (slot runs) and 20 ns (leak runs);
  - gate windows: timing window 1/4, emitEarly 2/5, emitLate 13/20.
- **The inverter was characterised at 1e-4 without areas. An inverter-fed deck at the new point (XOR3) runs at 1e-5**
  with the network's max step.
- So these must be re-measured at the network's options before XOR3 is calibrated:
  - the emission range (emitEarly and emitLate);
  - the silence margins at K0 and K3;
  - the leak on both sides;
  - the help window;
  - the wrong-sign charge.

  If the inverter is to get areas, they need a layout; none exists.
- **XOR3 has not been run.**

## Open

- XOR3: needs the inverter re-measured first (above).
- The question-1 rule makes a cell whose crossing is at its stop "not measured", not "not eligible". c1_0 is such a
  case. The rule is kept as it is; whether such a cell should count as measured-and-not-eligible is the owner's choice.
- The one-sided set and the both-lines check are not implemented.
