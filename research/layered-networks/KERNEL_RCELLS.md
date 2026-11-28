# The kernel on the R cells (item K, 2026-11-26). Development only; no simulation, nothing pushed

## (a) The stage-D gate of the R cells is the Python mirror; no Lean kernel checks them in the chain

- **The path.** The stage-D step runs stage_d5.py → stage_d3.py (inside fit3.rule(rule)) → stage_d.predict. That
  calls `fitmod.cell_fit(s, view, ro, c, k, i)` per cell (stage_d.py:332). The instance is eligible and has room
  iff every cell's `verdicts[K]["ok"]` holds and the inverter gate holds (stage_d.py:336–338).
- **What `ok` is** (fit.py:293–345): `valid ∧ trained_word_matches_model ∧ training_calibration ∧ read_calibration`.
  - `valid` is fit.cell_valid (fit.py:133–155), the clause-by-clause exact-integer mirror of Cell.Valid
    (LayeredMonotoneTarget.lean:84–92).
  - The two calibrations are Python mirrors of the AdditiveSlot / FiringSlot residuals and decoder checks of
    TrainingCalibration / ReadCalibration (LayeredMonotoneTarget.lean:186–211).
  - `lean_cell` is written as data (fit.py:347) and is never compiled at stage D.
- **Where Lean does run in the campaign_run12/13 chain: only the "inverters" step**, for the inverters, not the R cells.
  - campaign_run7.py:82–90 → indeck_noise4.py → the kit's invinst/indeck.py:220 and :266.
  - There, gate.py:201 runs lean/check.sh on Inverter_<seed>.lean against CircuitInverterGate, and driver.py builds its
    library into inv/lean_build/.
  - No other step compiles Lean: deck, D, seal, sealpush, N<n>/C<n>, U and the duplicates. Lean appears elsewhere only
    as envcheck's version/binary pin.

## (c) Run now: every sealed lean_cell through the kernel, clause by clause

- **The tool.** leancell.py, a new file. It is leanfit.py, the development tool used on 9801–9803 (dev/cal*/leanfit.json:
  `Checker.cellValid` and `Cell.stop` stated at the mirror's values, `decide +kernel`), made clause by clause.
  - Per cell and level, one theorem per fit.cell_valid clause states the mirror's truth value of that clause:
    dose; per group 0 < stop ≤ maxWrites, the early silences k < stop, the stop margin; the rails; the silent masks;
    the anchors.
  - Also stated: `Cell.stop g` = the mirror's stop, and `Checker.cellValid` = the mirror's valid. The latter is sound
    and complete for Cell.Valid (LayeredMonotoneCheckerProofs), so it also catches a clause the mirror could lack.
  - A clause that the kernel and the mirror disagree on fails its theorem, and Lean's error line gives the clause.
  - Beside it, the sealed `failing` list must equal the mirror's failing list recomputed from the sealed lean_cell.
- **The library.** Built fresh from the pinned integration tree (a2ea377f): 42 s for all modules, 28 s up to
  LayeredMonotoneCheckerProofs, 17 MB.
- **The data:** 95 sealed predictions (93 distinct files).

  | source | predictions |
  |---|---|
  | the yield lot | 56 |
  | dev/ dry runs and validations (XOR3 9803 and NOT1 9801/9804 dry and pipeline runs, 9805/9806, regate3, stage_d_*) | 25 |
  | the prefreeze dry runs (XOR3 9803, NOT1 9804 ×3) | 4 |
  | the G2 ANDOR3 6104 run (evidence/prefreeze-g2) | 1 |
  | the D4 check's 6 NOT1 | 6 |
  | the campaign_run13 rehearsal (6220, 6212) | 2 |
  | **one forced regate:** ANDOR3 9805 with d4_stage 0.0138 (d4_regate's path) | 1 |

  The forced regate turns K0 from eligible to not eligible: c2_0's g0 early silence k=2, slack −53. So the D4 rule's
  mirror is covered on a false clause as well.
- **Result.**
  - **The kernel agrees with the mirror on every theorem:** 7,826 theorems (3,913 at K0 and 3,913 at K3, over 568 cell
    levels). 263 of them state a clause as false (35 at K0, 228 at K3), and the kernel agrees there too.
  - The sealed failing lists equal the recomputed mirror's in all 95.
  - **No disagreement** by cell, clause or level.
  - Lean time: 99.8 s in total (0.78–1.52 s per prediction); 101 s wall.
- **Negative control.** The statement of one true clause and one false clause was flipped in the regate's file. The
  kernel then rejected exactly those two lines (22 and 66).
- **Data.** dev/kernel_rcells/LEANCELL.json (per prediction: theorems, seconds, disagreements, mirror failing lists)
  and dev/kernel_rcells/MANIFEST.json. The paths in them are the scratch paths of this machine.

## (b) Putting the kernel back into stage D: the cost (a proposal, not built)

- **Two levels, as in campaign 6 / campaign (a):**
  - **(i) Cell.Valid per cell and level.** leancell.py, or leanfit.py with the per-clause statements. It runs on
    D/prediction.json right after stage_d.predict:
    - the kernel's verdict is the last word: the instance is eligible / has room only if the kernel accepts every cell
      at that level;
    - the mirror stays beside it, and any disagreement is reported as a run failure under its clause.
  - **(ii) The calibration clauses (TrainingCalibration / ReadCalibration), optional.** The checkers
    checkLayeredTrainingCalibration / checkLayeredReadCalibration on the stage-D record's reads and scores, with
    leancal.py's emitter (leancal2 with a front end).
    - Measured on development records: 3–5 s per file, 2 files per instance (K0, K3).
    - Not yet tried on a sealed stage-D record. A dry run must show that the stage-D record has what leancal needs.
- **Per instance, (i) alone:** about 1 s of Lean (0.8–1.5 s measured, at most 118 theorems per instance), well under 1%
  of stage D's minutes. The disk is the .lean file and its log (a few kB), plus LEANCELL-like JSON in D/.
  - **Per machine, once:** the library build, 42 s and 17 MB. It is separate from the kit's inv/lean_build.
  - **(ii)** would add about 8 s per instance.
- **What must be pinned (new to FREEZE_PINS_2):**
  - the emitter: leancell.py, or leanfit.py plus lean.py's check (none of these is pinned yet);
  - for (ii): leancal.py / leancal2.py / measure.py (not pinned yet);
  - the 7 Lean sources of the import closure of LayeredMonotoneCheckerProofs that are not pinned yet:
    LayeredMonotoneTarget (521fdfee…), LayeredMonotoneCheckerTargets (81c29cdf…), LayeredMonotoneCheckerProofs
    (4dedf666…), MonotonePremiseTargets, MonotonePremiseSoundness, MonotonePremiseCompletenessTargets and
    MonotonePremiseCompleteness. The other 5 of the closure are already pinned.
  - config.json's lean.modules is pinned already.
- **The driver.** A stage_d6 wrapper (stage_d5 + the kernel step, writing D/kernel.json into the seal) and a
  campaign_run14 that calls it. The stage-D gate's rule changes from "mirror" to "kernel, mirror beside".
- **A dry run:**
  - **(i):** one NOT1, one XOR3 and one ANDOR3 at stage D through campaign_run14, about 2 h of cores, mostly ANDOR3
    and XOR3 stage D. Plus the re-run of leancell over these 95 sealed predictions, about 2 min, which must give the
    same verdicts.
  - **(ii):** the same three runs, plus a check that leancal accepts each sealed stage-D record.
