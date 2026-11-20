# Addendum to the dose report: the gate with a one-port budget, the solver's tolerance, the lines of c

**Development work. Exploratory, not preregistered, and nothing here is a claim.** Simulation only, one simulator,
one noise model, the nominal cell. It follows [`DOSE_REPORT.md`](DOSE_REPORT.md) and takes up three questions that
report left open. It recounts no claim of campaign 6.

Status on 2026-11-20: local and not pushed when it is written. Marks: **[K]** known, read from a file of section
6; **[I]** inferred, my reading.

## 1. The three results, in plain words

- **The Lean gate accepts a one-port testing budget for c** [K]. With that one number changed, campaign 6's gate
  file for the nominal cell passes at both doses, under noise as without. With the frozen two-port budget it gives
  the frozen verdict.
- **The 0.03 mV difference between identical cells at twice the dose was the solver's tolerance** [K]. With the
  relative tolerance ten times tighter, cells a and b cross in the same bracket.
- **Read on the stored voltage itself, what a run adds to it (the run offset) is the same in mV at both doses, on
  the lines of c** [K], post-hoc: 0.0595 mV at the unchanged dose, 0.0605 mV at twice the dose. This is one term of
  the noise, not the noise in general: the scatter within a run, `w`, is still open. Its growth on the lines is,
  for about a third, the conversion to mV; the rest is read-to-read scatter on one of the two lines, cause not
  found.

## 2. The gate with the one-port rule

**What was done** [K]. Campaign 5's `gate4.py` writes the gate's Lean file from an instance's budgets and verdicts.
`t1_gate.py` builds the nominal cell's instance at each dose with the frozen functions, then writes two files per
dose with the frozen generator: one as frozen, one in which c's `testingError` is the one-port budget of section
5.5 of the report (the larger of the two lines' at their needs, plus the measure terms H and S; S is 0 here), with
the verdicts the Python then gives. No frozen file is edited. Each file was checked as campaign 6 checked its own: one call of
campaign 5's `check.sh` per file, with the pinned Lean.

| File | c's testing budget, K = 0 / K = 3 (score units) | `checks` at K = 0 | `checks` at K = 3 | `check.sh` |
|---|---|---|---|---|
| 1x, frozen | 681 / 9135 | true | false | passed |
| 1x, one port | 371 / 4598 | true | **true** | passed |
| 2x, frozen | 677 / 9071 | true | false | passed |
| 2x, one port | 368 / 4565 | true | **true** | passed |

- `checks` is the gate's conjunction of `checkCascadeValid`, `checkTrainingSeparation` and
  `checkCascadeCalibrationOneSided`, proved by the kernel. A file compiles only if Lean agrees with the verdict
  written in it. Where the verdict is true, the file also derives the second layer's predicted outputs by
  `two_layer_monotone_recognition_one_sided`; in the one-port files that derivation holds at K = 3 too.
- **Which checker fails under the frozen budget** [K]: one, at both doses: `Disjunctions.check` on the second
  layer, and through it `checkCascadeValid`. That is the parameters' check of a single line's score at its need
  against the testing error. The calibration checker on the observed reads is true even with the two-port budget,
  and so is the training separation. These Booleans come from a diagnostic file of mine that evaluates each checker
  with `#eval`: Lean's evaluator, not a kernel proof. Its last column agrees with the kernel-checked theorems in
  all eight cases.
- Reading [I]: on the nominal cell, "no room for c under noise" is entirely the two-port number in the
  single-line check of the parameters. Nothing in the observed reads fails.

**The environment** [K]. Lean was not on the machine. It was installed from the archive the repository's own CI
pins (Lean 4.35.0, release `v4.35.0`), checked against the SHA-256 the CI file gives (`7289597a…8f6d`); the system
package `zstd` was installed to extract it. Both are outside every checkout.

## 3. The solver's tolerance

**What was done** [K]. `dosedev_tol.py` adds one allowed name, `reltol`, for scans only, beside the published
wrappers, which are unchanged; 13 tests, no simulation. Three pair scans were run at `reltol = 1e-5` instead of
the deck's `1e-4`. `abstol`, `vntol` and `chgtol` were kept.

The prediction, written before the runs: *if the cause is the tolerance, the 2x a/b difference shrinks well below
32 µV and the 1x crossing does not move by more than one bracket.*

| Scan | Crossing at `1e-4`, in stages | Crossing at `1e-5` |
|---|---|---|
| 2x, pair of a | 855/512 = 1.6699 | 857/512 = 1.6738 |
| 2x, pair of b | 861/512 = 1.6816 | 857/512 = 1.6738 |
| 1x, pair of a | 859/256 = 3.3555 | 859/256 = 3.3555 |

- At 2x the two cells differ by 31.7 µV at `1e-4` and give the same bracket at `1e-5`: the difference is below the
  bracket's width, 10.6 µV. At 1x the crossing of a did not move. **Both parts of the prediction hold** [K].
- Between the two tolerances a moved by +10.6 µV and b by −21.2 µV at 2x.
- **Two consequences** [I]. The "measure term of at least about 0.03 mV at 2x" of the report is a property of
  `reltol = 1e-4` at that dose, not of the cells. And any later protocol at 2x should run at `1e-5`, or justify
  `1e-4`.
- This does not show that `1e-5` is converged: a tighter tolerance was not tried. A null result would not have
  excluded every kind of solver error (the time step, for instance).

## 4. Why `w` grows on the lines of c at twice the dose

Analysis of the existing runs only: the 16 noisy runs and the two quiet runs. Post-hoc and descriptive.

**The run offset, read on the stored voltage itself** [K], post-hoc. For each noisy run and each line of c, the
stored voltage of the line's port before each FIRE read, minus the quiet run's at the same slot, averaged over the
run's six reads: its root mean square over the 16 rows is **0.0595 mV at 1x and 0.0605 mV at 2x**. No slope and no
latency enter this figure. For this term, on the lines, it answers the plan's question on the quantity itself: the
noise is constant in mV.

**The reads of a line are at one state, the same at both doses** [K]. Within a run, the six FIRE reads of a line
are at the same stored voltage to 0.05 µV. The trained state is −15.99 mV at 1x and −16.01 mV at 2x, and the quiet
FIRE latencies are the same. So no read sits on a steeper part of the latency curve at 2x.

**About a third of the growth is the conversion to mV** [K for the figures, I for the reading]. At that one state
the calibration deck's secant is 0.0951 per mV at 1x and 0.0785 at 2x, only because it spans one dose: 1.35 mV
against 2.71 mV. The same latency scatter therefore reads 21 % larger in mV at 2x. The lines' ratio of 1.63 in mV
is 1.21 from this, times 1.34 in latency units.

**The rest is read-to-read scatter on line 1** [K]; open:

| Within-run scatter of the FIRE latency, latency units | 1x | 2x | Ratio |
|---|---|---|---|
| line 1 | 0.0074 | 0.0132 | 1.78 |
| line 2 | 0.0089 | 0.0083 | 0.93 |

- It is not one run: all 8 rows of line 1 at 2x are above the 1x value, 7 of 8 above the largest 1x row. Without
  run 5200006 (singled out after the data), line 1 at 2x is still 1.56 times its 1x value.
- On line 1 at 2x the three teaching reads scatter more than the three tests (0.0166 against 0.0096).
- The split by line was made after seeing the rows.
- The cause was not found. One candidate, not tested: `reltol = 1e-4`, which section 3 shows to shift crossings by
  10 to 21 µV at this dose.

**A side finding** [K]: across the 16 line rows of a dose, a run's latency offset is only weakly tied to what the
run added to the stored voltage (correlation −0.13 at 1x, −0.57 at 2x). On these runs the run offset read from the
FIRE latency is mostly not the stored voltage's offset.

## 5. Not checked, and limits

- One cell, two doses. In section 2, decision 5's constants only: the constants read at each dose and the 0.03 mV
  term were not put through the gate.
- The gate shows that the one-port number satisfies the Lean statements on this instance. It does not show that a
  one-port budget is the right physical budget for a single-line test read; a protocol would have to argue that.
- In section 3: one tolerance (`1e-5`), three scans. The lines of c were not scanned at `1e-5`; the doses were not
  measured again, so the stages are those of the `1e-4` dose. Everything of steps B to D was run at `1e-4`.
- In section 4: no interval on the per-line figures (8 rows per line and dose, 6 reads each). The pairs of a and b
  were not split the same way. No waveform was opened by hand.
- No script of this addendum has unit tests except `dosedev_tol.py`. `t1_gate.py` stops unless the room it rebuilds
  equals the frozen prediction's; `t3_lines.py` stops unless its rows equal `G6.json`'s.

## 6. Files

| File | What | SHA-256 |
|---|---|---|
| `t1_gate.py` | writes the four gate files | `80906a2f11579f8999feccb2a720f60ad771317e9ab67e4809f2520282824b64` |
| `gate/GATE_INPUT.json` | the budgets and verdicts the files carry | `d55d1095703b927e92e65db256d088a5f1ba3f03ffa5421e435e4a98347c7ab3` |
| `gate/Gate6_1x_frozen.lean`, `gate/Gate6_1x_oneport.lean` | the gate files at 1x | `b0aa5385…4762`, `f8e32cfd…b1b6` |
| `gate/Gate6_2x_frozen.lean`, `gate/Gate6_2x_oneport.lean` | the gate files at 2x | `83167efd…4e59`, `22aaa1ad…b4cb` |
| `gate/check_Gate6_*.log` | what `check.sh` printed for each | four files |
| `gate/diag.sh`, `gate/DIAG_*.lean`, `gate/DIAG_*.out` | the diagnostic and its outputs | `diag.sh` `bfdfeec3…bff3` |
| `dosedev_tol.py`, `test_dosedev_tol.py` | the tolerance wrapper and its 13 tests | `5bef3787…b296`, `6d921bf5…f072` |
| `JOBS_T2.json`, `runsT2/` | the three scans at `1e-5` | `JOBS_T2.json` `ac785b47…56e7` |
| `t3_lines.py`, `analysis/T3_LINES.json` | section 4 | `d5db19d3…1117`, `e2a8d22b…0f42` |
