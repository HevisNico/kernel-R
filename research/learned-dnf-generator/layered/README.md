# The layered kernel-gate generator, for A∧B∧C, A∨B∨C and majority of three

A working prototype of [LAYERED_GENERATOR_DESIGN.md](LAYERED_GENERATOR_DESIGN.md), the design note accepted by the
coordinator (SHA-256 `6e72281ad47d9d1ecf33cf2dd7bef16783ca3149c80b9335a4e6b1248e547afd`).

- **Status.** Local only. No campaign file is edited; C5/check.sh is not touched.
- **Target.** The layered theory of research/learned-coincidence (#179): `Cascade M L N`, the four checkers of
  `LayeredMonotoneCheckerTargets.lean`, and `layered_monotone_recognition_one_sided`.
- **Calendar.** As the coordinator ruled, the separation premise is kept as it stands. Training is strictly
  sequential: one slot per (layer, cell, group, round).

## Files

| File | What |
|---|---|
| `lspec.py` | The layered spec. `load` checks every size against the Lean types: sources into the layer below, a stimulus and maxWrites + 1 rounds per active group, a replay of exactly the lower layers per lesson, 2^M tests. It refuses a missing or extra row, a value for an inactive group, and a float. It reports ports driven per input and per cell. |
| `lmirror.py` | A Python transliteration of the four checkers, in exact rationals, recording each condition with its kind and place. |
| `lemit.py` | The Lean writer: cells, nodes, layers, list-table traces, and per spec the four checker theorems (`= true|false := by decide +kernel`), `checks_*`, `outputs_*` and `function_*`. |
| `lsynth.py` | Traces from the additive model, in campaign units, with a strictly sequential calendar and four residual rules. |
| `lmutate.py` | 22 hand mutations, each meant to break one kind of condition. A mutation that cannot be built on a network raises `NotApplicable`. |
| `gencheck_layered.sh` | Compiles the 17 theory modules (the 13 of `../gencheck.sh` plus `LayeredMonotoneTarget`, `LayeredMonotoneRecognition`, `LayeredMonotoneCheckerTargets`, `LayeredMonotoneCheckerProofs`). For each file it audits the tokens and axioms, times the compile, applies a timeout and supports `--expect-fail`. |
| `run_layered.sh` | Compiles every step-2 file and the flipped controls. |
| `tests/test_example.py` | Test (a): the repository's own example and its five rejection fixtures. |
| `tests/networks.py` | The nine networks of the note's section 2.2. |
| `tests/run_layered.py` | Writes the files of 4(b), 4(c) and the controls, plus `REPORT.json`. |
| `tests/test_hashes.py` | Regenerates the 23 generated files and compares their hashes. |
| `tests/network_search.py`, `tests/network_chosen.py` | The exhaustive search behind the note's section 2. It is not a Lean proof. |
| `results/` | Logs, `REPORT.json` (with `generated_sha256`), `flip_check.json`, `example.json`. |

## Commands

```
python3 -I tests/test_example.py OUT/LayeredEx.lean        # test (a), mirror part, and the Lean file
python3 -I tests/run_layered.py OUT/lm4                    # the files of 4(b), 4(c) and the controls
LEAN=/opt/lean/lean-4.35.0-linux/bin/lean GENCHECK_BUILD=OUT/build bash gencheck_layered.sh OUT/LayeredEx.lean
LEAN=… GENCHECK_BUILD=… bash run_layered.sh OUT/lm4
python3 -I ../tests/flip_check.py OUT/lm4 /opt/lean/lean-4.35.0-linux/bin/lean OUT/build
python3 -I tests/test_hashes.py check
```

## Results

**Tags and setup.**

- [K] means run here, with the interpreter named. [I] means inferred. [G] means guessed.
- Lean 4.35.0 was checked against the CI's pinned SHA-256 (see `../README.md`). The theory is the checkout's
  research/learned-coincidence, whose `Layered*` files are identical to main `d50cdec`.
- Compile times are the wall time of one `lean` call, one file at a time, on a 4-core Xeon reported at 2.10 GHz.

### Test (a): the repository's example

[K: Python 3.13.18 for the mirror, Lean for the verdicts]

- **Mirror.** `LayeredMonotoneExample` (`circuit`, `train`, `test`) is transcribed as a spec.
  - It passes all four checkers, as `accepted_*` in `LayeredMonotoneCheckerExamples.lean:47–53` does.
  - Its predict equals (A∧B)∨(C∧D) on all 16 masks.
  - The five fixtures of `LayeredMonotoneCheckerExamples.lean:55–68` each fail exactly the checker their `example`
    names, on one kind:

    | Fixture | Checker that fails | Kind |
    |---|---|---|
    | replay 0 | separation | training before tests |
    | silentOutsideBudget | reads | residual |
    | firingAnchorBelowBound | reads | anchor |
    | submaskAboveObserved | reads | submask |
    | lowerReplayOutsideBudget | training | residual |
- **Lean.** One file holds the six specs. It compiled in 20.7 s, with 32 theorems on the allowed axioms (`results/example.log`).
- **Two writer bugs, fixed before that pass.**
  - A multi-line `Cell` literal did not parse, so each cell became its own one-line `def`.
  - The rewritten `checks_*` goal needed a closing `rfl`.
  - The log of the failing compile was overwritten by the rerun and is **not** kept.

### Synthetic cases, 4(b)

[K: Python 3.13.18 generation; Lean verdicts]

- Each network file holds 4 specs, one per residual rule (zero, +budget, −budget, seeded:7). Every spec asserts:
  - the four checkers, all true;
  - `checks_*`;
  - `outputs_*`, the layered recognition theorem through the four soundness lemmas;
  - `function_*`: `circuit.predict x 0` equals the function, stated independently, on the whole cube.

| Network | Cells | Two-port report | Compile | Theorems |
|---|---|---|---|---|
| AND3a: L1 both(A,B), copy(C); L2 both | 3 | inputs 1, 1, 1 | 10.2 s | 28 |
| AND3b: L1 both(A,B), both(C,C); L2 both | 3 | C on 2 ports | 10.3 s | 28 |
| AND3c: L1 both(A,B), both(B,C); L2 both | 3 | B on 2 ports | 10.2 s | 28 |
| OR3a: L1 either(A,B), copy(C); L2 either | 3 | inputs 1, 1, 1 | 19.0 s | 28 |
| OR3b: L1 either(A,B), both(C,C); L2 either | 3 | C on 2 ports | 19.0 s | 28 |
| OR3c: L1 either(A,B), either(B,C); L2 either | 3 | B on 2 ports | 22.8 s | 28 |
| MAJa: L1 both AB, AC, BC; L2 either(0,1), copy(2); L3 either | 6 | every input on 2 ports | 76.7 s | 28 |
| MAJb: as MAJa, with L2.1 both(2,2) | 6 | inputs on 2; L1.2 on 2 | 89.0 s | 28 |
| MAJc: L1 both(A,B), either(A,B), copy(C); L2 copy(0), both(1,2); L3 either | 6 | A, B on 2 ports | 81.0 s | 28 |

**Calendar of these traces** [K, `lsynth.py`]:

- one slot per (layer, cell, group, round);
- slots 22 units apart at depth 2, 24 at depth 3;
- layer-1 cells read the external inputs with delay 0, and routed lines have delay 3/2;
- one write limit of 5 per cell, so 6 rounds per group.

### Premise failures, 4(c)

[K: same tools]

- The 22 mutations of `lmutate.py` were built on AND3a, OR3a and MAJa, each from its seeded:7 base. 64 could be built.
- Two do not exist on AND3a, whose top cell is a `both`:
  - a proper firing submask (`submask`);
  - a silent lower read inside an upper lesson's replay (`replayresidual`). Every AND3a upper lesson makes both
    lower cells fire.
- In the mirror, every one of the 64 fails only its intended kind.
  - Three intended kinds have two parts. `copysource` (a source on a copy's port 1) also fails `route`, because its
    reads keep no arrival there. `stimulus` (a wrong lesson stimulus) also fails `replay input`, because the trace
    keeps its lessons.
  - `timing` fails "timing valid" in three checkers, because every decoder checks it.
- Lean agreed on every per-checker value:

  | File | Compile | Theorems |
  |---|---|---|
  | Mut_AND3a | 43.1 s | 100 |
  | Mut_OR3a | 93.8 s | 110 |
  | Mut_MAJa | 419.8 s | 110 |

  None came near the 30-minute stop.
- The full run of `run_layered.sh` took 15 min 46 s (`results/run_layered.log`).

### Controls

[K]

- **Flips.** `Control_pass` (AND3a, zero) compiled in 3.5 s and `Control_fail` (its `residual` mutation) in 3.2 s.
  Each has 4 asserted checker Booleans. Each flipped copy differs from its original in exactly one line and fails to
  compile, with its `decide` error at that line (`results/flip_check.json`, by `../tests/flip_check.py`).
  - The other errors all depend on the flip, checked over the whole theorem body. `checks_*` fails whenever the flip
    changes the conjunction: in the four pass copies and in `Flip_fail_2`, which flips the one false checker.
    `outputs_*` fails in the four pass copies.
  - No error falls elsewhere.
- **Missing row.** A spec missing one round of an AND3a L2 lesson is refused: "training[1][0][0] (maxWrites + 1
  rounds): expected a list of 6, got a list of 5".

### Reproducibility

[K]

- `results/REPORT.json` records the SHA-256 of all 23 generated files: the 9 Synth files, 3 Mut files, 2 Controls,
  8 Flips and LayeredEx. They were recorded with **Python 3.13.18**; nothing here uses numpy.
- They equal the hashes of the files that were compiled.
- `tests/test_hashes.py check` gave 23 of 23 identical under Python 3.13.18, and under /opt/venv312 (Python 3.12.3).

### Estimates

- [G] Kernel time per spec grows with the number of batches and replays. Majority took about 20 s per spec, against
  about 2.5 s for the 3-cell networks. The separation and replay checks dominate [I, from the bench note].

## Not checked

- Measured cells. Every case here is synthetic: one latency per layer, one slot spacing, parameters of a chosen kind.
  The real values of the copy cell's unused port 1, layer-3 latencies and slot lengths come from the circuit side.
- Whether a routed pulse can drive two ports (`both(X, X)`), or an input two cells, on the bench.
- Networks beyond the nine, and any shape beyond M = 3 and depth 3.
- The widened separation premise (option 2 of the note's section 3). It was ruled out for step 2 and is not built.
- The frozen C5/check.sh on a layered file. It compiles no `Layered*` module, so it cannot check one.
