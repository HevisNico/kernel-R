# A kernel-gate generator parameterized by shape and function

A working prototype of the design note GENERATOR_DESIGN.md (SHA-256 `5c3783b9…78c7`, accepted by the coordinator).
It is local only. No campaign file is edited. Frozen campaign-5 code is imported as a library from an extracted copy
of the branch `research/learned-dnf-circuit-campaign-6-impl` at `ecfcd1c1` (IMPL).

The generator writes Lean files for the two-layer one-sided theory (`Cascade A B M`, the three checkers of
`research/learned-coincidence/MonotonePremiseTargets.lean`, `two_layer_monotone_recognition_one_sided`). It works for
any shape and any monotone DNF given as terms and lines. The layered theory is not covered yet.

## Files

| File | What |
|---|---|
| `spec.py` | The instance spec (design note 3.1). `load` returns exact values. It refuses any missing or extra row, any float and any unknown key. It reports the two-port physical flag. |
| `emit.py` | The Lean writer. The `gate4` style reproduces campaign 5's `gate4.py`. The `generic` style adds `valid_`, `separation_` and `calibration_` theorems. |
| `legacy.py` | gate4 instance dicts mapped to specs. Uses the frozen `gate4.verdicts` and the `predicted` constants. |
| `mirror.py` | A Python transliteration of the three checkers, in exact rationals, with a condition-by-condition record. |
| `synth.py` | Observations built from the additive model: a calendar, and residual rules zero, ±budget and seeded. |
| `mutate.py` | 15 hand mutations, each meant to break one kind of condition. |
| `gencheck.sh` | Compiles the 13 theory modules. For each file it refuses forbidden tokens, compiles with warnings as errors and audits the axioms, times the compile, and applies a timeout. It has an `--expect-fail` mode. |
| `run_m4.sh` | Compiles every M4 file and the flipped controls. |
| `tests/test_legacy.py` | Test (a): the 7 references, byte for byte. |
| `tests/test_mirror.py` | Mirror against the Lean-asserted references, and the room model against the mirror. |
| `tests/k3_finding.py` | The room model is stricter than the kernel on c's both-lines read. |
| `tests/run_synth.py` | Writes the files of tests (b), (c) and the controls, and `REPORT.json`. |

## Environment

- Lean 4.35.0 from `lean-4.35.0-linux.tar.zst`, checked against the CI's pinned SHA-256 (`7289597a…268f6d`, OK) and
  extracted to `/opt/lean`, outside the checkout.
- **Two interpreters.**
  - The unpinned system Python 3.13.18 with numpy 2.5.3 (phase 1, and `python3` below).
  - `/opt/venv312`: Python 3.12.3 with numpy 2.3.5. Its interpreter SHA-256 equals `c4.PINNED`; numpy's RECORD
    differs, as expected outside the pinned venv. OpenBLAS reports SkylakeX.
- The frozen C5/check.sh, run as is with `PYTHON=/opt/venv312/bin/python` on `Gate6_7804.lean`: **passed**.
  - Step 2: "equal to expected/ … byte for byte".
  - The audit: Gate5Cases 33, Gate5CasesTargets 85, MirrorMutations 57 and Gate6_7804 3 theorems, all on the three allowed axioms.
  - Wall time: 9 min 32 s.

## Commands

```
IMPL=…/impl              # git archive of research/ at ecfcd1c1, extracted
python3 -I tests/test_legacy.py $IMPL                 # test (a)
python3 -I tests/test_mirror.py $IMPL                 # mirror cross-check
/opt/venv312/bin/python -I tests/k3_finding.py $IMPL OUT/K3Finding.lean
python3 -I tests/run_synth.py OUT/m4
LEAN=/opt/lean/lean-4.35.0-linux/bin/lean GENCHECK_BUILD=OUT/build bash gencheck.sh FILE.lean
LEAN=… GENCHECK_BUILD=… bash run_m4.sh OUT/m4
```

## Results

Tags:

- [K]: run here, with the interpreter named.
- [I]: inferred.
- [G]: guessed.

The logs and `REPORT.json` are copied under `results/`. Compile times are the wall time of one `lean` call, one file at a time, on a
4-core Xeon. Before the container restart the CPU was reported at 2.30 GHz: everything up to Mut_S0, Gen6_7804,
K3Finding and the first frozen check.sh. After the restart it was reported at 2.10 GHz: Mut_S1, Reach, the controls,
the flips and the second frozen check.sh. So the times of the two groups are not strictly comparable [K, from
/proc/cpuinfo as check.sh prints it].

### Test (a): byte for byte against gate4

- [K, Python 3.13.18 / numpy 2.5.3 (unpinned), and again with /opt/venv312 (3.12.3 / 2.3.5)] `tests/test_legacy.py`
  wrote 7 of 7 references identical byte for byte: `Gate6_7802` to `7805` (c1), `Gate6_7701` and `7706` (r3), and
  C5 `expected/Gate5Cases.lean` (342 851 bytes, 13 cases).
- The missing-row refusal of `spec.load` was on, so no reference relies on gate4's `getD` fallback.
- [K, phase 1, Python 3.13.18] The frozen gate4.py itself rewrote the same 7 files byte for byte.
- [K] `gencheck.sh` on the generated `Gate6_7804`: passed, compiled in 3.3 s, 3 theorems.

### Mirror cross-check (M3)

- [K, Python 3.13.18] There are 0 differences in 135 verdicts against the Lean-asserted references:
  `Gate5CasesTargets.lean` (78) and `MirrorMutations.lean` (57).
  - For each of the 19 mutations, the mirror's failing conditions are exactly the mutation's kind.
  - `maxwrites` keeps 7 firstTrain rows for Q1 = 3. `spec.load` refuses it. The test compares it through the
    test-only option `truncate_rows` (in `tests/test_mirror.py`, not in the generator).
- [K, Python 3.13.18] `gate4.verdicts` (the room model) and the mirror give the same conjunction on the 13 cases and
  the 6 campaign-6 instances, at K0 and K3. Condition-level detail is in `tests/test_mirror.py` and the probe in the
  M3 report.
- **The finding.** [K, /opt/venv312 for the construction; the kernel for the verdicts]
  - The room model's both-lines condition is `pair >= max(Z_1, Z_2) + te`. The kernel's `checkFiringMask` has no
    `+ te`.
  - `tests/k3_finding.py` builds two cases with the frozen cases.py: G1 with pair = max + te − 1 = 102016, and G0 with
    pair = max = 101470.
  - At K0, gate4.verdicts says false for both, and the mirror says true. The Lean file asserting the mirror's values
    compiled: 18 theorems in 11.6 s, including `checks_G1_K0 = true` and `checks_G0_K0 = true`.
  - So the room model refuses instances the kernel certifies when the pair lies in [max, max + te). It never accepts
    a wrong one [I, from the direction of the inequality].

### Synthetic cases (b)

- [K, Python 3.13.18 for the generation; Lean 4.35.0 for the verdicts]
- Each case holds 4 specs, residual rules zero, +budget, −budget and seeded:7, at K0. Each spec asserts `checks`,
  the three per-checker theorems, `outputs_*` (the derivation through
  `two_layer_monotone_recognition_one_sided A B M`) and `function_*`. `function_*` checks the cascade's `output`
  against a function stated independently of the terms, over the whole cube. Every verdict is true.

| Case | Shape | Function | Two-port | Compile | Theorems |
|---|---|---|---|---|---|
| S0 | 2 1 4 | (A∧B)∨(C∧D) | yes | 14.3 s | 24 |
| S1, candidate 1 | 2 1 3 | B∧(A∨C) | yes | 8.6 s | 24 |
| S2 | 2 1 3 | (A∧B)∨C | yes | 8.3 s | 24 |
| S3, majority of three | 3 1 3 | 2 ≤ card x | **no** (3 lines) | 19.3 s | 24 |
| S4 | 2 2 4 | out 0 (A∧B)∨(C∧D), out 1 A∧B | yes | 20.8 s | 28 |
| S5, A = 0 | 0 1 2 | constant true | n/a | 0.9 s | 24 |

- S5 (`Cascade 0 1 2`, `alwaysFire`) needed nothing special in the writer. `Fin 0` fields are written as
  `fun a => a.elim0`, and the term table as `Fin.elim0`.
- Its audit: 16 of S5's 24 theorems are on all three allowed axioms and 8 are on fewer. All are within the allowed set.

### Premise failures (c)

- [K, same tools] All verdicts are `= false`.
- `Mut_S0` and `Mut_S1` each hold the 15 mutations of `mutate.py` plus `edge` (a residual at budget + 1 on the
  +budget base), so 16 specs per file.
  - In the mirror, every one fails only its intended kind.
  - Lean agreed on every per-checker value: Mut_S0 compiled in 37.0 s (64 theorems), Mut_S1 in 116.9 s (64).
- `Reach`: comparable terms {A} and {A, B}, regenerated by synth. Only `reachable` fails. Lean agreed: 2.2 s,
  4 theorems.

### Controls (4.4)

- [K]
  - `Control_pass` (5.2 s) and `Control_fail` (4.7 s) compile.
  - Each of their 8 asserted Booleans, flipped one at a time, makes its copy **fail** to compile, with
    "Tactic `decide` failed to reduce".
  - Lean's message is its generic one. Its elaborator diagnosis got stuck on a `Rat` comparison of the delay, so the
    message does not itself say "false". The control holds by logic [I]: each original value was proved by the
    kernel, so the flipped statement is false.
- [K] A spec with one missing `teach` row is refused: "teach: expected a list of 12, got a list of 11".

**Flip control, in detail.** [K] `tests/flip_check.py` checks each of the 8 copies. The output is in
`results/flip_check.json`.

- Each copy differs from its original in exactly one line, the flipped theorem.
- Each copy has a `decide` error at that line and theorem.
- The only other error is in `Flip_pass_0`, which flips `checks_C0_K0`. There, `outputs_C0_K0` (line 79) fails with a
  type mismatch, because its proof starts `have checked := checks_C0_K0`. The script detects that dependence.
- No error falls anywhere else.

### Reproducibility of the generated files

- [K] The generated Lean files are not kept. `results/REPORT.json` records the SHA-256 of all 20 files under
  `generated_sha256`:
  - Synth_S0 to S5, Mut_S0, Mut_S1, Reach, Control_pass, Control_fail;
  - the 8 Flip copies;
  - K3Finding.
- They were recorded with **/opt/venv312 (Python 3.12.3, numpy 2.3.5)** by `tests/test_hashes.py record`. They equal
  the hashes of the files that were compiled above.
- `tests/test_hashes.py check IMPL` regenerates and compares. It gave 20 of 20 identical under /opt/venv312, and
  20 of 20 under the unpinned Python 3.13.18 with numpy 2.5.3.
- Only K3Finding depends on numpy, through cases.py's geometric fit.

### The restart incident

- The container restarted during the M4 run, after Mut_S0 had compiled, and that run's log stops there
  (`results/m4.log`).
- The remaining files were compiled in a second pass (`results/m4rest.log`). For that pass, `run_m4.sh` was
  **edited temporarily** to drop `Synth_*` from its first loop, and then **restored**.
- The restored file has SHA-256 `9a636917add21763d401074dfcd8615258292f252fbdf7c195f1db5c6f53b7c8`.

### The frozen C5/check.sh

- [K, /opt/venv312] It passed on `Gate6_7804.lean`. Its last line is "check.sh: passed" (`results/frozen_check_7804.log`).
- [K, /opt/venv312] It also passed, run as is, on the generic-style `Synth_S1.lean`. That file is candidate 1,
  `Cascade 2 1 3`, with per-checker, `outputs_*` and `function_*` theorems. Results:
  - "Synth_S1: 24 theorems, each on a subset of [propext, Classical.choice, Quot.sound] (24 on all three)";
  - last line "check.sh: passed";
  - 13 min 44 s, on the 2.10 GHz CPU (`results/frozen_check_S1.log`).

  So the campaign's own harness accepts a generated file of another shape.

### Estimates

- [G] The kernel time grows with the number of specs per file and with 2^M · B · 2^A. The largest case here,
  Mut_S1, took 117 s. No case came near the 30-minute limit. I measured only the shapes listed.

## Not checked

- The layered theory (#179). There is no writer and no mirror for it.
- Kernel cost beyond the shapes tested: M ≤ 4, B ≤ 2, three-line OR cells.
- Synthetic cases use one latency per layer and one slot spacing. Real latencies and the skewed pair read of c are
  exercised only through the legacy references.
- The physical feasibility of a shared input (S1, candidate 1).
