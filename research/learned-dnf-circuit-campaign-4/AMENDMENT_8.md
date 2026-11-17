# Campaign 4, amendment 8: the rehearsal's attempt 2 completed, not redone; the kernel of the floats pinned

Pushed alone on `research/learned-dnf-circuit-campaign-4`, after `PREDICTION.md` (commit `1596b36`) and amendments
1 to 7 (commits `c14124f`, `d6a75a9`, `41cf88b`, `a167f3c`, `6c5630f`, `424f6f9`, `53d50f3`), before the completion
of the rehearsal and before `BEFORE_M.md`. It is the owner's decision. Nothing else in `PREDICTION.md` or amendments
1 to 7 changes.

**No campaign seed (7501 and up) has been simulated, except as the seed guard's refusals, which simulate nothing.**
Every run below is on the nominal cell (model section `tt`, no mismatch, no seed).

## 1. The decision

The rehearsal's attempt 2 is **completed, not redone**. Every run of attempt 2 ended, and every stage was collected
through the kit; only the end of the chain failed, in the audit of a file written after the last run (section 4). The
files that change for the completion are used by no run of the rehearsal, no prediction and no kit launch
(section 2); no check of the record was evaluated or looked at; and the runs are deterministic. Completing them
therefore selects nothing.

The rehearsal's record, `REHEARSAL.json`, is written by the completion script (`complete_rehearsal.py`) on the new
frozen commit, from attempt 2's collected folders and with `rehearsal.py`'s own functions, `rehearsal.py` unchanged
(its `stage` function is a closure inside its `main` and cannot be called; the completion carries a copy of it, which
differs only in its names and in the governing protocol of the two new stages, below). It records `runs_commit`
(`3156ee4`, the commit the runs used), `frozen_commit` and `frozen_tree` (the new freeze), the files that differ
between them, the CPU model and the OpenBLAS core (section 3).

**Two stages are rerun: the memory stages, as `MEMD2` and `MEMI2`.** `PREDICTION.md` (Rehearsal, Memory) requires the
peak resident memory of the machine over four need-7 noisy runs at a time. `rehearsal.py` samples it in its own
process during the kit launches of `MEMD` and `MEMI` and keeps it only in the record it writes at the end, so attempt
2's machine peaks were lost when it stopped. The kit's evidence holds each run's own `peak_rss_MB`, which does not
measure the machine's peak. So the completion runs the same two stages again, under the new names, on the new frozen
commit, through the kit, detached, with the uptime recorder, four runs at a time, and with the machine's memory
sampled as `rehearsal.py` samples it. Their stage files name the governing protocol of attempt 2's `MEMD` and `MEMI`,
`PREDICTED.json`: `plan.governing_of` maps `MEMD` and `MEMI` explicitly but would read a new name by its first letter
(`M`, so `PREDICTION.md`), so the completion takes the governing protocol of `MEMD` and `MEMI` for the two new names,
`plan.py` unchanged. The runs are the same, their ids marked `-2`. Their wall times enter the limits basis like those
of any complete run of their kind, as do the wall times of attempt 2's `MEMD` and `MEMI` runs. Attempt 2's per-run
`peak_rss_MB` of those runs is reported beside the new machine peaks, for comparison only. **Everything else in the
record comes from attempt 2.**

The completion also repeats the two tests that `rehearsal.py` ran outside any kit launch and that simulate nothing:
the seed guard's refusal of seed 7501 outside the kit, and the stage files' safeguards (i) and (ii). They run on the
new frozen code, whose files for them (`run4.py`, `plan.py`) are byte-identical to `3156ee4`'s. The analysis is
rerun on attempt 2's collected folders, and its output is compared with what attempt 2's analysis wrote before the
failure.

If the machine that holds attempt 2's work folder is reset before the completion, `restore_attempt.py` rebuilds it
from GitHub (`rehearsal/run-2/` and its evidence branch), checking every file against the SHA-256 that
`rehearsal/run-2/NOTE.md` and the kit's `SURVIVORS.json` record. It was tested on 2026-11-17: the restored folder
equals attempt 2's file for file, except 15 bytecode caches (`__pycache__/*.pyc`) that the interpreter wrote in the
clone during attempt 2 and that git ignores.

The completion runs **once**, on the new frozen commit. If it shows a further defect, the defect is fixed, the
implementation refrozen, the completion rerun (its memory stages under new names again), and all of it declared.

## 2. The files that differ between `3156ee4` and the new frozen commit

None of them is used by a run of the rehearsal (simulation, prediction or kit launch). `plan.py`, `c4.py`,
`rehearsal.py` and every other frozen file but `check.sh` are unchanged.

| File | What it is | Why no run of the rehearsal uses it |
|---|---|---|
| `check.sh` | The audit takes the subset rule: every theorem's `#print axioms` must be a subset of `[propext, Classical.choice, Quot.sound]`, so a theorem on no axiom passes; it takes several files; it pins the kernel (section 3) | It audits Lean files written after the runs (the gate written from `PREDICTED.json`, M8). No run, prediction or launch executes it; the kit only compares its SHA-256, in each manifest's frozen-source inventory, with the clone of the same stage |
| `.github/workflows/learned-dnf-circuit-campaign-4.yml` | CI: the cases below, and the comparison of section 3 | CI only |
| `structural_compare.py` | The structural comparison of section 3 | CI only, on a runner without AVX-512; did not exist at the runs |
| `m8_case.py` | M8's eligible path, code path only: P0's prediction (`cases.py`) with attempt 2's run without noise (`collected-N-a/a-None-quiet`, its waveform fetched from the evidence branch, checked against `SURVIVORS.json`) | CI only; did not exist at the runs |
| `audit_cases.sh`, `audit-cases/*.lean` | The negative cases of the audit (below), and a check that no campaign Lean file uses their constructs | CI only; did not exist at the runs |
| `complete_rehearsal.py`, `complete_rehearsal.sh` | The completion (section 1) and its detached wrapper | Run after the runs; did not exist at them |
| `restore_attempt.py` | The restore of attempt 2 from GitHub (section 1) | Run, if needed, before the completion; did not exist at the runs |
| `WIP.md` | The work branch's note, naming the new frozen commit | Text |
| `rehearsal/run-1-interrupted/` (4 959 files), `rehearsal/run-2/` (8 587 files) | The evidence of attempts 1 and 2, copied as they stand (waveforms of 10 MB and more on their evidence branches) | Evidence, written after the runs; no run reads it (CI's M8 case and the restore read `run-2/`) |

**The cases of the audit**, run by CI on every push:

| Case | Files | Expected | What it proves |
|---|---|---|---|
| M8 with no eligible instance | `rehearsal/run-2/analysis/M8.lean` (attempt 2's) | passes | a theorem on no axiom (`no_eligible_instance`) passes the subset rule: the defect of section 4 is fixed |
| M8, the eligible path | written by `m8_case.py` | passes | the eligible path of M8 runs and writes a file the kernel accepts, its theorems on the three axioms |
| NegNative | `audit-cases/NativeDecl.lean`, `audit-cases/NegNative.lean` | refused on the check of the axioms | a theorem that rests on the compiler's evaluation is refused, though the audited file has none of the forbidden tokens. Lean 4.35.0 has no `Lean.trustCompiler`; `native_decide` declares an auxiliary axiom (`…_native.native_decide.ax_1_1`), here in the imported module, which builds the tactic's name from a split string and so passes the token filter |
| NegSorry | `audit-cases/NegSorry.lean` | refused on the check of the axioms | a theorem on `sorryAx` is refused, though its text has none of the forbidden tokens and its warning is not turned into an error |
| NegOwnAxiom | `audit-cases/OwnAxiomDecl.lean`, `audit-cases/NegOwnAxiom.lean` | refused on the check of the axioms | a theorem on an axiom of our own, declared without the token in an imported module (which itself passes), is refused |

`audit_cases.sh` asserts that each negative case fails on the check of the axioms, naming its axiom, and not on the
token filter. These five Lean test files are written by hand and are never written by the campaign code; no
campaign Lean file (the gate cases, their targets, the mirror mutations, the rehearsal's gate and M8) contains
`run_cmd`, `addDecl`, `sorryAx`, `warningAsError` or any other construct of these cases, which `audit_cases.sh`
checks.

## 3. The kernel of the floats

**The finding.** Some reported values are floats computed with numpy's OpenBLAS: the fits of `np.polyfit`
(`predicted.py`) in `geometric_fits` and `validation_residual_M5`. OpenBLAS chooses its kernel from the CPU, and the
last digits of these floats depend on that kernel. They decide nothing: since amendment 3, everything that becomes an
integer is computed exactly. But the byte comparisons depend on them: `check.sh`'s comparison of `CASES.json` and
`MUTATIONS.json` with the files under `rehearsal/`, and the byte reproduction of `PREDICTED.json` by the analysis.
The files under `rehearsal/` and every number of attempt 2 were computed with the SkylakeX kernel, which OpenBLAS
selects by itself on a CPU with AVX-512.

**The rule.** numpy's OpenBLAS is pinned to the SkylakeX kernel (`OPENBLAS_CORETYPE=SkylakeX`) wherever these
numbers are computed or compared, on a CPU with `avx512f`, and is refused otherwise with a clear message: in
`check.sh`, in the completion (its wrapper sets the pin, and `complete_rehearsal.py` refuses to run without it), and
in the campaign's computation of `PREDICTED.json`. On a CPU with AVX-512 the pin only locks the choice OpenBLAS makes
by itself, so attempt 2's numbers and the completion's are those of the same kernel. `REHEARSAL.json` records the CPU
model and the core that OpenBLAS reports. At the campaign, the kit's inventory already records each machine's CPU
model, kernel, processors and memory; `PREDICTED.json` is computed on machine `a`, after checking `avx512f`, with
`OPENBLAS_CORETYPE=SkylakeX` set, and the campaign director's report of that step states both. Machine `b` only
simulates (ngspice does not use numpy). The binding guarantee is the byte reproduction of `PREDICTED.json`, by the
analysis and by the coordinator's independent check on an AVX-512 Xeon. `c4.py` and `plan.py` do not change.

**CI.** On a runner with AVX-512, `check.sh` compares the generated files byte for byte, as before. On a runner
without it, CI compares the two generated JSON files structurally (`structural_compare.py`): every integer, string
(rationals are strings), Boolean and null exactly equal, every list and object of the same shape, and only floats
compared, with `math.isclose(a, b, rel_tol=1e-9, abs_tol=1e-15)`. The tolerance was set after the test under the
Haswell kernel (largest relative difference 2.68e-12, in `validation_residual_M5.c`); it applies to CI's structural
comparison only, and the floats it compares decide nothing. The three generated Lean files are compared byte for byte
on every runner (the kernel does not change them), and the Lean compile and the audit run on every runner. `check.sh`
states the CPU model, the core OpenBLAS reports, and which comparison it made. The structural path is exercised by CI
on every runner, whatever its CPU: a `CASES.json` written with `OPENBLAS_CORETYPE=Haswell` must be accepted against
the committed file, and a copy of it with one integer changed (P0's `Q1` + 1) must be refused.

**What happened (2026-11-17, UTC).** CI on commit `ee33af1` (run 44059225642, started 09:50:16) failed in
`check.sh`: `CASES.json rehearsal/gate-cases-4/CASES.json differ: byte 341, line 21`, a float of P0's
`geometric_fits`. Its rerun (attempt 2 of that run) failed the same way. A rerun of the last green commit, `6ef8cb5`
(run 44054282794, attempt 2), passed. The failing runs ran on the runner image `ubuntu-24.04` version
`20261111.370.1`, the passing one on `20261111.127.1`. On the campaign director's machine, an AVX-512 Xeon ("Intel(R)
Xeon(R) Processor @ 2.10GHz", OpenBLAS 0.3.30 of numpy 2.3.5), `cases.py` writes a `CASES.json` equal byte for byte
to the committed one with OpenBLAS's own choice and with `OPENBLAS_CORETYPE` set to SkylakeX or Cooperlake (both run
the SkylakeX core), and one that differs at the same place (character 341, line 21) with Haswell, Zen (which runs the
Haswell core) or Sandybridge. Under Haswell, `CASES.json` and `MUTATIONS.json` differ only in floats (81 of 144, and
190 of 342), and the three generated Lean files and the verdicts of `cases.py` are unchanged.

## 4. What happened to attempt 2 (2026-11-17, UTC)

- **05:48:47**: attempt 2 starts, `rehearsal.py` on commit `3156ee4`, from a clean clone at that commit, detached
  from the director's session. `uptime -s` reads `2026-11-17 05:34:37` (the machine had restarted at 05:34:37,
  while nothing ran).
- Every stage completes and is collected through the kit, machine `a` then `b`: M 05:58:47 and 06:14:48; X
  06:17:18 and 07:29:19; E 07:40:20 and 07:51:50; N 08:06:51 and 08:17:51; MEMD 08:35:23 (b); MEMI 08:37:23 (a) and
  08:58:56 (b); GUARD 08:58:56. The gate written from the rehearsal's `PREDICTED.json` passes `check.sh`.
- **09:01:26**: `rehearsal.py` stops with exit 1. The analysis has written `M8.lean`, and the nominal cell is not
  eligible (`PREDICTED.json`), so its only theorem is `no_eligible_instance : True := trivial`, on no axiom.
  `check.sh` required every theorem to be on exactly the three axioms and refused it. `REHEARSAL.json` is not
  written.
- `uptime -s` reads the same value on all 35 lines of the uptime log, from the start to 09:01:56: no restart.
- **No check of the record was evaluated or looked at**: neither reproducibility, the zero-amplitude check, the
  split extraction's identity, memory, the seed guard, the safeguards, the limits basis, nor any wall-time ratio.
  The director read, to diagnose the failure: the log's last lines, the nominal cell's eligibility in
  `PREDICTED.json`, the list of top-level keys of attempt 2's `RESULTS.json`, and `M8.lean`. The director also ran
  `m8_case.py`, whose verdicts are of P0's prediction with the nominal run, not a check of the record.
- **Checked before the completion** (by the campaign director, on attempt 2): the uptime log, constant; every
  stage's `STATE.json` complete with every run of its manifest recorded and complete (GUARD: its two refusals); every
  collected file equal to the evidence; no seed from 7501 simulated (the rehearsal's 46 decks set no seed, its 92 run
  records have seed `None`, noise seeds 90951 to 90953, no deck under GUARD); the clone based on `3156ee4`, with no
  uncommitted change, and its 41 frozen files equal to `3156ee4`'s.
- **Pushed**: attempt 2's waveforms of 10 MB and more on `evidence/learned-dnf-circuit-campaign-4-rehearsal-run-2`
  (commits `2a7c6f9` to `83df0a3`, 09:12:58 to 09:17:14); attempt 2's evidence, its note and these checks in
  `rehearsal/run-2/` on the work branch (commit `6ef8cb5`, 09:17:45); the code of sections 2 and 3 (commits `ee33af1`,
  09:50:12, `28bd116`, 10:19:20, and `a3dc736`, 10:31:39).
