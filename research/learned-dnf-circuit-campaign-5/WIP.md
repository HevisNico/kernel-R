# Campaign 5: the work branch (research/learned-dnf-circuit-campaign-5-wip)

The implementation of campaign 5's `PREDICTION.md` (commit `a2d8bad`, SHA-256 `36249501…0b10`, copied here byte for
byte). It is campaign 4's frozen implementation (`093995b`, copied unchanged at `b2a0561`), adapted as D5-8 says and the
text requires. The frozen files are `plan.FROZEN`. This branch descends from `a2d8bad` through the merge `8b6be77`, so
that a stage's source commit, built from the frozen commit plus the files of the closed list, descends from the
protocol commit, as the kit requires.

## Files changed against 093995b, and why

| File | Change | Rule |
|---|---|---|
| `c4.py` | folder; seeds 7601 up; development seeds 7691–7693; nominal noise seed 90 961, round 1 only; `limit` = 10 ceil(2 e / 10) and `rehearsal_limit` = min(10 ceil(3 e / 10), 3 580), both on exact Fractions; `NOISE_MODELS` | 4, 6, 10.4, 11.2 |
| `plan.py` | limits without any rehearsal ratio; Q and N split by the rule of M (Q.1, N1.1, …); the closed map of stage names; the closed list of safeguard (ii) (no `MEASURED.json`, no extractions; `REPORT.md`); BEFORE_M.md of 10.8; the rehearsal's run lists (`rehearsal_runs`); campaign ids without dots, rehearsal ids apart; the frozen list | 10.4–10.8, 11.2 |
| `run4.py` | the seed guard of 10.6 (the nominal cell refused in a campaign stage), the noise-model guard, the refusal of an optimised interpreter (every guard is an assert) | 6, 10.6 |
| `predicted.py` | the exact guarded fit (`drafts/prerun/predicted5.patch`); the control instance when none is eligible; the rehearsal's limits as a flag; refreeze after the chain test of RC (11.3): the nominal cell has round 1 only and can be its own control | 4.2, B3, 6, 11.3 |
| `cases.py` | the cases of 7.4 (asymmetric P0, the controls), from the pre-run's `cases5.py`; `build()` still returns the list | 7.4 |
| `analyze.py` | dates of the run and H's arithmetic exact; no limits basis; a rehearsal flag | 4.2 (rule 1), 9 |
| `rehearsal.py` | rewritten: the registered kind on two machines, subcommands, every check appended as it is done | 11 |
| `collect.py` | new: campaign 4's `collect_with_links.py`, unchanged but its docstring | 10.7 |
| `test_campaign.py` | rewritten for campaign 5's rules (30 tests, the nominal cell's predictions among them) | all |
| `check.sh`, `audit_cases.sh` | campaign 5's cases and reference files (`expected/`), `C5_CI_STRUCTURAL` | 7.3, 10.2 |
| `gate4.py`, `mirror_mutations.py`, `structural_compare.py` | docstrings only | — |
| `m8_case.py` | new for campaign 5: M8's eligible path with the nominal smoke run (`smoke/`) | 8 (M8) |
| `expected/` | new: the reference files of `check.sh`, written by the frozen code under the pinned toolchain; the cases' log equal to the pre-run's | 7.4 |
| `smoke/` | new: the record of the nominal smoke run of M8's eligible path; its waveform on `evidence/learned-dnf-circuit-campaign-5-smoke` | 8 |
| `PREDICTION.md` | byte-identical to `a2d8bad` | — |
| unchanged | `noisemodel.py`, `session4.py`, `plans4.py`, `reads4.py`, `noise/*`, `audit-cases/*` | the device-model code is kept and refused at the runner (choice 7) |
| left out | campaign 4's `PREDICTION.md`, amendments, `WIP.md`, `drafts/`, `rehearsal/`, `complete_rehearsal.*`, `restore_attempt.py`, `m8_case.py` | campaign-4-only |

The Lean namespace of the generated files stays `LearnedCoincidence.MonotoneDNF.PremiseCheck.Campaign4`, and the module
names `c4.py`, `run4.py`, `gate4.py`, `plans4.py`, `reads4.py`, `session4.py` stay: renaming them would change no rule
and every file that imports them.

## The float audit, by rule 1 (the coordinator's answer to report 6)

A measure is what the frozen instrument gives. The instrument is `research/network-circuit/measure.py` and `reads4.py`:
the code that turns a run's waveform into reads, run deterministically on the evidence (`trace.raw`, `result.json`),
wherever it runs (the runner writes the waveform, not the reads: the reads are made by the prediction and the analysis).
Everything computed from the instrument's values is exact. This line was confirmed by the coordinator's review of the
freeze at `6832af3`, and is written into the rehearsal's record (`rehearsal.NOTES`).

| Value | Where | Side |
|---|---|---|
| `q_peak` = max((1.25 − v)/0.5 + 0.1) | `reads4.py:30` | instrument: a measure, taken at its exact binary value by `zint` (`predicted.py:136`; `analyze.py` `score`) |
| latency = (fire − start)/TU, and the slot latencies | `reads4.py:52`, `reads4.py:55` | instrument: a measure, taken exactly by `q` (`predicted.py:139`, `:141`) |
| `move_mV` = (before − after)·1e3 | `reads4.py:60` | instrument: a measure, taken exactly by `exact` (`predicted.py:147`), then the doses, sensitivities and budgets exact |
| FIRE bits, write counts, decision windows, `skew_units` | `reads4.py` | instrument |
| the guarded fit | `predicted.py:72` (`solve`), `:195` | arithmetic: exact (B3) |
| a run's dates in units | `analyze.py` `units` | arithmetic: exact |
| H: separations, routes, skews against their bounds | `analyze.py` `h_check` | arithmetic: exact, campaign 4's tolerances kept as exact constants |
| limits, ceil10 | `c4.py` | arithmetic: exact |
| the expected compute and the sizing | `plan.py` (`expected`, `machine_expected`) | floats of `dnf.cost`; it decides `I` with a margin of 11.1 s against errors of about 1e-11 s, and CI checks I = 12 and 28 788.89 s (10.5) |
| M3, M7, M8's latency comparison (`assumption_on_c`) | `analyze.py` | reported floats, no integer |
| the geometric fit and M5 | `predicted.py` | floats, decide nothing (4.2) |

## The procedure of a stage (PREDICTION.md, 10 and 11), as ruled by the coordinator on 2026-11-18

On the branch `research/learned-dnf-circuit-campaign-5-rehearsal` (then the campaign branch), built from the frozen
commit plus only files of the closed list. `PY` = `/home/user/owner-prep/venv312/bin/python`, `KIT` = the launch kit.

The kit's rule that orders everything: at launch (and at any `resume-machine`), `published_marker` fetches the remote
branch head and `runtime_unchanged` (launch.py:225) refuses unless that head differs from the manifest's
`source_commit` only by that manifest, its marker and the two inventories. Hence:

- Two stages never share a source commit. The source commit of a stage is the previous stage's marker commit, or the
  last commit pushed before its manifest (a stage file, a run list, the development `PREDICTED.json`); CI must be
  green on that exact commit. A CI run on a marker commit runs while that stage runs.
- While a stage runs, nothing is pushed to the branch. A stage's manifest and marker are pushed only after the
  previous stage has ended on both machines.
- On the branch go only stage files, run lists, manifests, markers, inventories and the development `PREDICTED.json`.
  Every stage's evidence and the checks file go to `evidence/*` branches, one per stage and machine. The record
  (`REHEARSAL.json`) and copies of the small evidence come onto the branch only after the last rehearsal stage has
  ended on both machines. The campaign branch follows the same pattern (M1, M2, Q, N, ...).
- Each stage's go names its marker commit; each machine checks that its fetched head equals it before preflight.

Per stage S, on each machine m:

1. Once, just before the first manifests: `launch.py identity`; `launch.py inventory --machine m`, committed as
   `INVENTORY_<m>.json` (one per machine and branch; on the campaign branch, M1's new inventories are compared with the
   last rehearsal inventory).
2. Machine a: `rehearsal.py runs` / `plan.py runs` (in the source commit); `plan.py manifest NAME STAGE_COMMIT
   SOURCE_COMMIT 373cb3d OUT`; `launch.py preflight`, `prepare`; the manifest and marker pushed; the marker commit sent.
3. On the go: `uptime -s`; fetch by name and check head = marker commit; 4.0: `launch.py inventory` to
   `INVENTORY_BEFORE_<S>_<m>.json` (not committed), equal field by field to the committed inventory except
   `boot_utc` and `recorded_utc`, or no launch (10.1); `preflight`; then `rehearsal.py memory`, `launch.py
   run-machine` and the uptime recorder, each detached (`setsid nohup`); the session waits in the foreground (loops
   of at most 9 minutes) and stays active through every wait, CI waits included.
4. `collect.py` once into a new folder; the evidence (with `INVENTORY_BEFORE_<S>_<m>.json`, the memory samples and
   the uptime log) pushed to `evidence/learned-dnf-circuit-campaign-5-rehearsal-<S>-<m>` (files over 100 MiB in
   parts with `PARTS.json`).
5. Machine a: the checks of 11.5 (`rehearsal.py check`), appended at once to the checks file on its evidence branch.
   The 0.75 rule judges RM, RQ, RN and RMEM; for RC it records the wall times only. After RM, `rehearsal.py predict`
   (the development `PREDICTED.json`, pushed alone before RQ's manifest).
6. RG: `rehearsal.py guard` on each machine. At the end: `rehearsal.py record`; the commit that pushes
   `REHEARSAL.json` names the governing commit fb002cf of STAGE_RC.md and STAGE_RM.md (byte-identical to a2d8bad,
   accepted by the coordinator), as REPORT.md will.
