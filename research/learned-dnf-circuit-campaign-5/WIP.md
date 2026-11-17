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
| `run4.py` | the seed guard of 10.6 and the noise-model guard | 6, 10.6 |
| `predicted.py` | the exact guarded fit (`drafts/prerun/predicted5.patch`); the control instance when none is eligible; the rehearsal's limits as a flag | 4.2, B3 |
| `cases.py` | the cases of 7.4 (asymmetric P0, the controls), from the pre-run's `cases5.py`; `build()` still returns the list | 7.4 |
| `analyze.py` | dates of the run and H's arithmetic exact; no limits basis; a rehearsal flag | 4.2 (rule 1), 9 |
| `rehearsal.py` | rewritten: the registered kind on two machines, subcommands, every check appended as it is done | 11 |
| `collect.py` | new: campaign 4's `collect_with_links.py`, unchanged but its docstring | 10.7 |
| `test_campaign.py` | rewritten for campaign 5's rules (27 tests) | all |
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
whenever it runs. Everything computed from the instrument's values is exact.

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

## The procedure of a rehearsal stage (PREDICTION.md, 11)

On the branch `research/learned-dnf-circuit-campaign-5-rehearsal`, built from the frozen commit plus only files of the
closed list. `PY` = `/home/user/owner-prep/venv312/bin/python`, `KIT` = the launch kit, from a clean clone at that branch.

1. Each machine: `uptime -s`; its inventory (`launch.py inventory`), committed as `INVENTORY_<m>.json`.
2. Machine a: `rehearsal.py runs NAME STAGE_NAME_RUNS.json [PREDICTED.json]`; `plan.py stage-file NAME` (pushed alone); then
   `plan.py manifest NAME STAGE_COMMIT SOURCE_COMMIT FROZEN_COMMIT CAMPAIGN_NAME.json`; `launch.py preflight` and `prepare`
   (the marker); push. CI must be green on the source commit.
3. Each machine, at once: `rehearsal.py memory` detached, then `launch.py run-machine` detached (`setsid nohup`), the
   uptime recorder; the session waits in the foreground (loops of at most 10 minutes) until the shard ends.
4. Each machine: `collect.py` once into a new folder, pushed (waveforms of 10 MB and more to an evidence branch).
5. Machine a: the checks of 11.5 for that stage (`rehearsal.py check`), appended at once; for RM, `rehearsal.py predict`
   (the development instances' `PREDICTED.json` and its gate, pushed alone before RQ's manifest).
6. RG: `rehearsal.py guard`, on each machine. At the end: `rehearsal.py record`.

No kit launch before 2026-11-18 03:00 UTC.
