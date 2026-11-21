# The function family: development work for step 1

**This folder is development work.** It is not preregistered and claims nothing. No campaign exists.

- **The design.** [`FAMILY_DESIGN.md`](FAMILY_DESIGN.md), sixth version. Its section 0 is step 1 as the owner decided
  it: the five two-layer monotone functions of 3 inputs, A, A∧B, A∨B, A∧(B∨C), A∨(B∧C). Campaign 6's function stays as
  the code's regression anchor.
- **The rules of the top-up, fixed before its data.** [`TOPUP_RULES.md`](TOPUP_RULES.md): the unary port of each
  cell, the size by member, the room instrument.
- **The three machines.** [`MACHINE_PLAN.md`](MACHINE_PLAN.md): the assignment, the duplicate, the environment check,
  the collection.

## Files

| Path | What |
|---|---|
| `dev/topup.py`, `dev/test_topup.py` | The top-up's runs: decks with port-1 and port-2 reads at 1.0 on a and b, four unary scans, two preset checks per instance; a worker for a list of instances; the duplicate and its comparison. 19 tests, no simulation (`dev/test_topup_output.txt`) |
| `dev/envcheck.py` | The environment check each machine runs first (`MACHINE_PLAN.md` 3). `dev/ENV_M1_check_dry.json` is its output on M1, before any top-up run |
| `dev/record_compare.py` | The numpy RECORD against the official wheel's, line by line |
| `dev/unary_smoke.py`, `dev/test_unary_smoke.py` | The smoke on 8303, run once on 2026-11-21 (18 tests) |
| `dev/fam/*.py` | The scripts of `FAMILY_DESIGN.md` sections 1 and 2: the enumeration, the tables, the rewirings, the tied sub-runs, the slot tables |
| `dev/plan_one_instance.txt` | `topup.py plan` for one instance |
| `smoke/` | The smoke's small outputs. Its run folders, 297 MB with the waveforms, are not here; `smoke/SMOKE_RUNS_SHA256SUMS` lists every file of them |

## How to run the code

```
PYTHONPATH=FUP/dev:PREP/dev:research/function-family/dev  /home/user/owner-prep/venv312-dev/bin/python -B dev/test_topup.py REPO
```

- REPO: a worktree of `research/learned-dnf-circuit-campaign-6-impl` at `ecfcd1c1`.
- FUP: a worktree of `research/learned-dnf-circuit-campaign-6-followup` at `56f9e83e`.
- PREP: a worktree of `research/learned-dnf-circuit-campaign-7-prep` at `b956efe4`.

The code imports the frozen code of campaigns 5 and 6 and the development code of the follow-up and the prep, and
edits none of it.
