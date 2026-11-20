# Preparing a campaign 7 of the learned AND-OR circuit: development work

**This folder is development work. It is exploratory, it was not preregistered, and nothing in it is a claim.**

- It follows the development work of
  [`../learned-dnf-circuit-campaign-6-followup/`](../learned-dnf-circuit-campaign-6-followup/README.md), whose code it
  imports.
- **No campaign 7 exists.** There is no preregistration, no frozen code and no campaign seed has been simulated.
  The protocol here is a **draft**.
- **The batch of measures here is a development batch.** Its ten instances (seeds 8301 to 8310) are development
  instances. It ran no network and no noisy run, and it counts nothing for any campaign.
- Simulation only, one simulator, one noise model. There is no chip.

Each note says what it did not check, and marks what is known and what is inferred.

## What is here

| File | What it is | SHA-256 |
|---|---|---|
| [`CAMPAIGN7_DESIGN.md`](CAMPAIGN7_DESIGN.md) | A design note written before the batch: what changing only cell c's testing error (one port instead of two) would give at the unchanged dose, on campaign 6's own development batch | `db6fd415add51f83973f7b94034b8f129684da1f9d01756085dfda7e7a71e1ba` |
| [`BATCH2X_PLAN.md`](BATCH2X_PLAN.md) | The plan of the development batch at twice the dose: the question, the prediction written before any data, the runs, and the sizing rule the owner chose before the first run of an instance (section 8) | `573270f903562f58c65ff2fd5ef03cb0c33ce7cec03a5b91818a93be6fd670fc` |
| [`CAMPAIGN7_PROTOCOL_DRAFT.md`](CAMPAIGN7_PROTOCOL_DRAFT.md) | **A draft** of a protocol for a campaign 7, in the structure of campaign 6's preregistration, with the open choices listed for the owner. Not reviewed, not preregistered | `1dfd89e2fe9f4cf566f7e602181f201cf999896289e96ced508815c8ded6fb45` |
| [`dev/batch2x.py`](dev/batch2x.py), [`dev/test_batch2x.py`](dev/test_batch2x.py) | The batch's runs (two calibration decks, four scans, the both-lines check and two one-sided sets per instance, in three waves) and the smoke on the nominal cell; its 15 tests (no simulation) | `fc495acb…2868`, `adead8af…afdd` |
| [`dev/batch2x_report.py`](dev/batch2x_report.py), [`dev/test_batch2x_report.py`](dev/test_batch2x_report.py) | What the batch says, instance by instance, under campaign 6's frozen rule and under the one-port rule; its 4 tests (no simulation) | `b6c3ee6a…3b71`, `40662542…a054` |
| [`dev/batch2x/report/BATCH2X_REPORT.json`](dev/batch2x/report/BATCH2X_REPORT.json) | The batch's report: per instance, its needs, eligibility, room, and each crossing's place in its step; the two counts; each run's wall time | `d29bdf1c45e67afec1ff2231115995338c01b62054f7cac97bb314d8d35c72e1` |
| [`dev/batch2x/report/`](dev/batch2x/report/COMPILED.txt) | The 20 gate files of the batch (10 instances, each rule), written by the frozen generator, and the record of their compile | listed in `dev/SHA256SUMS_C7PREP` |
| `dev/batch2x/runs/`, `dev/batch2x/smoke/` | The record of each of the 90 runs of the batch and of the 4 runs of the smoke, the lists of runs as they were started, the doses and bounds each wave computed, and each wave's state | listed in `dev/SHA256SUMS_C7PREP` |
| [`dev/batch2x/RUNS_SHA256SUMS`](dev/batch2x/RUNS_SHA256SUMS), [`dev/batch2x/SMOKE_SHA256SUMS`](dev/batch2x/SMOKE_SHA256SUMS) | Every file of the batch's run folders (750 files) and of the smoke's (39 files) as the runs wrote them, hashed before the report ran | `2d6ab79a…dd77`, `92172edd…b2b1` |
| [`dev/c7_share.py`](dev/c7_share.py), [`dev/c7_rescale.py`](dev/c7_rescale.py), [`dev/c7_E.py`](dev/c7_E.py) | The design note's computations: the one-port rule on campaign 6's batch; that batch's crossings rescaled to twice the dose (an estimate); the expected compute of a campaign by campaign 6's function | `2c65ca47…e53d`, `4ac59326…affc`, `2425d877…2a37` |
| [`dev/c7/`](dev/c7/C7_SHARE.json) | Their outputs, and the 14 gate files of campaign 6's batch under each rule with the record of their compile | listed in `dev/SHA256SUMS_C7PREP` |

## What the batch found, in short

Read [`BATCH2X_PLAN.md`](BATCH2X_PLAN.md) for the question and
[`dev/batch2x/report/BATCH2X_REPORT.json`](dev/batch2x/report/BATCH2X_REPORT.json) for the figures. There is no
written report of the batch yet; this summary is not one.

- **The design measured**: twice the dose (`vhi = 0.7`), the solver's tolerance `reltol = 1e-5`, and cell c's testing
  error taken as the one-port budget, with the noise constants of campaign 3's decision 5.
- **90 runs of 90 completed.** Before them, a smoke on the nominal cell (4 runs).
- **All ten instances are eligible without noise** (`k_elig = 10`), under either rule.
- **On two instances of ten, cells a, b and c all have room under the noise budget** (`k_all3 = 2`: 8303 and 8306),
  under the one-port rule. Under campaign 6's frozen two-port rule, on one (8306).
- The prediction written before any data was "about 2 of 10", with the caution that anything from 0 to 5 would not
  be a surprise. One batch of ten does not show that the reasoning behind it is right.
- "Room under the noise budget" is the budget's prediction. **No noisy run was made**, so nothing here was observed
  under noise.
- By the sizing rule written before the batch, `k_all3 = 2` gives 15 instances for a campaign on this design. That
  is a size, not a decision to run one. Campaign 6's own compute bound would refuse 15 instances; the draft says so.

## How the files were made

- **The code** imports the development code of the follow-up folder (`dosedev.py`, `dosedev2.py`, `dosedev_tol.py`,
  `t1_gate.py`) and campaign 6's frozen code, and edits neither. To run a test from this branch, put the follow-up's
  `dev/` folder on `PYTHONPATH` and give as `REPO` a checkout that holds campaign 6's batch code (the branch
  `research/learned-dnf-circuit-campaign-6-impl` at `ecfcd1c1`), for example:
  `PYTHONPATH=../../learned-dnf-circuit-campaign-6-followup/dev python -B test_batch2x.py REPO`.
- For the time of a call, `batch2x.py` replaces two things of the frozen code and puts them back: the deck's text
  (two parameters rewritten) and campaign 6's seed guard (which accepts only its own batch's seeds). The plan's
  section 6 says so and names the tests.
- **Twelve files differ from the ones that were written**, in the paths they hold: the lists of runs
  (`JOBS_*.json`), each wave's `STATE.json`, and the two `compile_gates.sh`. The folder of the development files is
  written `dev` and the checkout of this repository `REPO`. `dev/SHA256SUMS_C7PREP` lists the 283 files as they are
  here; `dev/SHA256SUMS_C7PREP_as_computed` lists them as written. The three notes and
  every other file are as written.
- The records still name the Python, the simulator and the device library of the machine that ran them, and the two
  shell scripts name the folder where the pinned Lean was installed. They are kept as a record of what was run.
- The gate files were compiled with Lean 4.35.0, installed from the archive this repository's CI pins, by
  `compile_gates.sh`: the theory with the commands of campaign 5's `check.sh`, then each gate file. This is not
  `check.sh`: no audit of axioms.

## What is not on this branch

- **The waveforms, decks and logs of the 94 runs**, about 6.6 GB. Their SHA-256 are in `RUNS_SHA256SUMS` and
  `SMOKE_SHA256SUMS`. They are meant for the evidence branch `evidence/learned-dnf-circuit-campaign-7-prep`. The
  batch's report reads the calibration decks' waveforms, so it cannot be recomputed from this branch alone.
- A written report of the batch.
- Any code of a campaign 7.
