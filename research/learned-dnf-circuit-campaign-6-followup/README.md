# After campaign 6: development work on the learned AND-OR circuit

**This folder is development work. It is exploratory, it was not preregistered, and nothing in it is a claim.**

- It follows [campaign 6](../learned-dnf-circuit-campaign-6/REPORT.md), which predicted and then observed a network
  of three simulated cells learning `(A and B) or (C and D)`.
- **The noise audit uses the pushed runs of campaign 6's attempt c1 as development data, with the owner's
  permission. It recounts no claim of campaign 6** and does not say what campaign 6 would have counted under another
  rule.
- **Every result here is on the nominal cell or on development records**, unless the text says otherwise.
- Simulation only, one simulator, one noise model. There is no chip.

Each note says what it did not check, and marks what is known, what is inferred and what is a guess. Each note's
"Status" line describes the day it was written: where it says that nothing was pushed, that was true then.

## What is here

| File | What it is | SHA-256 |
|---|---|---|
| [`DESIGN_NOTE_WIDEN.md`](DESIGN_NOTE_WIDEN.md) | A written study, second version. What it would take to predict and certify other learned functions; why cell c had no room under noise in campaign 6; half a page on a second simulator or a chip | `bbe48105524a7ee8e8601ec87f61d32320b39f93268caf41d43534ba9462e003` |
| [`NOISE_AUDIT.md`](NOISE_AUDIT.md) | The noise actually seen in campaign 6's twelve noisy runs, against the budget's constants. Fourth version: the third, with two sentences of section 8 changed for publication | `5b24a860f0e9d6bd41681c1f694130811d4bf4354bca7999d6a35f00259e4676` |
| [`DOSE_PLAN.md`](DOSE_PLAN.md) | A plan to test a larger dose on the nominal cell, with what would say "go" or "stop" | `6cfdc8181278cf0d860b4d89f5a84084058dd45ec75ea34398588a986d3641a0` |
| [`dev/noise_audit.py`](dev/noise_audit.py) | The audit's script | `abebb63633323e823bc7bdaf28542cd5f08e2eaae2ae84671b8006da3733bb87` |
| [`out/`](out/SHA256SUMS) | The audit's output files: every table of the note comes from them. 29 files, listed with their SHA-256 in `out/SHA256SUMS` (see below) | `SHA256SUMS` `1cb22f20…eb5b` |
| [`dev/dosedev.py`](dev/dosedev.py) | Runs the nominal cell's guard-on calibration deck with the dose parameters of the cell rewritten | `18759e835bc54041300805ca3d5e57f3bce6f0e3ff12c3fab34349cc004601ed` |
| [`dev/test_dosedev.py`](dev/test_dosedev.py) | Its tests. No simulation | `2f051c8b35cda8eed9915d7ce881140bb808ed68cef7e85ba16ec329047d24ff` |
| [`smokes/none-1x-cal-on/`](smokes/none-1x-cal-on/record.json) | The calibration deck at the unchanged dose: the run's record and its doses | `record.json` `b049cd09…f5ab`, `DOSES.json` `3fb64b46…4eee` |
| [`smokes/none-2x-cal-on/`](smokes/none-2x-cal-on/record.json) | The same deck at twice the dose (`vhi = 0.7`) | `record.json` `793423f0…b8fb`, `DOSES.json` `ce3d32a5…4d37` |
| [`DOSE_REPORT.md`](DOSE_REPORT.md) | The dose experiment on the nominal cell, steps A to D of the plan: what was run, the plan's seven tests, the noise at each dose, and five analyses made after the verdict | `6a2468b57ad562f06f3a891d1884fac2ce1cbc0d46f1d3987c4dd720d83923b8` |
| [`dev/dosedev2.py`](dev/dosedev2.py), [`dev/test_dosedev2.py`](dev/test_dosedev2.py) | The wrapper for scans and network runs at a changed window, and its 13 tests (no simulation) | `b0999ebe…ce58`, `fd39b404…1686` |
| [`dev/step_b.py`](dev/step_b.py) | The list of step B's runs (the 2x measures) | `0356028c…3be5` |
| [`dev/NOISE_SEEDS_DEV.txt`](dev/NOISE_SEEDS_DEV.txt) | The 16 development noise seeds, declared before any noisy run | `b33b281d…2967` |
| [`dev/g4.py`](dev/g4.py), [`dev/g5.py`](dev/g5.py), [`dev/g6.py`](dev/g6.py) | The readers of the plan's tests G4, G5 and G6. `g6.py` was fixed before the noisy runs | `772475d1…6752`, `6d144868…6a74a`, `bd0a38b0…67cb` |
| [`dev/post_d.py`](dev/post_d.py), [`dev/post_d_a5.py`](dev/post_d_a5.py) | The analyses made after the verdict (sections 5.1 to 5.5 of the report) | `dc38aadf…477a`, `fece0fac…f25f` |
| [`dev/analysis/`](dev/SHA256SUMS_DOSE) | The readers' outputs: every figure of the report comes from them | listed in `dev/SHA256SUMS_DOSE` |
| `dev/runs2x/`, `dev/runsC/`, `dev/runsD/` | The record of each of the 31 runs of steps B to D, and the lists of runs as they were started | listed in `dev/SHA256SUMS_DOSE` |

## The results so far, in a few lines

- **Design note.** The Lean theory already covers any monotone function; the code that writes each instance's
  Lean file covers one shape only. Cell c had no room under noise for a structural reason: its budgets take 98 to
  99.7 % of one training step.
- **Noise audit.** The noise seen is about 0.19 to 0.25 of a step at three sigma, against 0.33 in the budget. Two
  instruments disagree on how it splits between the constants, and the note says which evidence sides with which.
- **Two calibration decks on the nominal cell.** At the unchanged dose, the doses equal those of campaign 6's
  rehearsal, string for string. At twice the dose, the dose is 2.0065 times larger and as constant as before, the
  write keeps 0.6 time unit of margin after the latest FIRE, and each need falls from 4 to 2. A calibration deck
  cannot show a read that both fires and writes; that check needs a network run.

- **The dose experiment.** At twice the dose the measures are clean and the network learns, without noise and in 8
  noisy runs of 8. The plan's test of the noise says "unclear": by campaign 3's definition the scatter within a run
  is 47 % larger in mV at twice the dose; counted in steps the noise is smaller by every reading. Under campaign 6's
  frozen budget, cell c has no room on the nominal cell at either dose. The report says what was computed after
  the verdict, and labels it so.

None of this is established. It says where to look next.

## How to run the code

The scripts read the frozen code of campaign 6 and edit none of it. `REPO` below is a checkout of the branch
`research/learned-dnf-circuit-campaign-6-impl` at `ecfcd1c1`; `main` does not hold that code. They need the pinned
environment of campaign 6: Python 3.12.3, numpy 2.3.5, ngspice 42 and the device library at commit `1232782c`.

```sh
python -B dev/test_dosedev.py REPO
```

```sh
python -B dev/dosedev.py cal REPO OUT /usr/bin/ngspice PDK
```

```sh
python -B dev/dosedev.py cal REPO OUT /usr/bin/ngspice PDK vhi=0.7
```

`OUT` is a new folder outside any checkout. The first line runs the seven tests and no simulation. The second runs
the deck of `smokes/none-1x-cal-on` (about 510 s), the third that of `smokes/none-2x-cal-on` (about 540 s).

The audit's commands are in section 8 of `NOISE_AUDIT.md`. They read the evidence branches of campaign 6's attempt
c1, fetched by name and checked against their own lists of hashes; they run no simulation.

## The audit's output files

`out/` holds what `dev/noise_audit.py` wrote: the integrity reports (`VERIFY.json`, `VERIFY_M1.json`), the reads of
each of the 17 runs (`RUNS.json`, `reads/`), the differences read by read (`PER_READ.json`), every table of the note
(`AUDIT.json`, `CONSTANTS_AS_CAMPAIGN_3.json`, `M5_AS_CAMPAIGN_3.json`, `WINDOWS_BATCH.json`) and what the script
printed.

**Eighteen of the 29 files differ from the ones the note lists**, in one field each: `RUNS.json` and the 17 files
of `reads/` recorded the folder of each run as a full path on the machine that computed the audit. Here that path is
written from the audit's folder (`ev/Q/a/7802-quiet`). Nothing else differs: each published file, with the prefix
put back, is the local file byte for byte.

- `out/SHA256SUMS` lists the 29 files as they are on this branch.
- `out/SHA256SUMS_as_in_the_note` is the list that section 8 of `NOISE_AUDIT.md` cites (`f98536ef…64ee`). The other
  11 files have the same SHA-256 in both lists; the note's SHA-256 of `RUNS.json` (`7ff35005…3b3f`) is that of the
  local file, and on this branch it is `967daed0…1ea7`.
- The script does not read that field after its `reads` step. Run again from the published `RUNS.json` and
  `reads/`, its `analyze` and `constants` steps give `AUDIT.json`, `PER_READ.json`, `CONSTANTS_AS_CAMPAIGN_3.json`
  and the printed output byte for byte.

## The dose experiment's files

`dev/` on this branch is the folder the experiment ran in: the scripts, the lists of runs (`JOBS_*.json`), the
readers' configurations and outputs (`analysis/`), and one folder per run with its `record.json`.

**Ten of the 95 files differ from the ones the experiment wrote**, in the paths they hold: the four `JOBS` files,
the four `STATE.json` and the two configurations recorded full paths on the machine that ran them. Here each path is
written from this folder: `dev/...` for the experiment's folder, `ev_r3/...` for the evidence of campaign 6's
rehearsal r3 (on its own evidence branches, not here), and `REPO` for the checkout of the frozen code. Nothing
else differs.

- `dev/SHA256SUMS_DOSE` lists the 95 files as they are on this branch.
- `dev/SHA256SUMS_DOSE_as_computed` lists them as the experiment wrote them. The report's SHA-256 of
  `JOBS_D.json` (`96a1fdf6…b8eb9`) is from that list; on this branch the file is `a17c991e…`. The other 85 files
  have the same SHA-256 in both lists.
- `dev/runs/none-1x-cal-on` and `dev/runs/none-2x-cal-on`, named in the two configurations, are the two decks
  published under `smokes/`.
- The records keep the path of the pinned interpreter and of the device library, as campaign 6's own records do.

To run the tests of the wrapper (no simulation):

```sh
python -B dev/test_dosedev2.py REPO
```

## What is not on this branch

- **The waveforms of the two decks**, about 63 MB each. Their SHA-256 are in each `record.json`. They are meant for
  an evidence branch, `evidence/learned-dnf-circuit-campaign-6-followup`.
- The evidence of campaign 6 that the audit read: it is on campaign 6's own evidence branches, named in section 2
  and section 5.4 of `NOISE_AUDIT.md`.
- **The waveforms and logs of the 31 runs of steps B to D**, about 2.4 GB. Their SHA-256 are in each
  `record.json`. They are meant for the evidence branch.
