# Family campaign (a): amendment 2b, the measured noise sensitivity values

This amendment fixes `b`, `w` and `d` as amendment 2 section 3 asks, from the rehearsal's noisy F2 runs. It makes no
new prediction. It changes no rule of `PREDICTION.md` or of amendments 1, 2a, 2 and 2c, and **no frozen file
changes**. It is pushed alone on `research/function-family-campaign`, before stage N1. Decided by the owner,
2026-11-22.

## 1. The values

The values were computed by `FREEZE_NOISE.txt` section 2 (`research/function-family-campaign-noise-freeze` at `7ad98b14`),
with the code `research/function-family-campaign/noise/noise_constants.py` (`a704b890…`, branch `7bc064e8`), run on M6
by `values_step.sh` (SHA-256 `2b54656a0a264fd2af1d3a52eda55ce1eb60ba224767cd72265ae348aa664c4a`).

| | campaign 3's definition | measured, pooled over 8303-F2 and 8306-F2 | decision 5 |
|---|---|---|---|
| `b`, between runs | `pooled.between_mV` | 0.110 mV | 0.111 mV |
| `w`, within a run | `pooled.within_mV` | 0.0818 mV | 0.094 mV |
| `d`, per dose | `pooled.per_dose_mV` | 0.00820 mV | 0.009 mV |

Full values: `between_mV` 0.10954728969073162, `within_mV` 0.0817991307837689, `per_dose_mV` 0.00820248107210645,
from 48 run offsets, 108 within-run counts and 108 doses.

- `NOISE_VALUES.json`, SHA-256 `65145fa3fbefa31cef34da82ccd24408a872bb582385151aa54d7973d2b4380b`, on
  `evidence/function-family-campaign-noise-values` at commit `cf58f9c3dbe7fd0f234dbe60ac67f265c0062ec9`, with its log and the
  SHA-256 of the record it read (`PREDICTED.json`, `c02057d3…`).
- Runs read:
  - 8303-F2: without noise 8303-F2-quiet; noisy 8303-F2-r1 to r4;
  - 8306-F2: without noise 8306-F2-quiet (amendment 2 section 2); noisy 8306-F2-r1 to r4.
- Runs not counted by campaign 3's rule, as `NOISE_VALUES.json` lists them: none, on either instance.
- Every input was fetched by name at the SHAs that `values_step.sh` pins, and checked against its own `SHA256SUMS`,
  `PARTS.txt`, `PARTS.json` or `COLLECTED.json` before use.

## 2. One deviation from FREEZE_NOISE.txt section 2

Section 2's command, `$PY -B noise_constants.py PREDICTED.json RUNS DECKS -- …`, cannot run as written:
- `noise_constants.main` reads the runs through `family_reads.record_of`, which imports the frozen modules `predicted`,
  `measure` and `reads4`;
- those import only after `family_net.paths(REPO)`, and `noise_constants.py` never calls it (`family_reads` calls it
  only in its own command line).

`values_step.sh` therefore called the same `noise_constants.main` with section 2's exact arguments through
`$PY -B -c`. That call first runs `family_net.paths('$W/campaign-6-impl')`, keeps the `assert __debug__` guard, and
prints the result as the file's `__main__` does. Neither the code nor the arguments changed, and no frozen file was
edited. Before the run, the coordinator checked this against the frozen code on GitHub at `7bc064e8`.

## 3. Where b, w and d are used, and where they are not

**They are used in one place only:** section 7's declared comparison after comparison M8, which counts nothing
(`PREDICTION.md` section 7 [FD §0.6, §8.3]). For each counted instance it reports whether the instance keeps room at
K = 3 with the larger of each pair (decision 5's value and the measured one).
- The frozen code is `impl/campaign_predict.py`'s `noise_sensitivity(record, regenerate, measured)` (FREEZE.txt, `920413ec`).
  `measured` is `{between_mV: 0.10954728969073162, within_mV: 0.0817991307837689, per_dose_mV: 0.00820248107210645}`.
- All three measured values are below decision 5's, so the larger of each pair is decision 5's own value, and the
  comparison reruns the gates with exactly the record's constants.
- No frozen command line calls it, and `analysis.py` (amendment 2c section 3) does not. It is run once, on the
  analysing machine, after the analysis. Its exact command is given in section 4.

**They are not used anywhere else** [K, from the frozen code]:
- **The network runs (N1, N2, N3).** `family_net.py run` reads neither decision 5's constants nor `b`, `w` and `d`.
  Its noisy runs use the injected model (campaign 5's `noisemodel.shim`), with the noise seed the record gives.
  Stages N1 to N3 run exactly as their stage files say (`predicted/stages/`, `d7e4fcc2`).
- **The prediction record.** `PREDICTED.json` (`2849a614…`) stays as pushed. Its budgets and `room_K3` were computed
  with decision 5's constants (`c4.DECISION5`, `between_mV 0.111, within_mV 0.094, per_dose_mV 0.009`), which the
  record also holds under `constants`.
- **The verdicts and the other comparisons.** They are taken under decision 5's constants (`PREDICTION.md` section 6).
  This includes M7's model sigma, which reads the record's `constants`.

## 4. The declared comparison's command

After amendment 2c section 3's analysis, on the same machine, with the same `$A`, worktrees, `LEAN` and PYTHONPATH:

```
cd $W/ffimpl/research/function-family-campaign/impl
LEAN=<the verified bin/lean> $PY -B -c "
import json, os, sys
from pathlib import Path
assert __debug__, 'refused: not with python -O, the guards are asserts'
import family_net as N; N.paths('$W/campaign-6-impl')
import campaign_predict as CP
rec = json.loads(Path('$A/PREDICTED.json').read_text())
nv = json.loads(Path('$A/NOISE_VALUES.json').read_text())['pooled']
measured = {k: nv[k] for k in ('between_mV', 'within_mV', 'per_dose_mV')}
regen = lambda: CP.campaign('$W/campaign-6-impl', '$W/learned-dnf-generator', '$A/RUNS_PARENT', '$A/sensitivity', True, os.environ['LEAN'])
print(json.dumps(CP.noise_sensitivity(rec, regen, measured), indent=1, default=str))" > $A/NOISE_SENSITIVITY.json
```

- The command calls `family_net.paths` first. `noise_sensitivity` runs `import c4` before it calls `regenerate()`,
  and `c4` (campaign 5's folder) imports only once the frozen modules' folders are set; importing `campaign_predict`
  does not set them. Without this line the command stops with "No module named 'c4'" (checked on M1, see Not checked).
- It reruns the 15 kernel gates under the larger constants, with the same Lean (the verified 4.35.0 `bin/lean`).
  It counts nothing, whatever it shows: no claim, verdict or comparison changes with its result.
- `$A/NOISE_VALUES.json` is fetched by name at `cf58f9c3dbe7fd0f234dbe60ac67f265c0062ec9` and checked against `65145fa3fbefa31cef34da82ccd24408a872bb582385151aa54d7973d2b4380b`.
- `$A/sensitivity` must not exist before the command.

- The output and its SHA-256 go with `RESULTS.json` on `evidence/function-family-campaign-analysis`.

## Not checked

- Whether every port's trained level falls inside its deck's fired range. Where it does not, the secant
  takes the two nearest points, as in campaign 3 (`FREEZE_NOISE.txt`, "Not checked").
- Section 4's command on real campaign evidence. On M1 its plumbing was run with a stub `regenerate` that returns the
  pushed record (`2849a614…`) and `measured` set to decision 5's values, with no Lean and no simulation:
  - without the `family_net.paths` line it fails at `import c4`;
  - with it, the command imports and returns `per_instance` with 15 entries (so did a variant with one null
    replaced by decision 5's value; no null occurred).
  The real `regenerate` (`CP.campaign` with Lean) was not run.
- `CP.campaign`'s argument order in section 4's command is taken from `analysis.main` (`920413ec`), which calls it
  the same way. It has not been run here.
