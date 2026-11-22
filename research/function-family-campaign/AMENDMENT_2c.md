# Family campaign (a): amendment 2c, the exact command of the one analysis

This amendment fixes how section 9's one analysis is run. It changes no rule of `PREDICTION.md` or of amendments 1,
2a and 2. **No frozen file changes**; it names the frozen entry and its inputs. It is pushed alone on
`research/function-family-campaign`, before stage D. Decided by the owner, 2026-11-22.

## Why

The frozen entry is `impl/analysis.py`'s command line (FREEZE.txt, `920413ec`):

    analysis.py PREDICTED.json RUNS.json REPO GEN RUNS_PARENT [--no-lean]

- It regenerates the prediction record from the measure evidence (`campaign_predict.campaign`, which first sets the
  generator's paths), compares it byte for byte, and runs the claims and the comparisons, M8 through the kernel.
- It takes `RUNS.json`, the network-code reader's records, as an input. No frozen command writes that file, and the
  layout of `RUNS_PARENT` is not written down.
- With `--no-lean`, the regenerated record has no kernel verdict, so it cannot equal the pushed one, and every claim
  would read "not established".

## 1. The layout

**Each machine Mn keeps one folder, `$O/campaign-runs/Mn/`, holding:**
- the run folders of its measure runs and of its network runs, side by side, each named by its run id;
- one `STATE.json` per stage: `D/`, `S/`, `O/`, `Q/`, `N1/`, `N2/` and `N3/`;
- on M5, `DUP/` as well.

Each machine pushes this folder to its own evidence branch, `evidence/function-family-campaign-Mn` (section 7), with
the parts split, and with `SHA256SUMS` and `PARTS.txt`.

**On the analysing machine**, `RUNS_PARENT` is one folder holding `M1/` to `M6/`:
- each branch is fetched by name at the SHA the coordinator has verified;
- its parts are joined, and every file is checked against its `SHA256SUMS`;
- a branch with any mismatch is reported, and its instances are not used (section 7).

## 2. RUNS.json

`RUNS.json` is the union over the six machines of `family_reads.collect` on that machine's folder. It covers the
network runs of the record (`PREDICTED.json`'s `network_runs`, each read on its own `machine`), with rows and the
run's observation:

```
cd $W/ffnet/research/function-family-campaign/net
$PY -B -c "
import json; from pathlib import Path
import family_net as N; N.paths('$W/campaign-6-impl')
import family_reads as R
P = Path('$A/PREDICTED.json'); rec = json.loads(P.read_text())
runs = {}
for m in ('M1', 'M2', 'M3', 'M4', 'M5', 'M6'):
    ids = [r['id'] for r in rec['network_runs'] if r['machine'] == m]
    runs.update(R.collect(ids, Path('$A/RUNS_PARENT') / m, with_rows=True, predicted=P))
assert sorted(runs) == sorted(r['id'] for r in rec['network_runs'])
Path('$A/RUNS.json').write_text(json.dumps(runs, sort_keys=True) + '\n')"
```

`$A` is the analysis folder. `PREDICTED.json` is the record pushed before stage Q, checked against its pushed
SHA-256. A run absent from its machine's `STATE.json` files is read as missing (`family_reads.collect`), never
replaced.

## 3. The analysis

```
cd $W/ffimpl/research/function-family-campaign/impl
LEAN=<the verified bin/lean> $PY -B analysis.py $A/PREDICTED.json $A/RUNS.json $W/campaign-6-impl $W/learned-dnf-generator $A/RUNS_PARENT > $A/RESULTS.json
```

- **Never `--no-lean`.**
- Before the analysis, Lean on the analysing machine is checked:
  - its archive `lean-4.35.0-linux.tar.zst` against SHA-256
    `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`;
  - its `bin/lean` against `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`;
  - and it must report version 4.35.0.
- The generator path is given exactly as `$W/learned-dnf-generator` (`4fca6256`), the string written into the
  record.
- The worktrees are those named in `FREEZE.txt`, each checked against it.
- `RESULTS.json`, `RUNS.json` and their SHA-256 are pushed in a commit of their own on
  `evidence/function-family-campaign-analysis`, under the owner's identity.

## 4. Which machine analyses

The analysing machine must meet three conditions:
- it is a machine with a verified Lean 4.35.0;
- its free space, measured just before the analysis, is at least 2.2 times the total size of the files of the six
  campaign evidence branches, as listed in their `SHA256SUMS`;
- it has rerun none of the campaign's runs by hand.

If no running machine meets these conditions, a fresh session is set up as in `MACHINE_PLAN.md` section 3 and
checked by `envcheck.py`.

It is named by the coordinator when the last network stage has ended, with the owner's go. It runs the analysis
once (section 9).

## Not checked

- The factor 2.2: it allows for the joined files plus their extraction, and is not measured on a campaign folder.
- `family_reads.collect` on a real folder holding both measure and network `STATE.json` files. It was tested on a
  synthetic one, with measure states in `D/` and `S/` and a network state in `Q/`:
  - the network run was read and counted;
  - a network id absent from every state was read as missing.
