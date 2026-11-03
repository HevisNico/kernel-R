# Numerical records: restore history or compute a fresh campaign

The four committed `evidence/validation.json` reports are historical records.
Their compressed traces are not in the checkout. A successful certificate replay
is separate from numerical record verification, which requires the exact trace,
source bytes and Python/NumPy/SciPy versions recorded in its report.

## Available historical traces

The [v0.1.0 robust asset](https://github.com/HevisNico/kernel-R/releases/download/v0.1.0/robust_n_cells_tested.zip)
contains the local and periodic traces. The [pinned manifest](../../tools/robust_recordings.json)
records the archive SHA-256, both trace SHA-256 identities and the source commit.
The restoration helper checks these identities and the historical reports before
publishing to a fresh directory; it never overwrites the committed evidence.

| Campaign | Cases | Historical trace in this asset |
|---|---:|---|
| Local prepared chains | 53 | Available and hash-matched |
| Periodic packets | 10 | Available and hash-matched |
| Birth | 39 | Not available |
| Latency | 12 | Not available |

The birth and latency historical reports remain readable, but their full
source/runtime/trace verification cannot be reproduced from this asset. A fresh
run creates new evidence; it is not a recovery of the missing historical bytes.
No replacement historical trace is claimed.

From the repository root, with the pinned numerical requirements installed:

```sh
git fetch origin 5be69a7a441506cfd8f69bc21f9d27af8ffba3e0
python -B tools/restore_robust_recordings.py --out audit_runs/robust-historical
# An existing download can instead be supplied with --archive /path/to/robust_n_cells_tested.zip.
cd research/robust
python -B validate.py --verify-record --out ../../audit_runs/robust-historical/local --source-ref 5be69a7a441506cfd8f69bc21f9d27af8ffba3e0
python -B periodic/validate.py --verify-record --out ../../audit_runs/robust-historical/periodic --source-ref 5be69a7a441506cfd8f69bc21f9d27af8ffba3e0
```

`--source-ref` checks the unchanged historical report and every recorded source
against that exact Git commit, rather than claiming that later validator edits
were used in the historical run. Runtime versions must still match. Fetching
the commit is only needed when it is absent from the local Git object database.

## Fresh campaigns

All four validators require an explicit, nonexistent `--out` directory.
Reports, compressed traces and their `MANIFEST.json` are staged together and
verified before the directory is published with a single rename. An exception
cleans the staging directory and writes a separate `*.FAILED-*.json` attempt
report beside the intended output. Earlier published directories remain intact.
An abrupt process termination can leave a hidden staging directory, which is
not a published campaign.

From `research/robust`, choose fresh directory names for every invocation:

```sh
python -B validate.py --out ../../audit_runs/robust-local
python -B birth/validate.py --out ../../audit_runs/robust-birth
python -B latency/validate.py --out ../../audit_runs/robust-latency
python -B periodic/validate.py --out ../../audit_runs/robust-periodic
python -B validate.py --quick --out ../../audit_runs/robust-smoke
```

Verify each new record with the same validator and output directory, for example:

```sh
python -B birth/validate.py --verify-record --out ../../audit_runs/robust-birth
```

The two-case `--quick` run has its own fresh directory and is labelled quick in
both its report and publication metadata. It never replaces a full campaign.
These checks verify provenance and numerical records; they are not a rerun or
a formal proof of the simulated trajectories.
