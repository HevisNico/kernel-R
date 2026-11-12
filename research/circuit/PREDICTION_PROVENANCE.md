# Where the date of the predictions can be checked

[`PREDICTION.md`](PREDICTION.md) says that it was written before any run
of the campaign. This repository cannot show it: the file entered this
repository after the campaign had started. The date can be checked in
another place, by whoever has read access to it.

## The record

The campaign was prepared and run in a private repository,
`HevisNico/kernel-R-circuit`, branch `sim/core-loop`. GitHub records the
time at which it receives each push. That time is set by GitHub, not by
the author, and a commit date cannot change it.

| Push received by GitHub (UTC) | Push id | Commit after the push | What the commit holds |
|---|---|---|---|
| 2026-11-12 07:22:56 | 49971586004 | `a8fd2197916c017cbc58198fa627e951cfab57a3` | `PREDICTION.md`, the netlist, the runner and the list of runs. No result |
| 2026-11-12 07:26:09 | 49971909721 | `3b7319475b4998db8664f126bb42f8bceb4d5627` | The design note and the first analysis script. No result |
| 2026-11-12 08:55:13 | 49981168303 | `4ee2d314f0dc29750a381631c45ded87d89fcf97` | The first results: 69 files |
| 2026-11-12 09:56:24 | 49987975686 | `de9e68ecb92b53aec3905ba054bda79a1924df2b` | The last results of the 141 runs |

In this repository, GitHub received the branch of this folder at
09:02:46 UTC (push id 49982009830), with `PREDICTION.md` in it. The
branch was rebased since, so its first commit has another name today.

## The files are the same

Git names a file by a hash of its content. The files of the commit
`a8fd219` of the private repository have the same hash here.

| File | Git hash of the content | Same in this repository |
|---|---|---|
| `PREDICTION.md` | `35a317975ce4dc51feba935df464ee3c25b8c731` | yes, in every commit |
| `cell.spice` | `532374af73c7dc859c06330ffa8f3bfcb14ede6c` | yes, in every commit |
| `blocks.spice` | `462312fcd52890595fa8b5100de83b5c87efa504` | yes, in every commit |
| `noise.json` | `28428eac6d07287ed8cdab40ac6daa9721c82e1b` | yes, in every commit |
| `campaign.py` | `1f949706bfeb2102f669728523e1f4c1465d4d98` | yes, in every commit |
| `run.py` | `4202913c466001e3a2093370e6494aa71cc0666a` | yes, in the first commit of the folder. Options were added after the campaign |

The SHA-256 of `PREDICTION.md` is
`8c17bf311e7f1353a6a41da84ad8f9c4fd3b4b6ff150c2a6009b620e935181e8`.

`PREDICTION.md` is not edited to hold this record: it would no longer
be the file of the commit `a8fd219`.

## How to check

With read access to the private repository:

```sh
gh api "repos/HevisNico/kernel-R-circuit/activity?per_page=100" \
  --jq '.[] | "\(.timestamp) \(.id) \(.after)"'
git rev-parse a8fd2197916c017cbc58198fa627e951cfab57a3:05-cell/PREDICTION.md
```

In this repository:

```sh
git rev-parse HEAD:research/circuit/PREDICTION.md
sha256sum research/circuit/PREDICTION.md
```

## To consult the private repository

Ask the author, Nicolas Breuillaud. Open an issue on this repository,
or write to the GitHub account `HevisNico`. Read access to the private
repository is given on request, for the time of the check.

## What this shows, and what it does not

- **It shows** that the predictions, the netlist and the list of runs
  were at GitHub at 07:22:56 UTC, and that the first results reached
  GitHub at 08:55:13 UTC.
- **It does not show** that no run had been made before 07:22:56. That
  stays a statement of the author.
- **It is not public.** A reader without access to the private
  repository cannot check any of this.
- **The predictions are not blind.** `PREDICTION.md` lists what was
  known when it was written.
