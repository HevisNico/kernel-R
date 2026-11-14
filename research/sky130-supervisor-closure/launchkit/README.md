# Launch kit, second version — no registered campaign is supplied

This folder replaces, for the future registered campaign, the launcher of
[`../../sky130-supervisor-qualification/launchkit`](../../sky130-supervisor-qualification/launchkit/README.md).
That first version is left untouched; its files are still checked by its own
test. Nothing here is a registered scenario, a seed list or a PREDICTION.md.

**Who runs the campaign.** The executor is a Claude Code cloud session on
behalf of the owner, on two cloud containers whose inventories are recorded.
The first version said "the owner alone, on the owner's machines"; that
sentence is replaced by this one. The manifest must carry the executor
sentence exactly, and the attempt marker and both inventories repeat it.

What stays from the first version: the environment check, the protocol commit
that must precede the implementation commit, the attempt marker published
before any launch, one permanent claim per machine (a claimed machine is never
launched a second time, from any clone or folder), the collection of every
surviving file byte for byte.

## What changes

| Subject | Second version |
|---|---|
| Python | 3.12.3, the interpreter of the Ubuntu 24.04 package `python3.12-minimal` version `3.12.3-1ubuntu0.17`; SHA-256 of the executable `e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f` |
| numpy | 2.3.5 from PyPI; SHA-256 of its installed `RECORD` file `064003bdb6f9f7bb06e46e07cc3398cbfdc3c114dfe55b89d239e564917be2fb` |
| ngspice | unchanged: 42, executable SHA-256 `820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45` |
| PDK | unchanged: commit `1232782c1b9fab3aacda74d67ce7c92bf7da8105`, clean checkout |
| Simulator start file | the launcher sets `SPICE_SCRIPTS` itself, to the folder of a committed file named `spinit` that contains `set num_threads=1` and is frozen by hash in the manifest. A registered launch is refused if `SPICE_SCRIPTS`, `LD_PRELOAD`, `PYTHONPATH` or `PYTHONHOME` is set by the caller |
| Runs of a machine | independent; listed round-robin over the scenarios, so that every prefix of the list is balanced (the counts of two scenarios never differ by more than one); up to `jobs` at the same time, started in list order |
| A run that fails or reaches its time limit | stays failed (`failed-never-rerun`, `time-limit-never-rerun`); the runs not yet started go on |
| Restart of the machine | `resume-machine`: every run that had started and not ended is recorded `lost-started-before-restart-never-rerun` and is never run again; the runs that had never started proceed. Refused if the machine did not restart since the shard was last started |
| Inventories | `inventory` writes, for each machine, its processor, memory, system, kernel, start date and the pinned identities; both files are committed and their hashes are bound in the attempt marker; a new inventory is written at launch and at each resume |
| Noise | every registered run hands over a fingerprint of the noise it drew; `check-noise` lists the runs that share one |
| CI | the live check of the exact implementation head is made by `prepare` and again by each launch and resume; `prepare` stores what it saw in the marker (`ci_at_prepare`) |
| Budget | a bound on wall time: for each machine, `sum(timeout + 10 s) / jobs + max(timeout + 10 s)`; the two machines together at most `budget_s`, itself at most 14 400 s |

### Python: why 3.12.3, and what was checked

Python 3.12.14 cannot be installed on the cloud containers; 3.12.3 is the
interpreter of their system package. The 23 diagnostics without noise of
PR 123 were replayed with `calibrate.py` under 3.12.3 and numpy 2.3.5:
every deck, every waveform and every analysis result is identical to what
[`RESULTS.json`](../../sky130-supervisor-qualification/RESULTS.json) published
under 3.12.14 ([`PYTHON_IDENTITY.json`](../PYTHON_IDENTITY.json), written by
[`python_identity.py`](../python_identity.py)). The three noisy diagnostics
cannot be replayed and are not part of the comparison.

```sh
/usr/bin/python3.12 -m venv ../campaign-python
../campaign-python/bin/python -m pip install numpy==2.3.5
../campaign-python/bin/python -B research/sky130-supervisor-closure/launchkit/launch.py identity --ngspice /usr/bin/ngspice --pdk /absolute/path/to/pdk
```

`identity` prints the seven pinned values and refuses any difference.

### Noise is not replayable

ngspice 42 seeds its noise sources from the number of its own process. The
kit refuses the preloaded library that PR 115 used to impose that number, so
the noise of a registered run is whatever the operating system gave: it
cannot be chosen, and it cannot be replayed. A lost run cannot be
reconstructed.

What is recorded instead is a fingerprint: the SHA-256 of the first 64 values
drawn by the five voltage noise sources, in nanovolts, at the sources' own
sample dates ([`extract.noise_fingerprint`](../extract.py)). Measured with
imposed process numbers, outside any registered run
([`fingerprint_check.py`](../fingerprint_check.py), results in
[`QUALIFICATION.json`](../QUALIFICATION.json)):

- two runs have the same fingerprint exactly when they have the same process
  number and the same `setseed` command; the corner and the temperature do
  not change it. Two runs with the same fingerprint drew the same noise and
  are not two repetitions;
- on a corner without mismatch, `setseed` changes the noise and nothing else
  (without noise the waveform is identical byte for byte whatever the seed).

Two containers number their processes in the same range (the numbers wrap at
32768 on the containers used here), and a restarted container starts again
from low numbers: equal process numbers are to be expected. Consequences for the registered campaign:

1. each run on a corner without mismatch gets its own `setseed` value in the
   manifest, distinct over the two machines; equal process numbers then give
   different noise;
2. a mismatch instance is defined by its `setseed` and cannot receive another
   one: the runs of one instance are separated by their process numbers only;
3. the analysis runs `check-noise` on the evidence of both machines before
   counting anything, and applies the rule that PREDICTION.md fixed for runs
   that share a fingerprint.

`check-noise` exits with status 2 when two runs share a fingerprint and lists
them; it changes nothing.

## What PREDICTION.md must fix before any implementation

The kit executes; it does not decide. The preregistration must contain, in
words that leave no choice after the data are seen:

- **the truncated campaign.** Proposed rule: the analysis uses, for each
  scenario, every run that is `complete` in the state files, whatever their
  number; a run that is failed, at its time limit or lost is reported with
  its status and is neither replaced nor counted as a success or as a failed
  service — it is a missing run. Because each machine lists its runs
  round-robin, a campaign cut at any point has scenario counts that differ by
  at most one per machine. Each claim of the preregistration states the
  smallest number of complete runs under which it is declared "not
  established" instead of being evaluated; no claim is re-scoped after the
  cut;
- **runs that share a noise fingerprint.** Proposed rule: of several complete
  runs with the same fingerprint, the first in manifest order (machine a
  before machine b) is counted; the others are listed as duplicates and are
  not counted;
- **the resume rule**, as implemented here, and that a container restart is
  the only event that allows `resume-machine`;
- the machine split, `jobs`, every `setseed`, every time limit and the budget.

## Commands

All paths are examples. `KIT=research/sky130-supervisor-closure/launchkit/launch.py`,
`PY` the interpreter of the pinned environment.

```sh
"$PY" -B "$KIT" inventory --machine a --out path/to/INVENTORY_a.json --ngspice "$NGSPICE" --pdk "$PDK"
```

One inventory per machine, each written on its own machine, both committed
with the manifest on the campaign branch. Then, on one machine:

```sh
"$PY" -B "$KIT" preflight --repo "$PWD" --manifest "$MANIFEST" --ngspice "$NGSPICE" --pdk "$PDK"
```

```sh
"$PY" -B "$KIT" prepare --repo "$PWD" --manifest "$MANIFEST" --ngspice "$NGSPICE" --pdk "$PDK"
```

`prepare` checks the CI of the exact implementation head, then writes
RUN_ATTEMPT.json once (it never overwrites). The marker binds the protocol,
the implementation, the manifest, the environment, both inventories, the
split, the scenario order and the budget. It is committed and pushed before
any launch; a marker that exists only locally is refused. The checkout must
be a clone of `https://github.com/HevisNico/kernel-R` (that exact spelling).

One launch per machine:

```sh
"$PY" -B "$KIT" run-machine --repo "$PWD" --manifest "$MANIFEST" --ngspice "$NGSPICE" --pdk "$PDK" --branch "$BRANCH" --machine a --out "$PWD/../evidence-a"
```

After a restart of that machine, and only then:

```sh
"$PY" -B "$KIT" resume-machine --repo "$PWD" --manifest "$MANIFEST" --ngspice "$NGSPICE" --pdk "$PDK" --branch "$BRANCH" --machine a --out "$PWD/../evidence-a"
```

When a shard has ended:

```sh
"$PY" -B "$KIT" collect --out "$PWD/../evidence-a" --destination "$PWD/path/to/evidence/machine-a"
```

```sh
"$PY" -B "$KIT" check-noise --evidence "$PWD/../evidence-a" "$PWD/../evidence-b"
```

`collect` copies every surviving regular file byte for byte and writes
SURVIVORS.json with each size and SHA-256. It compresses, edits and deletes
nothing. The raw evidence is then committed unchanged with that list.

The evidence folder of a machine lives on the container's disk. A restart
that also erased the disk would leave nothing to resume: the claim would
remain, the shard would be reported lost, and nothing would be relaunched.

## Tests

```sh
"$PY" -B -m unittest discover -s research/sky130-supervisor-closure/launchkit -p 'test_*.py' -v
```

```sh
"$PY" -B research/sky130-supervisor-closure/launchkit/synthetic_test.py --ngspice "$NGSPICE" --pdk "$PDK" --work /a/new/empty/folder --report /a/new/report.json
```

The second command is the end-to-end test recorded in
[SYNTHETIC_TEST.json](SYNTHETIC_TEST.json): an RC circuit unrelated to the R
cell, a local bare Git remote, never GitHub. It checks that an unpublished
marker is refused; that a run which exits 0 without its output stays failed
while the runs after it proceed; that the runner receives the committed start
file; that second launches are refused; that a resume without restart is
refused; that after a simulated restart the two runs that had started are
recorded lost and never run again while the two others complete; that the
evidence of the lost runs is untouched; that fingerprints are recorded and
compared; and that the collection is byte-identical. A synthetic test neither
authorizes nor consumes a registered attempt.
