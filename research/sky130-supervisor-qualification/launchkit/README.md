# Owner launch kit — no registered campaign supplied yet

The registered campaign is run **only by the owner on the owner's machines**.
This directory supplies and tests the environment checks, durable one-attempt
launch protocol, two-machine split, evidence collection and interruption path.
It contains no PREDICTION.md, registered seeds, jump scenarios or launchable
registered manifest. Phase 1 is still qualification. Commands below become
campaign commands only after the owner approves the final protocol, source
commit and frozen `CAMPAIGN.json` described in [MANIFEST.md](MANIFEST.md).

## Exact environment

| Component | Required identity |
|---|---|
| Platform | Linux x86_64; native Ubuntu24.04 is the reference host |
| ngspice | 42, Ubuntu package `42+ds-3build1` |
| ngspice executable SHA-256 | `820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45` |
| Package SHA-256 | `466c4c06418107ceaa9c9457065b3bb71a9d9dc5ec6fef186d7de9d5208ce8db` |
| SKY130 PDK | `1232782c1b9fab3aacda74d67ce7c92bf7da8105`, clean checkout |
| Python | 3.12.14 exactly |
| numpy | 2.3.5 exactly |

The ngspice44.2 phase-0 runtime is deliberately rejected. Use Python3.12.14
from an existing installation or install that exact interpreter before making
the virtual environment. Do not substitute another Python and alter the check.
For example, from a fresh owner checkout:

```sh
PHASE1_PYTHON=/absolute/path/to/python3.12.14
"$PHASE1_PYTHON" -m venv ../owner-python
../owner-python/bin/python -m pip install numpy==2.3.5
mkdir -p ../owner-runtime
curl --fail --location https://archive.ubuntu.com/ubuntu/pool/universe/n/ngspice/ngspice_42+ds-3build1_amd64.deb -o ../owner-runtime/ngspice.deb
../owner-python/bin/python - ../owner-runtime/ngspice.deb <<'PY'
import hashlib,sys
from pathlib import Path
assert hashlib.sha256(Path(sys.argv[1]).read_bytes()).hexdigest() == '466c4c06418107ceaa9c9457065b3bb71a9d9dc5ec6fef186d7de9d5208ce8db'
PY
dpkg-deb -x ../owner-runtime/ngspice.deb ../owner-runtime/extracted
git clone https://github.com/efabless/skywater-pdk-libs-sky130_fd_pr ../owner-runtime/pdk
git -C ../owner-runtime/pdk checkout 1232782c1b9fab3aacda74d67ce7c92bf7da8105
```

Install the native package's shared-library dependencies if required; a missing
library fails the preflight. A registered run must use the frozen Python runner, not direct ngspice.
The frozen runner must stage the pinned
`research/circuit/spiceinit.txt`, model includes and deck exactly as reviewed.
Registered launches reject `LD_PRELOAD`, `SPICE_SCRIPTS`, `PYTHONPATH` and
`PYTHONHOME` overrides. The sandbox-only tmpfile adapter used in the synthetic
kit test is not an allowed substitution for the native owner environment.

Set paths on each machine (absolute paths may differ; identities may not):

```sh
PHASE1_PYTHON="$PWD/../owner-python/bin/python"
PHASE1_NGSPICE="$PWD/../owner-runtime/extracted/usr/bin/ngspice"
PHASE1_PDK="$PWD/../owner-runtime/pdk"
PHASE1_KIT=research/sky130-supervisor-qualification/launchkit/launch.py
PHASE1_MANIFEST=path/to/the/future/approved/CAMPAIGN.json
PHASE1_BRANCH=the-future-owner-campaign-branch
```

## Preflight and publish the attempt before launch

The approved manifest must already be committed on the campaign branch before
these commands; its only difference from the frozen source tree is the manifest.
Do not leave a draft manifest untracked in this checkout.

```sh
"$PHASE1_PYTHON" -B "$PHASE1_KIT" preflight --repo "$PWD" --manifest "$PHASE1_MANIFEST" --ngspice "$PHASE1_NGSPICE" --pdk "$PHASE1_PDK"
"$PHASE1_PYTHON" -B "$PHASE1_KIT" plan --repo "$PWD" --manifest "$PHASE1_MANIFEST" --ngspice "$PHASE1_NGSPICE" --pdk "$PHASE1_PDK"
```

Preflight checks executable version/hash, exact Python/numpy, PDK commit and
cleanliness, protocol/source commit ordering, frozen source/deck hashes, and
both machine inventories. After the implementation freeze the only permitted
tracked changes are the approved manifest and its RUN_ATTEMPT.json. This also
freezes repository-local imported modules outside the explicit file list.
Unknown tracked changes or untracked potential runtime files reject launch.
The final frozen runner/dependency list remains subject to code review; these
checks are not a proof of arbitrary Python or external OS libraries.

The plan reports the sum of declared `estimate_s` for **machine a** and
**machine b**, as well as their run IDs. Both must be nonempty; their combined
forecast must fit the timeout envelope, and the sum of **every timeout plus
10 seconds termination allowance per run** must fit the declared budget of
at most 14,400 seconds. Small estimates cannot conceal unbounded timeouts.
The marker records both per-machine estimates and execution/cleanup caps.
These caps cover launched process waits and forced termination; environment
setup, Git publication and copying the collected evidence are outside those
process-time caps and must be scheduled separately.

The phase-1 measurements now give this **provisional packing**, before any
scenario assignment or preregistration:

| Machine | Allocation | Estimated simulation time |
|---|---|---:|
| a | Three sequences of 32 service periods plus one setup-period allowance | 5,827.63 s (1 h 37 min 08 s) |
| b | Three sequences of 32 service periods plus one setup-period allowance | 5,827.63 s (1 h 37 min 08 s) |
| Aggregate | Six sequences | 11,655.26 s (3 h 14 min 15 s) |

The rate uses 35 s per 440 us period, the largest observed paired noise factor
1.324705, 25% reserve and 30 s extra startup per sequence. This is an empirical
forecast on the calibration machine, not a bound for arbitrary hardware.
A tentative cap of 2,300 s plus 10 s cleanup per sequence fits 13,860 s total;
the future manifest must freeze the actual limits before launch. More expensive
charged preparation, additional repetitions, or slower owner hardware must
reduce the scope **before** preregistration. Three whole-run noisy repetitions
alone cannot support a strong reliability statement. No registered run IDs,
seeds or leakage jumps have been assigned here. Final estimates must appear
in CAMPAIGN.json and RUN_ATTEMPT.json; changing them after launch is forbidden.

On one machine, after all exact-implementation-head CI workflows and their
latest-attempt jobs are successful:

```sh
"$PHASE1_PYTHON" -B "$PHASE1_KIT" prepare --repo "$PWD" --manifest "$PHASE1_MANIFEST" --ngspice "$PHASE1_NGSPICE" --pdk "$PHASE1_PDK"
git add -- "$PHASE1_MANIFEST" path/to/the/future/approved/RUN_ATTEMPT.json
git commit -m "Record owner campaign attempt 1 before execution"
git push origin HEAD:"$PHASE1_BRANCH"
```

`prepare` performs a live GitHub CI check for `source_commit`: every expected
workflow must exist, every additional workflow present is checked, and the
latest attempt's jobs must all finish with success. No parent green result
is accepted. It creates RUN_ATTEMPT.json exclusively; it never overwrites an
existing marker. The marker binds the protocol, implementation, manifest,
environment, split and estimates. Each machine fetches the published campaign
branch before launching; a local-only marker is rejected.

## Exactly one launch command per machine

Both machines first check out the same published marker commit. Each launch
performs preflight and live exact-head CI checks again, then pushes a durable
claim **before starting its first process**. Git identity and normal GitHub
push access must already work. Claim branches are
`owner-launch/protocol-<protocol_sha256>/a` and `/b`; keep them permanently.
The content hash of the protocol is the lock identity: changing campaign ID
or output directory cannot create another attempt under the same protocol.

Machine a:

```sh
"$PHASE1_PYTHON" -B "$PHASE1_KIT" run-machine --repo "$PWD" --manifest "$PHASE1_MANIFEST" --ngspice "$PHASE1_NGSPICE" --pdk "$PHASE1_PDK" --branch "$PHASE1_BRANCH" --machine a --out "$PWD/../owner-evidence-a"
```

Machine b:

```sh
"$PHASE1_PYTHON" -B "$PHASE1_KIT" run-machine --repo "$PWD" --manifest "$PHASE1_MANIFEST" --ngspice "$PHASE1_NGSPICE" --pdk "$PHASE1_PDK" --branch "$PHASE1_BRANCH" --machine b --out "$PWD/../owner-evidence-b"
```

A normal push creates each claim; no force push, deletion, merge or retry is
used. Concurrent claims produce different sibling commits, so the second push
cannot fast-forward the first. Any existing claim rejects execution, including
from a different clone or output path. A claim followed by a network failure,
crash or cancellation is still consumed. Changing the campaign ID does not bypass the protocol-hash lock. The external owner can always deliberately modify Git/code;
this protocol protects the declared workflow, not a malicious administrator.

## Interrupted run: preserve, never relaunch

A zero simulator exit code does not establish a complete transient or a
scientific pass. The manifest requires named nonempty regular output files
and simulator logs. The kit rejects missing/empty outputs and fatal markers
(`aborted`, `timestep too small`, `transient op failed`, `fatal error`), even
after exit 0. The frozen runner must additionally validate final waveform
time, required vectors, event inventory and scientific protocol conditions.
`complete` in the launch ledger means successful execution/postflight, not
that every scientific prediction held. Unfavorable valid runs are retained.

Reaching a timeout consumes the attempt: publish the partial result, never
restart it or extend its limit after seeing the data. On timeout, error or ordinary interruption the launcher terminates the process
group, closes its logs, marks the shard incomplete and does not start later
runs in that shard. SIGKILL or power loss may leave `STATE.json` as `running`;
that is evidence of interruption, not permission to restart. Confirm no child
process remains, retain the original state, and collect all survivors with
`--interrupted`. The durable Git claim forbids restarting either completed or
interrupted shards. A separate already-running shard can finish; never repeat
its runs to replace lost data. Report missing runs as missing.

Do not delete an output directory, remove a claim, change a seed, rerun a
scenario, repair a raw trace or overwrite a marker. If the marker exists but
a preflight fails before any durable claim, fix the environment and repeat the
preflight only. If a claim push's success is uncertain, inspect the remote
claim and preserve it; do not treat uncertainty as a fresh attempt.

## Collect and push raw evidence unchanged

After each shard has stopped, collect to a **new** publication directory:

```sh
"$PHASE1_PYTHON" -B "$PHASE1_KIT" collect --out "$PWD/../owner-evidence-a" --destination "$PWD/path/to/evidence/machine-a"
"$PHASE1_PYTHON" -B "$PHASE1_KIT" collect --out "$PWD/../owner-evidence-b" --destination "$PWD/path/to/evidence/machine-b"
```

Add `--interrupted` only after confirming processes are stopped if an original
state still says `running`. Collection copies every surviving regular file
byte for byte, checks unchanged source bytes, rejects symlinks, and writes
SURVIVORS.json with every size/hash. It does not recompress, edit or delete raw
files. A failed collection is preserved too; use a new destination only after
understanding why it failed, never a new experiment attempt.

The owner then stages the **exact manifest-listed evidence files plus their
SURVIVORS.json**, reviews `git diff --cached --name-status`, commits and uses a
normal push. Use separate owner evidence branches if the two machines would
otherwise push competing commits to the same branch; do not resolve that by
force-pushing. Bring both evidence commits into the review branch normally.
No campaign is discarded because it was partial or unfavorable.

## Synthetic end-to-end verification

[SYNTHETIC_TEST.json](SYNTHETIC_TEST.json) records a real ngspice42 run on a
simple RC circuit, unrelated to the R cell. A second local fixture exits
zero without its required waveform; it is refused and its claim stays consumed. It uses a fresh local bare Git
remote, not GitHub. The test exercises publication-before-launch, both machine
claims, successful execution, timeout with surviving binary evidence,
relaunch rejection even with new output paths, and byte-identical collection.
The same RC waveform SHA-256 was reproduced across the kit development checks.

```sh
python3 -B -m unittest discover -s research/sky130-supervisor-qualification/launchkit -p 'test_*.py' -v
python3 -B research/sky130-supervisor-qualification/launchkit/synthetic_test.py --ngspice "$PHASE1_NGSPICE" --pdk "$PHASE1_PDK" --work /a/new/empty/synthetic-test-directory --report /a/new/synthetic-test-report.json
```

The `--runtime` option is only for the sandbox portability test and does not
exist on the registered launcher. Synthetic tests may be rerun in fresh local
fixtures; they neither authorize nor consume any registered campaign attempt.
