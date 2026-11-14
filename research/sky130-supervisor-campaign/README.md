# SKY130 supervisor campaign

**Nothing has been launched.** This folder holds the preregistration of the
campaign and, written after it, its frozen implementation. It waits for an
independent review of [`PREDICTION.md`](PREDICTION.md), then for the owner's
word.

| File | What it is | When |
|---|---|---|
| [`PREDICTION.md`](PREDICTION.md) | scenarios, split, seeds, budget, predictions, rules of the analysis | commit `77ffe5e`, alone, before anything below existed; SHA-256 `27989a36013709de4fe77e1c8baa5fbdf168c4b4662cd38fec3583af9b72cab5` |
| [`run.py`](run.py) | one run: the deck, session, kernel and bounds of the qualification, plus the leakage jump and the mode without supervisor | after |
| [`plan.py`](plan.py) | the 124 runs, and the manifest of the launch kit, written at launch time from the two commits | after |
| [`analyze.py`](analyze.py) | the analysis, run once at the end; every measure is taken again from the waveforms | after |
| [`test_campaign.py`](test_campaign.py) | the plan against the preregistration and the bounds; the decisions of a period; the analysis on made-up runs | after |
| [`rehearsal.py`](rehearsal.py), [`REHEARSAL.json`](REHEARSAL.json) | the whole chain on the real simulator: four runs of three services, **no leakage jump**, outside the registered scenarios | after |

The launcher is the second launch kit,
[`../sky130-supervisor-closure/launchkit`](../sky130-supervisor-closure/launchkit/README.md).
The files that a run or the analysis executes are listed in `plan.FROZEN`; the
manifest freezes each by its hash at the implementation commit.

No leakage jump has been simulated: not in the qualification, not in the
tests, not in the rehearsal (its "jump" value is the reference leak).

## What the rehearsal showed

Launcher in its `synthetic` kind, a local clone and a local Git remote: the
attempt marker published before the launch, one claim per machine, a second
launch refused, the four runs complete, no link in the evidence, the
collection byte for byte, and the analysis reading the collected evidence:
records equal to the waveforms, reports equal to the waveforms, every write
as commanded, twelve correct services. The waveform of a run of three
services is 1.4 to 3.6 MB; a run of 24 services will be about 8 MB without
noise and 16 MB with.

## Before the launch (step C, on the owner's word only)

1. Gates: the qualification is published with its bounds (PR 136); this
   preregistration was pushed alone before the implementation; every CI job
   is green on the exact implementation head; the split, the seeds and the
   budget are in the preregistration; `launch.py identity` gives the same
   seven values on both containers.
2. On each container: a clone of `https://github.com/HevisNico/kernel-R`
   (that spelling), the pinned environment, at least 3 GB free, push access
   to this repository and to the private `HevisNico/kernel-R-circuit`.
3. `plan.py manifest PROTOCOL_COMMIT SOURCE_COMMIT > CAMPAIGN.json`, the two
   inventories, `launch.py preflight`, `launch.py prepare`; the manifest,
   the inventories and RUN_ATTEMPT.json are committed and pushed.
4. `launch.py run-machine --machine a` on one container and `--machine b` on
   the other. No count is looked at while they run. After a container
   restart, and only then, `resume-machine`.
5. `launch.py collect` on each machine, `check-noise`, then `analyze.py`
   once. Decks, logs, records, fingerprints, small waveforms, the SHA-256
   list and the generated report are committed here; the waveforms of the
   whole runs go unchanged to the private repository.

A change to a frozen file after the review is a new commit, a new CI run and
a new review; the preregistration is never changed.
