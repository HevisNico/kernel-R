# Registered v4 recovery demonstration

Status: protocol published before implementation; **no registered attempt has
been executed**. Predictions are not observations. The prerequisite is #117 at
`c6684f796d092b2324489cb9920f78a9fcca7a5a`; every workflow and latest-attempt job
on that exact head must succeed before the attempt.

The [preregistration](PREDICTION.md) fixes the v3 scenario, four unguaranteed
recovery writes, one external authorization at 666, and a return to guaranteed
service **after delivery at 666**. The pre-delivery state at 666 remains unsafe
and unguaranteed. Predicted total cost is 5,421 declared units: 838 probes,
450 writes at ten units each, one root authorization and 82 phase tokens.
All unsafe exposure and old-lease claims remain visible.

The new ceiling 150 is justified by the registered simulator's future leakage
140. It is an external model certificate, not a bound inferred from past
samples, a transistor measurement, or a guarantee for an unknown future plant.
Unconditional uninterrupted service across the whole run remains refuted.

## Evidence boundary

`Model.lean` proves the root ceiling, sensor enclosure, actual Lean policy
shape, invariant preservation and arithmetic predictions. Its axiom audit
covers 59 declarations, including 49 theorem declarations (generated ones
included), with only `propext`, `Classical.choice` and `Quot.sound` allowed.
Five paired semantic mutations must fail. These are local formal results;
the complete Python orchestration is not a formally proved refinement.

`experiment.py` uses the unchanged v2 Contract and #117 Supervisor. The
external authority receives time and request state, never plant truth or
sensor reports. `score_v4.py` independently audits saved rows algebraically,
including the original v3 prefix, pre/post boundaries, commands, generations,
authorizations, budgets, costs and append hash chain. It never launches
another trajectory. Six saved-trace mutations must be rejected even after
recomputing their hash chains; these checks run only once evidence exists.
Synthetic fixtures never import the registered runner.

## Preparation and one attempt

With the repository's pinned Lean 4.35.0 distribution on `PATH`:

```sh
cd research/recovery-v4
python3 -B verify.py --preflight --report validation.json
```

Publish the tested implementation and its validation report. Then inspect
#117's exact head and all latest workflow attempts/jobs; publish their successful
snapshot as `CI_GATE.json` and a persistent `RUN_ATTEMPT.json` identifying attempt
1, protocol commit and implementation commit. Only after that publication, from
a clean checkout, launch the registered runner once:

```sh
python3 -B experiment.py --run-once
```

The runner creates `run-v4` exclusively and preserves failure output. An existing
remote attempt marker forbids a new launch after interruption, even if the local
output disappeared. Never delete the output directory, tune the protocol, retry
a failed attempt, or run a shortened pilot. Publish raw output and the unedited
report even on failure. CI never executes this command.

After evidence has been published:

```sh
python3 -B verify.py
```

This rechecks saved evidence without running the controller. CI uses preparation
checks until recorded evidence exists, then requires the full saved-evidence
audit. A green preparation job alone does not establish the experiment's result.
The original experiments and #117 sources are frozen. Learned variation,
statistical repetition and transistor campaigns are outside this PR.
