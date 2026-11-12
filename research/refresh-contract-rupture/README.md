# V3: contract rupture and blocked stop

The final [PREDICTION.md](PREDICTION.md) was published at
`07caf3fdf22c1cd28f05a2159d40aceaa33af80b`, before implementation or execution.
It fixes the active spacing (6), expected detection delay (1), dangerous
exposure, and blocked stop after demonstrated invalidation. Dose 220 exceeds
140*1: this is an invalid-contract/entry-buffer test, not insufficient power.

The v2 controller, bridge, calibration and all previous results remain frozen.
`experiment.py` imports that controller unchanged and runs one negative test.
Its exclusive `run-v3` directory must never be removed to retry the trial.
A new replication requires a separate protocol. All periods after refusal
remain in the raw trace and unsafe exposure totals.

Safety reporting distinguishes a fresh sampled-instant declaration from an
active conditional contract. Neither an absent probe nor a stale carried
bound justifies an unconditional safety declaration. Rows are emitted once
with a hash chain; the report separately exposes any unsafe period during
which the old conditional contract was still active.

`score_rupture.py` audits recorded CSVs without running any trajectory.
`check_evidence.py` verifies historical source/protocol hashes, saved v1/v2/v3
metrics and reports. With `--proofs`, it also compiles/checks v2 in an isolated
copy and runs synthetic tests. It never calls an experiment runner. During
preparation only, `--preflight` explicitly checks existing v1/v2 evidence;
normal CI requires v3 evidence as well and does not use that option.

After publication the raw trace, unedited report, metadata, stdout/stderr and
exit status reside under `run-v3`. No forward Markdown link is added before
those files exist. The registered command is `python3 -B experiment.py --run-once`.
The owner handles fusion of #114; no merge is performed here.
