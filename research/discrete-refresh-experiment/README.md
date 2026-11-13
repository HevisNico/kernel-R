# Discrete refresh experiment v1

Protocol: [PREDICTION.md](PREDICTION.md), published in commit
`ca8645502588339c43e836b7319c6348dbebcfd2` before implementation.
Dependency: PR #111 frozen at `ba978af1edaf51572aa0af9d1bfc83e309438d3d`.
This PR is stacked on #111; the owner handles both merges.

## Files and information boundary

- `controllers.py`: observations and policies. The contract policy calls Lean;
  it has no access to plant state, the jump instant or the noise generator.
- `Bridge.lean`: invokes `ClosedLoop.choose` and `Renewal.review` from #111.
- `experiment.py`: deterministic plant, within-period chronology, one-run gate
  and streaming traces. Only this layer and the scorer know ground truth.
- `evaluate.py`: checks recorded traces and emits the report. It never runs a
  controller or plant trajectory. All registered predictions remain in output.
- `test_synthetic.py`: six synthetic checks; no registered trajectory is run.
- `run-v1/`: the single run's raw traces, metadata, logs and unedited report.

The fixed fallback keeps U=22 even before the jump; rate measurements drive
reopening memory only. It therefore tests a conservative contract supervisor,
not a policy learning a tighter future bound. No new end-to-end wrapper proof,
physical R certification, statistical significance or real energy is claimed.

## Checks without rerunning the experiment

Use the pinned Lean 4.35.0 distribution on PATH. Build the frozen dependency
from `../self-certifying-learning` with `lake build`. From this directory:

```sh
python3 -B -m unittest -v test_synthetic
```

The recorded results are in [REPORT.md](run-v1/REPORT.md) and
[summary.json](run-v1/summary.json). Each CSV has 1321 rows, including the
charged initial observation. Timestamps and numbers use exact integers.

The registered invocation is `python3 -B experiment.py --run-once`. It was
reserved for the initial publication workflow. Its exclusive `run-v1`
directory prevents overwriting or rerunning the registered result. Do not
remove that directory to repeat v1: register a separate replication instead.

To inspect metrics without emitting files, import `load_rows`, `metrics` and
`audit` from `evaluate.py` and apply them to the recorded CSVs. This analyzes
existing evidence; it does not execute the experiment again.
