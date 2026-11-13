# Adaptive refresh experiment v2

[PREDICTION.md](PREDICTION.md) was published in commit
`c58ba5af913a5d129734aaa6d66a16fce99e27aa` before implementation or execution.
V1 (#112) and its formal basis (#111) remain frozen and are not rerun or merged.

The new information assumption is an upward excursion at most 10 over each
41-period horizon. No absolute rate ceiling is supplied to any controller.
Each rate report produces a local ceiling; handoff and carried-state margins
protect the subsequent repair. This estimates a renewable envelope under a
known physical law. It does not learn that law or certify arbitrary futures.

`Bridge.lean` contains the local inference/handoff/repair lemmas and invokes
#111's exact scheduling and interval-memory primitives. `controllers.py` holds
only observation inputs and action history. `experiment.py` owns plant truth;
`evaluate.py` independently checks the recorded traces. The wrapper is not a
newly proved end-to-end physical system.

With pinned Lean 4.35.0 on PATH and the frozen standalone foundation package
built, run `python3 -B verify_local.py` here for proof/synthetic checks only.
The recorded check result is in `validation.json`. Neither those checks nor
CI execute the registered trajectory. Python 3.12 and the standard library
suffice; no external Python package is needed.

The registered command is `python3 -B experiment.py --run-once`. It creates an
exclusive `run-v2` directory and must only be invoked once in the publication
workflow. Results, when published, occupy `run-v2/REPORT.md`, `summary.json`,
three CSVs, metadata, stdout/stderr and exit status. These paths are plain text
until the evidence exists. Do not remove the directory to rerun v2. A future
replication needs a separately identified protocol and output directory.

`evaluate.load_rows`, `metrics` and `audit` can inspect existing evidence
without executing a new trajectory. All predictions, including failures,
remain in the unedited generated report. Comparisons with v1 use its published
1247-unit cost and do not replay v1.

Next physical work: establish a circuit state map and sensor correspondence,
extract dose/loss intervals from actual refresh waveforms with explicit units,
and check those premises against fabrication/noise conditions. A transistor
jump experiment comes after that calibration and its own preregistration.

After the registered v2 run, [R_CALIBRATION.md](R_CALIBRATION.md) derives nominal
voltage/dose/leakage estimates from 13 existing refresh CSVs, separating net
write increments from inferred gross dose. No v2 input or result was changed.
