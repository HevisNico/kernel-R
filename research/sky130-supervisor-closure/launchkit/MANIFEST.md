# Manifest of the future campaign, second version

No registered manifest exists yet. This is the contract that
[`launch.py`](launch.py) enforces; fields not listed here are as in
[the first version](../../sky130-supervisor-qualification/launchkit/MANIFEST.md).

Campaign fields:

- `kind`: `registered` (`synthetic` is reserved for local tests);
  `campaign_id`; `attempt`: exactly 1.
- `executor`: exactly
  `a Claude Code cloud session on behalf of the owner, on two cloud containers whose inventories are recorded`.
- `protocol_commit`, `protocol_path`, `protocol_sha256`: the preregistration,
  pushed alone; `source_commit`: the implementation, a descendant of it that
  did not change the protocol file.
- `launcher_path`: this `launch.py`; `marker_path`: where RUN_ATTEMPT.json goes.
- `spinit_path`: a committed file named `spinit` containing `set num_threads=1`.
  The launcher gives its folder to every run as `SPICE_SCRIPTS`.
- `inventory_a_path`, `inventory_b_path`: the committed inventories of the two
  machines, written by the `inventory` command on each machine.
- `source_sha256`: every frozen file — launcher, start file, runners, decks,
  included netlists, kernel, configuration, analysis. After `source_commit`
  the only files that may differ are the manifest, the marker and the two
  inventories.
- `expected_workflows`: the CI workflows that must be green on `source_commit`.
- `jobs`: how many runs a machine executes at the same time (1 to 16).
- `scenario_order`: the distinct scenario names, in the order of the round-robin.
- `budget_s`: at most 14 400. The bound that must fit it is, summed over the
  two machines, `sum(timeout_s + 10) / jobs + max(timeout_s + 10)`.

Fields of each element of `runs`:

- `id` (unique), `machine` (`a` or `b`), `scenario`: the i-th run of a
  machine must belong to scenario `scenario_order[i mod n]`.
- `deck`, `runner`: frozen files; `argv`: an argument list whose first two
  elements are `{python}` and `{repo}/<runner>`; never a shell command.
- `estimate_s`, `timeout_s` (at least the estimate).
- `required_outputs`: files that must exist and be nonempty after exit 0;
  `diagnostic_logs`: simulator logs searched for fatal messages.
- `noise_fingerprint`: one of the required outputs, a file of 64 hexadecimal
  digits written by the runner (see [README](README.md#noise-is-not-replayable)).
  Mandatory for a registered run.

Statuses that a run can have in STATE.json: `started`, `complete`,
`failed-never-rerun`, `time-limit-never-rerun`,
`lost-started-before-restart-never-rerun`. A run of the manifest without a
record never started. `complete` means that the process ended with status 0,
its outputs exist and its logs carry no fatal message — not that a prediction
held.
