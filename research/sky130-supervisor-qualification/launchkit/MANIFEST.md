# Future campaign manifest contract

No registered manifest is included during phase 1. Once the domain and
budget are qualified, preregister first, implement second, freeze the exact
source commit and its complete runtime dependency inventory, obtain green CI,
then publish a manifest and RUN_ATTEMPT marker. Do not generate new registered
scenarios during phase 1 to fill this document.

Required fields:

- `kind`: `registered`; the `synthetic` namespace is reserved for local tests.
- `campaign_id`: stable lowercase letters/digits/hyphens, never changed to
  evade a consumed claim; `attempt`: exactly 1.
- `protocol_commit`, `source_commit`: full Git SHAs, distinct and ordered by
  ancestry. `protocol_path` and `protocol_sha256` identify the frozen protocol.
- `marker_path`: repository-relative destination of RUN_ATTEMPT.json.
- `launcher_path`: repository-relative path of this exact launch.py.
- `source_sha256`: every frozen runner, deck, included netlist, startup file,
  scenario generator, configuration and repository-local imported dependency.
  Every listed file must equal its source-commit blob. The entire repository
  tree is also frozen after that commit except the manifest and marker.
- `expected_workflows`: nonempty list of workflow names required at the exact
  source SHA. Additional workflows actually present are checked too. Latest
  attempts and all jobs must be completed with success.
- `budget_s`: finite positive aggregate execution/termination budget, at most
  14400 seconds. The sum of all `timeout_s + 10` must fit it; the extra ten
  seconds per run reserve process-group termination. Estimation alone cannot
  authorize larger runtime limits.
- `runs`: nonempty machine-a and machine-b lists expressed as a single array.
  Each element has unique `id`, `machine` (`a` or `b`), frozen `deck` and
  `runner` paths, `argv`, positive `estimate_s`, and `timeout_s` no smaller
  than that estimate. `required_outputs` is a nonempty list of run-relative
  regular files that must exist and be nonempty. `diagnostic_logs` lists the
  simulator stdout/stderr paths; it is nonempty for registered runs. The
  estimates include noise factor, initialization,
  readout/output overhead and reserve. Their sum must fit the timeout envelope and its cleanup allowance must fit
  the budget. A timeout is a consumed incomplete attempt, never a relaunch.

`argv` is an argument array, never a shell command. Its first token is
`{python}` for a registered campaign. Direct `{ngspice}` is permitted only
in synthetic fixtures. A Python runner's second token must be
`{repo}/<runner path>`. Available substitutions are `{repo}`, `{out}`,
`{python}`, `{ngspice}`, `{pdk}` and `{deck}`. The launcher creates `{out}`;
the runner should put its exclusive raw output under `{out}/evidence`.
No `shell=True`, shell expansion or environment-supplied command is used.

The registered runner must implement the reviewed physics/kernel execution,
verify final waveform time, required vectors and event inventory after every
simulator process, write all intended raw vectors and observed decisions,
preserve all failures,
explicitly price preparation, and distinguish preparation from requested
service. This kit does not supply that implementation or prove its semantics.
It controls execution identity, launch chronology and preservation only.

The owner may set different filesystem paths on the two machines. Binary,
PDK, Python/numpy, source/manifest/protocol identity and machine assignment
must match. Each machine gets only its assigned run IDs; the claim branch is
bound to the protocol-content hash and machine, not to a campaign label or
local directory.
