# Campaign 6 of the learned AND-OR circuit: amendment 1 to the stopping rule

Pushed alone on `research/learned-dnf-circuit-campaign-6`, after the stopping rule (`STOPPING_RULE.md`, commit
`2e26910`, SHA-256 `773a7811b530d4f31aeebe26be0e704ebe661710bc0f8efefc78eef05d5b035d`) and after the development
batch ran, **before any `k` was computed under the rule**. It is the owner's decision of 2026-11-18, taken before
the owner or either coordinator had seen any eligibility (section "What was known").

## What happened

The batch ran at the marker `085c6bc` (machine `a`: evidence at `d9e431b`; machine `b`: evidence at `88a34de`). The
batch's prediction code, exactly as pushed, stops with an error before it reaches any gate, so it computes no `k`:

- `predict6.py predict` calls campaign 5's frozen `predicted.instance` on each measured instance. On seed 7709, its
  fit `predicted.geometric` finds no solution and the code raises a `TypeError`.
- The cause: this fit tries offsets `h` from 0.05 of the firing level upwards, and needs every single-port read to lie
  above `h`. On 7709, the two single-port reads of cell `b` at stage 0 are at 2 923 (cell units, `theta = 100 000`),
  below 5 000. Under `MAPPING_U.md`, a single-port read at stage 0 is `g = d (K - s*)`, which is near 0 when a cell's
  `s*` is near `K`. The nominal cell of the acceptance test did not come near this edge.
- On every other instance whose two calibration decks completed, `predicted.instance` runs. (7707 is not measured:
  its guard-off calibration deck did not complete.)

The stopping rule says that `k` is computed by the code as pushed, and that a defect found afterwards changes neither
`k` nor the decision. It does not say what to do when that code computes no `k`.

## The rule added

**An instance on which the batch's prediction code raises an error is not eligible**, as an instance whose run does
not complete is not eligible. It enters `k` as not eligible, and its error is reported.

`k` is then computed by the batch's code at the marker `085c6bc`, unchanged, through one added wrapper:
- The wrapper catches only an error raised, for one instance, by the call of campaign 5's `predicted.instance` in
  `predict6`. That instance is then recorded as not eligible, with the error's type and message.
- It adds no fallback fit, and it skips no part of the frozen code.
- It comes with a test that reproduces the 7709 case.
- It is reviewed by both coordinators and pushed alone, with its SHA-256, before it runs. It changes nothing else.

The batch's report cites the marker, and this one declared change.

This rule can only lower `k`. So if the decision is a go, it would also be a go with 7709 eligible.

For a campaign 6, if any: under `MAPPING_U.md`, this failure occurs whenever `K - s*` of a cell is below about
5 000 / `d`, close to half a stage. So it can recur on any seed. The preregistration must either keep the report-only
geometric fit from blocking an instance, or state this rule from the start.

## What was known when this was decided

- The statuses of the batch's 90 runs: 82 complete, 1 failed (7707's guard-off calibration deck, where ngspice found
  no operating point), and 7 not started (the runs of 7707 that needed it).
- The error above, and the two stage-0 reads of 7709's cell `b` that cause it.
- That every other instance with both calibration decks complete passes `predicted.instance`.

No gate had run, and no `k` had been computed under the rule.

**Declared:** while locating the error, before this rule was asked for, the campaign director ran the per-instance
prediction in memory, on the Python side only, with no gate and no Lean. He sent its eligibility verdicts and a
hypothetical decision to the coordinator, at 16:19 UTC. The coordinator read them only after the owner had decided.
The owner had not seen them. They are not a `k` under the rule, and they are reported as they were, with the batch's
report.
