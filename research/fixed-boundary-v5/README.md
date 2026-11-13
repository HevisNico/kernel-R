# V5: service inside a fixed boundary

**Preparation complete; registered batch not executed.** The
[protocol](PREDICTION.md) was published in
`6361398d04cf6cbf7c382b4955b879f6025a07a3` before v5 implementation and before
any of its twelve seeded scenarios were generated or inspected. The known v3
case is explicitly an explored replication. The fixed boundary is H=150,
service100, dose220, capacity660, latency1, with bounded sensor errors.

V5 removes the optimistic variation law. It proves the safety of early refill
and the matched safe-prudent policy. The prior study's identical-action negative
result stays in #119; the separate economic sweep is in #121. Neither is a new
v5 confirmation or evidence that every possible learning mechanism is useless.

## Formal scope

[Model.lean](Model.lean) contains 33 explicitly named theorems. The audit checks
266 declarations, including 132 theorem declarations with generated ones
included; it requires 17 central theorems by name and permits only `propext`,
`Classical.choice` and `Quot.sound` as axioms.

The same observation-only kernel is proved and called by [Bridge.lean](Bridge.lean).
It receives policy, reserve/rate reports, delivery flag and prior certified
carry. It never receives true reserve, future leakage, scenario names or seeds.
The proofs cover:

- bounded-error fresh lower/upper enclosure, H-based carry and early-refill
  saturation avoidance;
- the exact early/prudent action certificate, including the wait-length formula;
- service both before and after delivery, and preservation of Ready;
- a recursively constructed physical execution using the actual kernel,
  safe exact-length prefixes covering every horizon and no refusal inside H;
- one or two ticks per action, bounded writes and abstract cost at most `11N+1`;
- immediate kernel refusal on a measured lower rate above H, and soundness of
  that violation; the rejected carry is discarded;
- arithmetic showing that the already known 5671/5516 cost ratio is below
  2.82% excess, and is **not** below 2.8% excess.

`Physics` supplies the fixed loss and sensor bounds; exact next-tick dose and
saturation are built into the canonical model. The theorem constructs its
execution, rather than assuming an already safe trace as a premise. These
premises still need external physical justification before applying the result
to a circuit. There is no runtime reauthorization inside the fixed boundary.

The Python scheduler/IO wrapper is tested and independently audited, not formally
proved as arbitrary Python execution. Outside H, Lean proves the measured
violation/refusal statement; persistent Python shutdown is checked in saved
trace evidence. It does not prove detection of every small or between-probe
excursion, nor continued service after the hard premise fails.

## Oracle and evidence status

The prior cost 5671 versus 5516 is an exploratory result to reproduce, not an
unseen prediction. The exact gap is `155/5516`, about 2.810%. The oracle knows
future plant/noise, may trade dose saturation for fewer probes, values terminal
inventory at zero and optimizes only the declared one-command/Ready-at-next-probe
family. No claim of 2.82% excess is made for the twelve new scenarios.

The batch will contain the known replication, twelve fixed seeded scenarios,
matched safe-prudent runs and one outside-boundary control. Every case and every
failure will be retained. Two independent frozen dynamic programs check oracle
costs. The saved-row audit reconstructs decisions, plant chronology, sensor
bounds, carry, costs, refusal and exact registered seed draws without running
another controller. Six saved-evidence mutations must be rejected after
recomputing valid hash chains. All registered source files are hashed.

Current validation comprises the Lean build/axiom audit, four isolated synthetic
tests and five paired semantic proof mutations. The unit fixtures do not execute
registered scenarios or shortened pilots. The six saved-evidence controls cannot
run until evidence exists; preparation CI success alone is not the experiment.

## Execution gate and reproduction

Use the pinned Lean 4.35.0 distribution and Python 3.12. Preparation:

```sh
cd research/fixed-boundary-v5
python3 -B verify.py --preflight --report validation.json
```

Publish the tested implementation. Before any registered scenario generation,
inspect #119 exact head `2cd95d2043ad2c964304a64178f3b7f1c377d671`: every workflow
and latest-attempt job must be completed/success. Publish their authentic
snapshot as `CI_GATE.json` and a durable `RUN_ATTEMPT.json` with attempt1,
protocol commit and tested implementation commit. Only after this marker is
published, from a clean checkout, invoke once:

```sh
python3 -B runner.py --run-once
```

The runner creates exclusive `run-v5`, stores full scenario arrays, gzip CSV
traces with append hash chains, journaled oracle results, metadata, error logs,
exit status and the unedited report. Gzip headers are deterministic (mtime0).
No existing attempt marker may lead to a relaunch after interruption. Preserve
all surviving evidence instead. Do not tune or revise sources after the batch.

After raw evidence is published, verification is read-only with respect to the
registered files and never replays the controller:

```sh
python3 -B verify.py
```

This checks the saved trace/report, both oracle solvers on saved arrays and the
six semantic controls. CI runs preparation checks until evidence exists, then
requires full saved-evidence checks. CI never calls the registered runner.
The owner handles all merges; this PR remains draft pending review and CI.
