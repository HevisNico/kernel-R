# V5: service inside a fixed boundary

**The registered batch completed once; S1–S6 and all local saved-evidence
checks passed. Its 50 authorized evidence files are now published byte for byte
in dedicated commit
[`d2a815f07113ec92a392a9b08da3bef9a26aa90d`](https://github.com/HevisNico/kernel-R/commit/d2a815f07113ec92a392a9b08da3bef9a26aa90d),
also identified by [POSTRUN_CHECKS.json](POSTRUN_CHECKS.json).
Do not rerun the batch.** The protocol
was published before implementation and before the twelve new scenarios were
generated. The successful exact-head CI snapshot and attempt marker were
published in `975fefb224787baca8e941f38ba4d00ccb24bf5f` before execution.

The published evidence includes the [unedited generated report](run-v5/REPORT.md),
[full summary](run-v5/summary.json), [oracle outputs](run-v5/oracle.json),
[recorded scenarios](run-v5/scenarios), [27 compressed raw traces](run-v5/traces),
metadata, logs and exit status. The previously published
[aggregate RESULTS.json](RESULTS.json), [ORACLES.json](ORACLES.json) and
[PUBLIC_REPORT.md](PUBLIC_REPORT.md) remain unchanged.
[PENDING_EVIDENCE.json](PENDING_EVIDENCE.json) retains its historical filename
and the exact 50 authorized paths, sizes and SHA-256 fingerprints; the current
publication status and raw commit are recorded in POSTRUN_CHECKS.json. No trace
was regenerated, recompressed or replaced for publication.

All twelve new early-refill and matched-prudent cases stayed safe. **The twelve
observed early-refill costs are within 4.2% of their restricted omniscient
oracles:** median excess 3.75%, maximum 4.19% (exact recorded maximum 4.188288%).
Only 2/12 were below 2.82%. The **2.82% statement applies to the already explored
known replication**, which reproduced 5671 versus 5516, or 2.810007% excess; it
is not a bound for every physical trajectory or an unseen prediction. These
gaps value terminal inventory at zero and do not require equal final reserves:
in the known case, the policy retains 440 versus the oracle's 330, with 110
lost to oracle saturation. Part of the comparison is unused stock, so the gap
must not be attributed solely to better decisions.

Against the matched safe-prudent policy, observed seeded cost savings range
from **0% to 13.34% (about 13%)**. Seed2026111304 costs 2800 versus 3231, a
431/3231 = 13.3395% saving; seed2026111303 has no saving (8521 versus 8521).
Thus one of twelve cases has zero improvement. These empirical counts have no
pass threshold or statistical population guarantee. The outside-boundary
control refused at 661. This is a fixed-boundary discrete-model result, not
transistor validation.

V5 removes the optimistic variation law. It proves the safety of early refill
and the matched safe-prudent policy. The prior study's identical-action negative
result stays in #119; the separate economic sweep is in #121. Neither is a new
v5 confirmation or evidence that every possible learning mechanism is useless.

## Formal scope

[Model.lean](Model.lean) contains 35 explicitly named theorems. The audit checks
271 declarations, including 137 theorem declarations with generated ones
included; it requires 19 central theorems by name and permits only `propext`,
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
- one or two ticks per action, bounded writes and abstract cost at most `11N+1`,
  including a last wait started before N and shortened by the terminal readout;
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

## Oracle, terminal inventory and evidence checks

The prior cost 5671 versus 5516 is an exploratory result to reproduce, not an
unseen prediction. The exact gap is `155/5516`, about 2.810%. The oracle knows
future plant/noise, may trade dose saturation for fewer probes, values terminal
inventory at zero and optimizes only the declared one-command/Ready-at-next-probe
family. No claim of 2.82% excess is made for the twelve new scenarios.

The known-scenario comparison does **not** impose equal final inventory:

| Known replication | Cost | Final reserve | Saturation loss |
|---|---:|---:|---:|
| Early-refill policy | 5671 | 440 | 0 |
| Restricted omniscient oracle | 5516 | 330 | 110 |

Consequently, the reported gap is a result for the registered objective, not a
terminal-stock-adjusted economic inefficiency. Costs, terminal reserves and
saturation are published separately for every case.

The same convention matters in the separate exploratory
[#121 capacity/price sweep](https://github.com/HevisNico/kernel-R/pull/121).
Its [frozen results](https://github.com/HevisNico/kernel-R/blob/14df7155c1112f80da40ec16d25e6b67e4592aff/research/economic-sweep/RESULTS.json)
show, for the jump case with C=6600 and probe/write prices 1000/100, early refill
costing 119400 versus oracle105000: a 13.71% gap. Early refill ends at reserve
3520, while the fixed/optimistic policies end at 440. Part of the interpretation
therefore concerns retained terminal stock, which has zero value in that
objective; the gap is not an isolated measure of learning inefficiency. A future
v6 must preregister its inventory convention, such as equal terminal reserve or
an explicit residual-stock value, before using this comparison to assess a
learning benefit. The existing v5 and sweep objectives/results remain unchanged.

The completed batch contains the known replication, twelve fixed seeded
scenarios, matched safe-prudent runs and one outside-boundary control. All cases,
including outside-boundary service loss, are retained. Two independent frozen
dynamic programs check oracle costs. The saved-row audit reconstructs decisions,
plant chronology, sensor bounds, carry, costs, refusal and exact registered seed
draws without running another controller. Six saved-evidence mutations are
rejected after recomputing valid hash chains. All registered source files remain
hashed and unchanged.

The new [saved-publication wrapper](checks/verify_saved.py) checks the manifest
against its published authorization commit
`f067f1cf1b2dc47ea33dcdf652995b2d794f10c4`, requires exactly the 50 authorized
files with matching byte counts and SHA-256 digests, rejects missing/extra files
and symlinks, and verifies the dedicated commit contains only those 50 additions.
It also compares the committed blobs with the authorized hashes and local bytes.
Only after these checks does it call the frozen saved-evidence verifier.

Validation includes the Lean build/axiom audit, four isolated synthetic tests,
five paired semantic proof mutations and six saved-trace controls. The new
wrapper adds **16 tests using temporary repositories**, covering byte corruption,
missing/extra files, path escape, symlinks, altered manifests, false publication
metadata and non-dedicated commits. The fixtures do not modify real evidence or
execute registered scenarios. Remote CI now requires this saved-evidence path;
it cannot silently fall back to preparation if published raw files are missing.

## Recorded execution procedure — do not relaunch

The commands below document the completed procedure. The persistent attempt
marker already exists: **never invoke the registered runner again**. Use the
read-only verification commands against the published saved evidence.

Pinned versions: Lean4.35.0 and Python3.12. Preparation used:

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

Verification is read-only with respect to the registered files and never
replays the controller. From `research/fixed-boundary-v5`:

```sh
python3 -B -m unittest discover -s checks -v
python3 -B checks/verify_saved.py
```

This first authenticates the exact publication, then checks the saved trace and
report, both oracle solvers on saved arrays and the six semantic controls through
the frozen verifier. CI never calls the registered runner or regenerates raw
traces. The owner handles all merges; this PR remains draft pending review and
all final-head CI checks.
