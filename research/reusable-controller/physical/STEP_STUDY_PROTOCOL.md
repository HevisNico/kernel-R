# Deterministic integration-step study S1

**Status: NOT_STARTED.** No refined-step simulation has been run here.
The pinned ngspice binary and SKY130 models are absent. These rules must be
published before the first run; they specify a comparison, not a measured result.

## Frozen runs and runtime

Use #109 source `7ded279f103dab5beb6c1c671f1acbdf4cff18c0`, ngspice 42 binary
SHA-256 `820658317b0b54035208da41936fd6871ce924036e5ea4113a4168b821b7fc45`,
and SKY130 commit `1232782c1b9fab3aacda74d67ce7c92bf7da8105`. Preserve its
startup/compatibility files, solver tolerances, netlist, temperature 27 C,
pulse schedules, current channels and compact-trace retention.

Select the nominal cell and the first two calibration mismatch identifiers,
5001 and 5002, by identifier rather than by residual. Run both train and leak
modes for each. This is six fixed cases, not a search for a favorable subset.
All six runs are noiseless, as in their source calibration records.

For every case run maximum solver steps **200 ns, 100 ns and 50 ns**. Repeat
the 200 ns baseline once, before its refinements, to test deterministic replay:
**24 scheduled simulations** in total. Preserve other solver settings and
output sampling; changing the maximum step must actually affect the transient
analysis setting, not merely resample an unchanged saved trace. Record both.
Do not introduce 25 ns runs, change samples or alter solver tolerances after
viewing results without a separately published amendment.

The baseline duplicate must reproduce the physical read/current summaries
byte for byte, excluding timing/runtime metadata. If it does not, stop and
report the discrepancy before attributing differences to integration step.
Record the source #107 nominal/calibration run identities as well as these
new instrumented-run identities; added current logging is explicit.

## Measurements and analysis

Retain raw solver timestamps and both output mirror currents, along with the
original state/read/FIRE/steering signals. For every pulse integrate current
through the full window and the early 0.75 window using the same extraction
rule, interpolation and normalization as #109. Record endpoint placement,
point counts, peak/early values and all guard results. Hash deck, binary, PDK,
startup files, extractor and compact trace. Private storage must retain the
traces, not only the public scalar summaries.

At every step recompute the original eps3 statistic, including its full-silent,
early-silent and eligible-early-FIRE components. Keep kappa and MG=1e-4 fixed.
Report the fitted D/DE at each resolution, and also evaluate residuals with
the 200 ns offsets frozen: a refit must not conceal a change of absolute gauge.
Missing reads, different pulse alignment, an unsupported early FIRE, a guard
failure or changed FIRE classification is reported explicitly, not paired away.

For each fixed case/port report eps3 at all three steps, the absolute changes
200-to-100, 100-to-50 and 200-to-50 ns, component changes, offset changes,
current integrals and count/FIRE-time changes. The prespecified numerical
sensitivity check passes only if every comparison is evaluable, guards and
FIRE classification are unchanged, and every absolute eps3 difference is at
most 1e-4. Report failures individually and the maximum across all comparisons.
Do not enlarge the margin or remove a case after seeing its result.

A successful check supports the statement:

> Across the six fixed calibration cases and three tested maximum steps,
> the observed eps3 sensitivity to step refinement was at most 1e-4.

It does **not** establish that the integration error relative to the exact
continuous-time solution is bounded by 1e-4. Convergence between finitely many
settings can share a common bias. It also does not establish behavior for all
37 test ports or all noisy repetitions. The margin remains an empirically
supported allowance unless an independent numerical error enclosure is proved.

## Readiness and next stage

Restore and authenticate the pinned runtime/PDK, implement and review the
instrumented step override, then publish its hashes before execution. No
alternative runtime is silently accepted; a different binary needs its own
amendment and deterministic preflight.

Only after this study is reported should the frozen-cohort noisy repetition
campaign start. Its separate protocol and statistical analyzer are prepared in
REPETITION_PROTOCOL.md and repetition_plan.py; their status is also NOT_STARTED.
Noise-seed plumbing and endpoint extraction remain explicit implementation
blockers. A schema or synthetic test is not a circuit simulation.
