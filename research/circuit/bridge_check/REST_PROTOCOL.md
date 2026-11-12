# Bridge hypothesis audit: rest-state diagnostic

This is a diagnostic of already known circuit designs, not an unseen-data
confirmation of the need theorem. The original `mc_2064`, port 1 disagreement
and the previous need-budget estimates are already known and will remain
unchanged. The original noisy trajectory is unavailable. A noisy replay
cannot identify its original rest state or establish a causal explanation.

Publish this protocol, `manifest.json` and `rest_probe.py` on GitHub before
running any of the listed simulations. Record the publication commit in the
run metadata. The manifest freezes source hashes, PDK revision, executable
hash/version and the ordered five-run list. No run is selected or repeated
according to whether it agrees with the theorem.

## Exact quantity and rule

The netlist declares `vr0 = 1.25 V`, `vunit = 0.5 V`, `tu = 20 us`,
`tper = 440 us`, `t0 = 4.1 us`. Its declared coordinate is

```text
q = 0.1 + (1.25 - Vq) / 0.5
q in [0.1, 0.1001]  iff  Vq in [1.24995, 1.25] V.
```

For every training pulse and the final joint read (periods 1 through 21),
sample at `k*tper + t0 - 1 ps`, immediately before the admission edge.
Interpolate linearly between saved solver points; save both bracketing
points and the unrounded value. Also sample 0.5 us before the edge as a
secondary diagnostic, never as a replacement for the primary sample.
Do not estimate the start state from the period's minimum voltage.

Report three numerical flags using the fixed guard `u = 0.000002` in model
units: `inside` if `[q-u,q+u]` is contained in `[0.1,0.1001]`, `outside` if
these intervals are disjoint, and `boundary` otherwise. Also report the
literal membership without the guard. The guard is an engineering diagnostic,
**not a proved solver error bound**. Numerical flags are not Lean certificates.
For the two deterministic nominal runs, report differences at the same dates
between maximum time steps 200 ns and 100 ns; do not tune the guard afterwards.

Record the first protection-latch rise and all subsequent rises per period,
the sensor entry/exit latch dates, stored and summing-node voltages and sensor
voltages. These extra signals provide context; they cannot turn voltage
proxies into calibrated log-gain or separate all parasitic currents.

## Scope, versions and stopping rule

Five runs: nominal tt/27 C at 200 ns and 100 ns; tt_mm/27 C with mismatch
seed 2064 without noise at 200 ns; two tt_mm/27 C runs with that mismatch
seed and noise at 200 ns. Each has the original 10 pulses per port and final
joint read. The two noise draws are new samples and need not match each
other or the original `mc_2064`. They are both retained regardless of outcome.

The original campaign used ngspice 42. These diagnostics use the available
Debian ngspice 44.2 binary, identified by hash in the manifest. Version change
is a limitation: even deterministic mismatch replay is not an exact archival
reconstruction. The SKY130 PDK remains pinned to the campaign revision.
The original netlist is not edited; the generated deck only adds saves,
explicit temperature/time-step settings and the existing noise/seed controls.

Each run has a 600-second timeout. Run every listed case once; report technical
failures rather than replacing them. A parser/instrumentation repair requires
a public amendment before another simulation, with the failed attempt retained.
Keep compressed raw solver output, generated decks, logs and hashes. No gain,
threshold, dose or `room` estimate is changed by this test.

If a replay violates the band, the scalar theorem does not apply to that
replay as stated. This is an applicability failure, not proof that rest
charge caused the old count disagreement. If it passes, the other hypotheses
remain unverified. Deterministic gain sweeps and current/charge measurements
will need their own frozen run manifest before launch.

## Runtime amendment 1, before retry

The five attempts under commit `c8439968e3516c3f51f5d03d66d65d0a1a6b9852`
all exited before transient analysis: the C runtime's `tmpfile()` tried an
unavailable temporary directory. Their decks, logs and metadata are retained.
No physical outputs were produced. `manifest_v1.json` preserves the initial list.

The retry uses the same five configurations with names suffixed `_retry1`.
A small audited adapter makes `tmpfile()` honor a writable `TMPDIR`; its C
source and binary hash are recorded. A minimal central `spinit` sets one
thread and avoids paths to uninstalled optional XSPICE models. The existing
local `.spiceinit` compatibility settings are checked byte-for-byte.
No solver, device, noise, sample-date or acceptance rule changes. The runtime
adapter was tested on temporary-file I/O, without simulating a circuit.
The amended code and manifest must be pushed before retrying.
