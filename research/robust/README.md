# Robust prepared chains: drift, bounded noise and pulse amplitude

This research module is maintained in the kernel-R repository. It contains the
code, written theorems, certificates and numerical evidence for robust prepared
chains with bounded drift, disturbances and received-amplitude variation.

It originated in a review and extension of `robust_noise_drift.zip`.
[ORIGIN.json](ORIGIN.json) records that delivery's provenance; the
[original delivery README](reference/README_OFFLINE_DELIVERY.txt) preserves its
wording. The sections below describe this module as it is used in the repository.

## Result and scope

The local prepared B→A theorem covers the eight combinations of epsilon in
{0.003,0.1} with (nu,alpha) in {(0,0),(.002,0),(0,.09),(.0015,.05)}.
The independent integer replay checks 36 sufficient strict inequalities per
point, including invariance during arbitrarily long initial silence.

`THEOREM_N.md` gives a written induction for **every finite prepared chain**:

- N cells, K >= 3N+1 source inputs;
- source period T >= 7.5 + 0.5(N-1), default max(8,7.5+0.5(N-1));
- cell i (zero-based) emits K-3(i+1) pulses, and the root emits K-3N;
- every cell receives exactly three full ERROR doses, keeps b unchanged, and
  its isolated frozen probe changes from 0/8 to 8/8;
- K=3N+8 leaves eight root emissions.

This schedule explicitly budgets accumulated latency and edge-delay uncertainty.
It is **not** a robustness proof for the original fast period-4 N-cell packet
protocol. It assumes the prepared state, unit-support canonical emissions with
bounded received amplitude, lossless links with delays in [.3,.4], and bounded
measurable histories. Entry from birth and arbitrary waveform/noise models are
outside scope. There is no complete Lean formalization in this package.

## Reproduce

The certifier, verifier and rational chain contract use only the Python standard
library. Numerical testing additionally needs the versions in requirements.txt.
Run these commands from this module's directory:

```sh
# From the repository root:
cd research/robust
python -B -m unittest tests test_regressions -v
python -B verify.py results/eps0.1/nu0.002_alpha0.json
python -B chain.py results/eps0.1/nu0.0015_alpha0.05.json --n 32 --k 104
python -B validate.py                 # full numerical campaign, traces and refinement
python -B validate.py --verify-record # source/runtime/trace correspondence only
```

`python -B validate.py --quick` is a two-case development smoke test. It writes
its own report with `quick=true`; it is not the full campaign.

The full campaign has 53 chain cases: all eight local points under four history
families, depth cases N=1,3,4,8,16, and an oscillatory N=32 case. Histories include
both constant box corners with signed noise, independent smooth oscillations,
and known discontinuous coefficient switches. Link delays alternate between
both endpoints. Initial coordinates include both ends of the prepared box.
Every tested cell gets eight frozen probes before and after learning. Selected
cases repeat with tighter solver tolerances and a smaller maximum step.

## What the tests actually check

`simulate_events.py` implements the differential equations independently of
`bounds.py`. DOP853 localizes charge guards and integrates dose/noise only up to
their true numerical exit; known pulse/history discontinuities split the solve.
It checks energy dynamically and retains full continuous state between inputs.
Analytic tests compare constant-rate exit times and signed-noise doses against
closed forms, including simultaneous auxiliary exits.

`validate.py` asserts exact emission counts, pulse correspondence, minimum gaps,
input-state sections, firing latency windows, complete first-three doses and
zero later doses, the integrated dose identity, unchanged recovery, terminal
modes, sampled charge/energy bounds, and before/after probes. The numerical
acceptance tolerance is 3e-8; a floating result can lie just outside an exact
certificate interval by this tolerance. The maximum such distance is recorded.
Sampled extrema are not certified continuous extrema. Successful simulations
cover only their recorded histories and do not establish the universal theorem.

The report is evidence/validation.json; full state/event traces are in
 evidence/traces.jsonl.gz. The report locks code, written proof, certificates,
Python/NumPy/SciPy versions and trace bytes. Source mismatch is a refusal.

Documentation-only updates are recorded in the validation reports' separate
`documentation_revision` metadata. Their source maps match the current README;
the archived delivery README preserves the exact as-run text and hash. Such a
documentation refresh does not rerun or change the numerical campaign.

## Review fixes

- The verifier now requires the complete source manifest, exact model/section/
  protocol/conclusion metadata, and full obligation definitions. The previously
  accepted tampering cases are regression tests.
- Corrected the shifted initial value in comparison lemma C1.
- The original Euler simulator and evidence are retained for diagnosis only.
  They over-integrate the last ERROR step before snapping the charge to its
  endpoint. They cannot validate the claimed dose intervals.
- Authentic execution of the verifier and imports remains a trust assumption.
  Self-contained hashes are source correspondence checks, not signatures or a
  sandbox for running arbitrary uploaded Python code.

The original written hybrid comparison argument, the independent arithmetic
replay, the N-cell induction and floating-point testing are distinct layers of
evidence. Neither green tests nor hashes turn them into full formal semantics.
