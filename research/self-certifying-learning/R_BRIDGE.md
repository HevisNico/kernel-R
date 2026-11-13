# R bridge: evidence and proof obligations

This is a source-level bridge plan, not a completed R instantiation. The
abstract package remains independent of R and Mathlib. A future adapter
should import the native and circuit results separately.

## What the refresh evidence actually supplies

The circuit [verdicts](../circuit/VERDICTS.md), P15, report seven relapses at
22 or 23 periods under 0.1 TΩ, with observed steps 1.288 mV and a band of
0.99 dose. P17 and P18 separately report noisy and mismatch variants.

Under an ideal steady-cycle balance, the nominal voltage figures suggest an
average loss around 1.288/23 to 1.288/22 mV per period, roughly 0.056–0.059.
That is an **inference for calibration**, not a deterministic upper bound on
loss between probes, nor a conversion into the abstract service reserve.
The period and voltage-to-log-gain map also need explicit definitions.

The repository already distinguishes agreement from certification. Its
[bridge application](../circuit/BRIDGE_APPLICATION.md) reports zero of 200
ports in the certified domain. The [cumulative results](../circuit/bridge_check/CUMULATIVE_RESULTS.md)
report 69 inside under estimates, with no count disagreement there, but
explicitly retain zero certified ports. Missing original waveforms,
peak-based proxies, limited threshold measurements, nominal calibration and
an unestablished scalar read equation prevent using those estimates as
universal premises. This follow-up does not change those historical results.

## Four correspondences to prove

| Existing result | What it actually establishes | Required adapter work |
|---|---|---|
| [`stop_training_exists`](../recursive-learning/native/Training/TrainingLoop.lean) | A native hybrid run stops training with a firing gain; counts, queue, rest state and observational uniqueness are included | Relate each abstract write to a native silent pulse and the actual dose; prove progress and availability from native guards; retain the extra execution/uniqueness conclusions rather than discarding them |
| [`needAlong_of_cumulative_tolerance`](../recursive-learning/native/Search/VariableNeedTolerance.lean) | An exact silence/firing count under a centered gain ladder, cumulative error, threshold error and post-target monotonicity | Transfer calibrated state and error bounds into the integer abstraction with justified scaling; preserve the threshold lattice alignment and the `1/8000` charge term |
| [`trained_read_exists`](../recursive-learning/native/Training/JointRead.lean) | Two trained ports yield a read event in the specified timing window, with complete-run agreement | Relate the abstract lower service reserve to the two-port read specification; prove hybrid timing, recovery and scheduling correspondence; the scalar lower-bound theorem alone cannot supply the read window |
| [`robust_cost_nondegradation`](https://github.com/HevisNico/kernel-R/blob/b078b1c3b80e3e8905a273baa2a316389a6ba715/research/reusable-controller/ReusableController/Selection.lean) | Reported improvement by at least 2*tau implies nondegradation of true cost under both report-error bounds | Define one physical cost model with sensing/trials/writes accounted for; establish report accuracy and align the adoption decision, instead of substituting the abstract write count for true cost |

The existing [circuit-to-need lemmas](../circuit/lean/CircuitNeed.lean) already
spell out sensor-window, current-transfer residual and state-linkage terms.
They are the appropriate starting point; a fitted refresh period cannot
replace those assumptions.

## Interface the adapter must discharge

1. State map from the native/circuit state to a conservative service reserve,
   with explicit units and a sound observation lower bound.
2. A hard inter-probe loss bound, or a justified finite-horizon slew envelope,
   including temperature, fabrication, noise and leakage conditions claimed.
3. Minimum delivered dose, delivery time and saturation/capacity bounds,
   including leakage while the write is in progress.
4. The exact event correspondence: what is sensed, what counts as a write,
   which observation attempts cost resources, and when their timestamps apply.
5. A theorem connecting the native/circuit execution to `Delivers`, flow and
   generated phase contracts. Then instantiate service/cost results without
   assuming the desired physical correspondence in the conclusion.

A separate deterministic calibration campaign would need to record the
quantities required by these premises. A stochastic or nominal fit may guide
that campaign, but cannot certify every device in the fabrication box.
