# Two-sided rest tolerance, phase 1

## Where the current premise enters

The references below are pinned to the source reviewed on main at
[`27ba71a`](https://github.com/HevisNico/kernel-R/tree/27ba71a50d88c58f2fa453362a633e3374762fb5).

| Source | Exact use of the premise |
| --- | --- |
| [`Training/StopLearningLatency.lean:452–455`](https://github.com/HevisNico/kernel-R/blob/27ba71a50d88c58f2fa453362a633e3374762fb5/research/recursive-learning/native/Training/StopLearningLatency.lean#L452-L455) | `readyPulse_from` separates the initial-charge residual as `(q0 - 1 / 10) * exp (-(1 / 2) * t)`. |
| [`Training/TrainingLoop.lean:45–50`](https://github.com/HevisNico/kernel-R/blob/27ba71a50d88c58f2fa453362a633e3374762fb5/research/recursive-learning/native/Training/TrainingLoop.lean#L45-L50) | `pulseFires_of_peak` assumes `1 / 10 ≤ charge` to make that residual nonnegative at time 1. |
| [`Search/VariableNeedTolerance.lean:12–16,33–59`](https://github.com/HevisNico/kernel-R/blob/27ba71a50d88c58f2fa453362a633e3374762fb5/research/recursive-learning/native/Search/VariableNeedTolerance.lean#L33-L59) | `NeedAlong` quantifies over `1 / 10 ≤ c` and `c ≤ 1 / 10 + 1 / 10000`. `needAlong_of_cumulative_tolerance` delegates to `needIs_of_tolerance` at lines 49–52 with `+ 1 / 8000` in its common room at line 39. |
| [`Search/NeedTolerance.lean:67–103`](https://github.com/HevisNico/kernel-R/blob/27ba71a50d88c58f2fa453362a633e3374762fb5/research/recursive-learning/native/Search/NeedTolerance.lean#L67-L103) | `needIs_of_tolerance` uses `level - 1 / 10 - 1 / 10000` for silence at lines 74–93, bounds its log shift by `1 / 8000`, and uses `level - 1 / 10` for FIRE at lines 94–103. |
| [`Search/AsymmetricNeedTolerance.lean:15–49,56–93`](https://github.com/HevisNico/kernel-R/blob/27ba71a50d88c58f2fa453362a633e3374762fb5/research/recursive-learning/native/Search/AsymmetricNeedTolerance.lean#L15-L93) | `needAlong_of_peak_bounds` uses `decay_upper` at lines 24–25 and `pulseFires_of_peak lo` at line 31. `resting_log_gap` at lines 36–49 supplies `1 / 8000` for `needAlong_of_asymmetric_cumulative_tolerance` at lines 66 and 77. FIRE has no legacy rest charge cost. |
| [`PhysicalEvaluator/Envelope.lean:23–34`](https://github.com/HevisNico/kernel-R/blob/27ba71a50d88c58f2fa453362a633e3374762fb5/research/reusable-controller/physical/PhysicalEvaluator/Envelope.lean#L23-L34), [`Asymmetric.lean:23–38`](https://github.com/HevisNico/kernel-R/blob/27ba71a50d88c58f2fa453362a633e3374762fb5/research/reusable-controller/physical/PhysicalEvaluator/Asymmetric.lean#L23-L38), [`ReadoutBridge.lean:18–24`](https://github.com/HevisNico/kernel-R/blob/27ba71a50d88c58f2fa453362a633e3374762fb5/research/reusable-controller/physical/PhysicalEvaluator/ReadoutBridge.lean#L18-L24) | `chargeBand` is an explicit premise alongside the two physical observation implications. |
| [`cert_analyze.py:306–311`](https://github.com/HevisNico/kernel-R/blob/27ba71a50d88c58f2fa453362a633e3374762fb5/research/circuit/certification/cert_analyze.py#L306-L311), [`uncond_amend1.py:120–131`](https://github.com/HevisNico/kernel-R/blob/27ba71a50d88c58f2fa453362a633e3374762fb5/research/circuit/certification-unconditional/uncond_amend1.py#L120-L131) | The former emits “a rest state is outside the band”. The status-3 amendment carries that refusal forward and subtracts `1 / 8000` from the common room. |
| [`asymmetric_check.py:77–95`](https://github.com/HevisNico/kernel-R/blob/27ba71a50d88c58f2fa453362a633e3374762fb5/research/reusable-controller/physical/asymmetric_check.py#L77-L95), [`ASYMMETRIC_PROTOCOL.md:15–29,67–77`](https://github.com/HevisNico/kernel-R/blob/27ba71a50d88c58f2fa453362a633e3374762fb5/research/reusable-controller/physical/ASYMMETRIC_PROTOCOL.md#L67-L77) | A1 checks `0.1 <= c_pre <= 0.1001` at line 86, subtracts `1 / 8000` for silence at line 84, and charges zero for rest on FIRE at line 85. |

## Scalar proof

Write `lo = delta_lo` and `hi = delta_hi` for the total distances from
`rest = 1/10`. For a charge in `[rest - lo, rest + hi]`, the score
difference is exactly `(c_pre - rest) * exp(-t/2)`. The exponential lies
in `(0, 1]` for `t ≥ 0`, so `read_score_error` bounds the difference by
`[-lo, hi]` over the whole read window. The silence check bounds all
times using monotonicity of the nominal pulse response on `[0, 1]`.
The FIRE check uses time 1 as a witness.

At FIRE level `L ≥ 19/20`, let `H = L - rest ≥ 17/20`. Apply
`log(x/y) ≤ x/y - 1` to the ratios `H/(H-hi)` and `(H+lo)/H`.
If `0 ≤ hi ≤ 1/20`, then `H-hi ≥ 4/5`. For `lo ≥ 0`, the other
denominator stays at least `17/20`. The response normalization cancels.
Consequently the log-gain allowances are `(5/4)*hi` for silence and
`(20/17)*lo` for FIRE. Use their maximum in the strict symmetric room,
or pay them separately with strict silence and inclusive FIRE.

`legacy_symmetric` and `legacy_asymmetric` recover the original theorem
statements at zero expansion of the original band. In those corollaries
`lo = 0` and `hi = 1/10000 + 0`; `(5/4)*(1/10000) = 1/8000`.
Setting both *total* distances to zero gives the exact-rest special case.

`observed_training_count_a1` applies the scalar theorem at the lower and
upper detection levels and proves the prefix shape `false^m ++ [true]`
and the count `m`. The write interpretation uses one write per silent
read and zero on FIRE. `status3_implies_a1_rooms` and the symmetric gain
bounds imply the directional hypotheses. The finite result uses the gain
prefix only. Physical gain transfer and soundness/completeness of the
detection envelopes are explicit hypotheses. The native hybrid execution
and its rest-state invariant retain their original scope.

## Prospective Python rule

`status3_delta.certify` and `rule_a1_delta.certify` take an ordered port
prefix and exact decimal strings or rational inputs. The input carries
the existing normalized log-gain reconstruction, including the FIRE
correction, and a conservative pre-read charge enclosure. The routines
apply the per-read endpoint radii `MZ + eps_kappa * fired`, `+eps3` on
initial gain, `+2*eps3` on cumulative gain, and
`ell = h3 + 2*max(noise_sup_V) + MQ`. Supply `base_a` with its initial
allowances already included. The symmetric rule uses the largest
absolute deviation with both endpoint radii at each nonzero prefix
index. This can be more conservative than the frozen status-3
projection. Both prospective rules require the complete predicted
prefix through `m`, including after an early observed FIRE. Count
agreement is reported independently of eligibility. Missing or invalid
required data produce a `ValueError`.

The prior readout reconstruction already subtracts the actual signed
pre-read term ([`cert_analyze.py:55–65`](https://github.com/HevisNico/kernel-R/blob/27ba71a50d88c58f2fa453362a633e3374762fb5/research/circuit/certification/cert_analyze.py#L55-L65)).
The new cost covers the effect of that initial condition on the *true
read score*. The supplied readout bounds must still cover any
measurement and transfer residuals, including uncertainty from
subtracting the measured pre-read term.

## Future preregistration proposal

1. Freeze the two distances and the units, charge conversion, sampling
   time and outward measurement allowance using an independent
   calibration set. Record the threshold floor and coefficient cap.
2. Before any test run, publish the exact rule and code commit, predicted
   need per port, complete prefix length, gain/threshold transfer
   assumptions, FIRE/steering guards and detection-envelope protocol.
   Pin the netlist, toolchain, condition grid, cell/noise seeds, and the
   handling of missing, invalid and refused reads. Include fresh cells
   so the first read is tested under the same published rule.
3. On new test runs, retain the charge enclosure and both room
   components for each port, including all refusals and contradictions.
   Record count agreement independently of eligibility. Freeze the
   analysis before examining test outcomes and use new confirmation
   data for any later rule revision.

**This proposal must NOT be used to re-certify layout v2.2 after the
fact, except as a declared exploratory reading with no change to its
published verdicts.** See the
[`C_REPORT.md`](https://github.com/HevisNico/kernel-R/blob/aa45b434699712db641a04cbfffdfcae98c52100/research/sky130-layout/v2.2/C_REPORT.md)
and
[`REST_DIAGNOSTIC.md`](https://github.com/HevisNico/kernel-R/blob/aa45b434699712db641a04cbfffdfcae98c52100/research/sky130-layout/v2.2/diagnostic/REST_DIAGNOSTIC.md).
Phase 1 runs proof and synthetic tests only.

## Check

From this directory, with Lean 4.35.0 and the locked Mathlib v4.35.0:

```sh
lake exe cache get
lake build
python -B -m unittest -v
python -B check_mutations.py
```

The audit checks the imported `RestTolerance` modules, including private
and generated declarations, with only `propext`, `Classical.choice`
and `Quot.sound` allowed. The mutation runner checks that removing
either rest cost or widening the upper cap with the old coefficient
fails at the relevant proof obligation or test assertion.
