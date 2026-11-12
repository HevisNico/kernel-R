# From a finite scalar certificate to evaluator precision

This checkpoint derives the discrete feasibility tolerance from a finite
physical-observation certificate. It also connects that evaluator to the
adaptive controller's non-degradation theorem for **computed pulse accounting**.
It is a conditional bridge and a replay of recorded simulation observations,
not a newly simulated physical adaptive feedback loop.

The general [adaptive controller](../ADAPTIVE.md) remains a controller that
adjusts its own search with proved safeguards, **with assumed evaluator
precision**. The specialization here replaces its separate accuracy assumption
with explicit scalar gain, threshold, rest-state and observation premises.
Those physical premises are not all established by the public CSV projection.

## Measured campaign entry: 37 ports

[campaign_check.py](campaign_check.py) independently recomputes the public
summaries from PR #109 at `7ded279f103dab5beb6c1c671f1acbdf4cff18c0`:
202 completed runs, 100 cells and 200 ports. Its pinned snapshot contains
1,035 files. Read CSV hashes, current/read row alignment, fitted residuals,
threshold brackets, eligibility and observed counts are checked. This is a
reanalysis of published simulated measurements, not a new simulator run or a
hardware measurement. Private compact traces are not re-extracted.

The amended `eps3` budget retains **37 ports**, with no count contradiction.
[CampaignData.lean](PhysicalEvaluator/CampaignData.lean) contains all 37 entries,
their recorded observation prefixes and exact rational numerical gates checked
by Lean. Published bounds receive outward padding of `1e-10`. The numerical
gates do not supply physical trajectories or discharge the transfer premises.
The independent Python reanalysis uses floating-point logarithms with a
`1e-10` comparison tolerance. Lean checks the resulting decimal budgets as
exact rationals; it does not certify the campaign's numerical integration or
replace that empirical residual calculation with interval analysis.

`eps3` is already a **logarithmic residual**. It is not an amplitude error to
feed through `epsilonPeak / (L - epsilonPeak)`. The campaign entry directly pays
`a = baseA + eps3` and `B = baseB + 2*eps3`, using each port's own enlarged
threshold budget `ell3`. [CampaignBridge.lean](PhysicalEvaluator/CampaignBridge.lean)
proves this transfer and connects the resulting certificate to exact counts,
zero feasibility tolerance, Ready and retained computed-cost non-degradation.
The evaluator and acceptance rule remain fixed.

| Campaign result | Value |
|---|---:|
| Original #107 eligible ports | 59 |
| Leak-scan update (`status1`) | 58 |
| Registered full-FIRE-current check (`status2`) | 0 |
| Amended early-current check (`status3`) | 37 |
| `eps3` range across all 200 ports | 0.000475776–0.001097527 |
| Ports exceeding the old illustrative `1e-4` log budget | 200 |
| Cells with both ports eligible under `status3` | 6032, 6077 |

The explicit two-port composition in
[CampaignExample.lean](PhysicalEvaluator/CampaignExample.lean) uses `t6032`
(needs 3 and 4), chosen
retrospectively as the lowest cell identifier with both ports eligible. The
former `t6004` preparation port fails the new budget: its conservative room is
about `-0.000854388`. Lean retains that failed inequality as a negative case.
Its matching observed count does not rescue certification. The earlier
`t6004` replay and hypothetical sensor budgets below remain historical
conditional examples; they are not validated by the new campaign.

The measurement boundary matters. Full and early current integrals use the
output transistor current independently of the main capacitor voltage. Their
logarithms are aligned to the voltage-derived readings by **two fitted offsets
per port/run**, estimated on silent reads. `eps3` is the largest full-silent
or early-read residual, plus the declared integration margin `MG = 1e-4`.
That margin is not a proved numerical solver error bound. The early FIRE
check stops at 0.75 and does not establish the final-quarter correction
`kappa`/`eps_kappa`. Full FIRE current is affected by the routing event.

The new measurements are noiseless, whereas the retained #107 observation
prefixes are noisy runs. A common mismatch seed and matching counts do not
prove that the residual transfers between these runs. Therefore
`CampaignTransferPremises` still explicitly requires its bound on **each actual
read**, the reference initial/cumulative bounds, resting charge and the two
physical detection envelopes. All 37 numerical entries use measured `eps3`;
none silently constructs those remaining physical premises. The chain is
connected conditionally, not an unconditional physical closed-loop theorem.

## Directional rule A1: 57 ports, original 37 retained

[ASYMMETRIC_PROTOCOL.md](ASYMMETRIC_PROTOCOL.md) and the new scalar theorem were
published in commit `8b11a5f5d2b6843bc6ca1f9ff0b82c30fa99f19d` **before the first
directional eligibility calculation**. This is a new retrospective rule; it
does not retroactively preregister the original test cohort.

The theorem requires an upper cumulative bound only before `m`, and a lower
bound only at `m`. The separate sufficient conditions are

```text
aSilent + BSilent + (20/17)*ell + 1/8000 < d0/2
aFire   + BFire   + (20/17)*ell          <= d0/2.
```

The FIRE condition permits equality and does not need the largest-rest-charge
penalty. The old symmetric theorem is recovered as a corollary.
[Asymmetric.lean](PhysicalEvaluator/Asymmetric.lean) proves the finite
certificate, exact first-FIRE decoding and controller contract directly from
these conditions. Every old finite envelope certificate embeds in it without
changing its observations or adding a physical hypothesis.

The transfer adds `eps3` to **both** initial bounds (`aSilent = aFire = baseA + eps3`)
and `2*eps3` to **both** cumulative bounds (`BSilent = baseBSilent + 2*eps3`,
`BFire = baseBFire + 2*eps3`), paying the initial and current read errors in each direction.

[asymmetric_check.py](asymmetric_check.py) follows the frozen A1 formula:
initial centering remains unchanged; only the cumulative budget is split by
direction and read index. It retains all applicable kappa errors, both endpoint
errors, the measured `eps3`, rest/steering checks and threshold bounds. Count
agreement is an outcome, not an eligibility filter. The full
[200-port table](asymmetric-ports.csv) reports both rooms and exclusion reasons.

The result is **57 numerically eligible ports, 20 added, zero original ports
lost, zero count contradictions**. [AsymmetricData.lean](PhysicalEvaluator/AsymmetricData.lean)
checks all 57 padded rational gates in Lean. The original `CampaignData` and
its 37-entry report are unchanged. The previously excluded `t6004` preparation
port now passes A1, while its failed symmetric gate remains recorded; these
are different rules, not a revision of the old result.

| Rule | Eligible ports | Count contradictions |
|---|---:|---:|
| Registered symmetric budget (#109 amended status3) | 37 | 0 |
| A1, declared before its calculation | 57 | 0 |

**None of the 11 wrong-count ports from #107 is among the 57.** The reproducible
[review report](ASYMMETRIC_REVIEW.md) lists their identities and decomposes all
20 additions: the largest old term was `a` for 12 and `B` for 8; the limiting
A1 side is silence for 13 and FIRE for 7. Both room tests pass for every added
port. These are dominant-term and limiting-margin labels, not exclusive causes;
`a` is unchanged and the old failure concerned the sum of the budget terms.

Two negative controls mutate `Search.AsymmetricNeedTolerance` itself: replacing
the lower FIRE bound with an upper bound, and removing `1/8000` from the silence
condition. Both must fail Lean's proof check; parser/import failures do not count.

This improves the sufficient scalar criterion. It does not discharge noisy-run
transfer, fitted-offset interpretation, FIRE reconstruction, rest-state or
physical detection-envelope premises. The same conditional boundary remains.

## Planned numerical and noisy-repeat checks

Scope is frozen for PR #110. The campaign owner will perform step refinement
and noisy repetitions; their measured results will enter a separate PR based
on `main` after #110 is merged. The existing plans below are not new results.

[STEP_STUDY_PROTOCOL.md](STEP_STUDY_PROTOCOL.md) freezes six nominal/calibration
cases at maximum steps 200/100/50 ns, with duplicate baselines: 24 runs.
**NOT_STARTED:** the pinned ngspice executable and PDK are unavailable here.
A successful comparison would measure sensitivity to step refinement, not
prove an absolute integration-error bound.

[REPETITION_PROTOCOL.md](REPETITION_PROTOCOL.md) freezes the original 37 ports
at 100 repeats each: 3,500 complete cell trains and 3,700 eligible-port
observations. [repetition_plan.py](repetition_plan.py) checks complete ledgers
and computes one-sided Clopper–Pearson bounds per port, with Bonferroni bounds
for simultaneous coverage. It keeps count agreement and residual success
separate and never treats all 3,700 observations as iid. Its synthetic tests
validate the analyzer only. The [readiness report](repetition-readiness.json)
records **NOT_STARTED**, with missing runtime, reproducible noise injection
and physical endpoint extraction explicitly listed. No new circuit run or
noisy error measurement is claimed.

## Why the derived tolerance is zero

The analog error budget is

`E = a + B + (20/17)*ell + 1/8000`.

When `E < d0/2`, the need theorem guarantees the integer count exactly. Thus
the derived **count error is zero**, even though the analog errors are nonzero.
The decoded two-block feasibility margin also has `tauL = 0`. Substituting `E`
directly for the integer `tauL` would mix log-gain units and pulse counts.
Failure of the budget does not give a larger certified count tolerance.

The prerequisite [VariableNeedTolerance.lean](../../recursive-learning/native/Search/VariableNeedTolerance.lean)
is copied byte for byte from PR #107 at
`9a30f822c8b01fddf11e2514c4aa4059750644cf`. That prerequisite was copied without
merging PR #107; no prior result or certification script is changed.

## Proof chain and its premises

| Layer | What is checked | Remaining premise |
|---|---|---|
| Cumulative need theorem | Error budget implies silence before `m` and firing at `m` in the scalar model | Bounds on the true initial/cumulative gains and threshold |
| [Counts.lean](PhysicalEvaluator/Counts.lean) | Finite observations decode to `some m`; two counts imply `LessonAccurate ... 0` | Resting-charge bounds and explicit scalar observation correspondence |
| [Envelope.lean](PhysicalEvaluator/Envelope.lean) | Lower/upper detection envelopes imply the same exact finite count | The physical detection respects those envelopes |
| [RecordedData.lean](PhysicalEvaluator/RecordedData.lean) | Published numerical budgets/floors, recorded rest charges and first-FIRE decoding | Their interpretation as bounds on actual scalar states |
| [RecordedBridge.lean](PhysicalEvaluator/RecordedBridge.lean) | Numerical constants discharge room/floor in conditional certificate constructors, including a direct envelope entry | Explicit gain, cumulative, charge and scalar level/envelope correspondence fields |
| [RecordedGains.lean](PhysicalEvaluator/RecordedGains.lean) | Initial and cumulative inferred-gain bounds recomputed from twelve published reads, including proved log/exp enclosures | Published decimal readings and fixed scalar inference formula |
| [ReadoutBridge.lean](PhysicalEvaluator/ReadoutBridge.lean) | Those inferred bounds discharge the true-gain premises after paying an explicit readout residual | True normalized gain differs from the inferred gain by at most `1e-4`, plus rest-state and detection envelopes |
| [PeakMeasurement.lean](PhysicalEvaluator/PeakMeasurement.lean) | Peak and initial-charge measurement errors propagate to a corrected-amplitude budget, together with a separate model residual | Supplied measurement-error bounds and physical/model discrepancy |
| [PeakError.lean](PhysicalEvaluator/PeakError.lean), [PeakBridge.lean](PhysicalEvaluator/PeakBridge.lean) | Amplitude error becomes a log-gain error and feeds the recorded controller contract | A physical corrected-amplitude residual within the proved admissible budget |
| [MeasurementBridge.lean](PhysicalEvaluator/MeasurementBridge.lean) | Raw readout vectors and declared sensor/model budgets derive both the amplitude residual and the actual resting-charge band | Supplied peak, charge and model-error bounds, plus physical detection envelopes |
| [CampaignData.lean](PhysicalEvaluator/CampaignData.lean), [CampaignBridge.lean](PhysicalEvaluator/CampaignBridge.lean) | All 37 amended campaign budgets; measured per-port `eps3` enters the gain-transfer and controller theorem | Reference-state bounds, applicability to every actual read, rest charge and physical detection envelopes |
| [Controller.lean](PhysicalEvaluator/Controller.lean) | Derived feasibility precision, exact computed-cost precision, Ready, retained reference-cost non-degradation and budgets | Fixed two-block benchmark and declared resource accounting |

`FiniteProbeCertificate m` contains only `m+1` samples. It has no exact-count
field, no supplied `LessonAccurate` field and no post-FIRE monotonicity premise.
The proof uses a constant extension of the last finite gain only as an internal
mathematical construction. It asserts nothing about later physical gains.

`FiniteEnvelopeCertificate` also allows threshold noise **during** a read.
Detection must imply scalar firing at the lower threshold, and scalar firing
at the upper threshold must imply detection. A low/high effective threshold
is a logical witness, not an assertion that the real threshold was constant.
This does not prove the circuit-to-scalar envelope correspondence itself.

[IdealExample.lean](PhysicalEvaluator/IdealExample.lean) constructs concrete
`FiniteProbeCertificate` values without physical hypotheses: unit threshold,
resting charge `0.1`, constant dose `1/20` and zero gain/threshold errors.
Their executable observations are false until the target count and true at
that count. Instances at counts two and three show that the certificate
interface is inhabited and derive zero margin error for those ideal needs.
These are scalar-model examples, not calibrated circuit realizations.

`readoutCounts` returns `none` when a FIRE is missing, including on a nonempty
all-false trace. Decoding alone is not certification: an uncertified trace can
have a perfectly readable count. Only the certificate-backed constructor has
the conditional physical guarantee.

## What the cost theorem means

`certifiedEnvironment` computes policy costs from the derived evaluator's
complete commanded-pulse ledger, declared per-probe overhead and fixed number
of lesson uses. For this evaluator `tauC = 0` follows from exact computation.
`certified_cost_eq_reference` connects that computation to the objective based
on the **true certified needs**; `certified_controller_nondegradation` then
uses the existing robust adoption theorem. No `LessonAccurate` or `CostAccurate`
hypothesis is passed to this specialized theorem.

This is not a calibration of an arbitrary physical cost sensor. Gain/need
bounds alone cannot bound energy-report error; the formal counterexample
`count_certificate_does_not_bound_arbitrary_cost` states that separation.
Joules, elapsed time, lost/extra delivered pulses and physical reset costs
require their own measurement or refinement theorem.

Acquisition is not silently free. `certified_total_budget` adds an explicit
acquisition ledger to selection and live-search work. The theorem does not
measure or upper-bound that ledger physically. `acquisition_break_even`
requires the savings to cover acquisition as well as selection.

## Original recorded-data replay (before the #109 measurement update)

The seven files in [evidence/provenance.json](evidence/provenance.json) are
public extracts from the pinned PR #107 revision. Hashes are checked against
the pinned manifest, and each retained CSV against its metadata hash. No private
binary trace is fetched or re-extracted, and no simulator is rerun.

The originally selected case `t6004` had two in-domain ports under #107's
budget, with counts 6 and 4. Its preparation port fails #109's amended budget.
The negative case `t6007` has both ports outside the domain: port 1 counts 4
instead of predicted 5; port 2 counts the predicted 3 and is **still excluded**.
Agreement alone does not certify a port. These cases were selected after the
campaign for a bridge demonstration, not as a new held-out experiment.

`evidence_check.py` uses exact rational decimal arithmetic and outward padding
of `1e-10` for the published numerical budget tests. Generated nominal level
and dose constants retain the published nominal references separately; the
lower bound used for the floor is not silently substituted as a new center.
The positive conservative rooms are approximately 0.003754 and 0.005725.
The constructor's true-state premises must still hold relative to its exact
references. Arithmetic widening is not a proof of those premises.

### Recomputing the inferred gains

[gain_check.py](gain_check.py) now recomputes the twelve readings through the
first FIRE of each positive-case port. It uses `q_peak` for a silent read and
`q_tc` for a firing read whose latency is at least 0.76:

```
y_silent = log(q_peak - 0.1 - (c_pre - 0.1)*exp(-1/2))
y_fire   = log(q_tc   - 0.1 - (c_pre - 0.1)*exp(-3/8)) + kappa
z_inferred = y - log(response(1))
```

The response normalization matters: the published `y` is not the native model's
log gain `z`. [MeasuredGains.lean](PhysicalEvaluator/MeasuredGains.lean) proves
the corresponding center identity and that subtracting this fixed response
leaves cumulative increments unchanged. It also proves that a uniform readout
error `delta` costs `delta` in the initial bound and `2*delta` in the cumulative
bound. The total need budget therefore pays `3*delta`.

The generator uses exact rational arithmetic, with outward-rounded intervals.
[LogIntervals.lean](PhysicalEvaluator/LogIntervals.lean) proves the analytic
Taylor remainder; [Readout.lean](PhysicalEvaluator/Readout.lean) proves the
exponential enclosures and propagates them through the readout formula. Lean
independently checks all twelve generated logarithm intervals and the derived
initial/cumulative bounds. No floating-point logarithm is trusted.

| Positive-case port | Samples | Inferred initial bound `ahat` | Inferred cumulative bound `Bhat` |
|---|---:|---:|---:|
| `t6004`, preparation | 7 | 0.0054284 | 0.00466844 |
| `t6004`, practice | 5 | 0.00127293 | 0.004584 |

Both satisfy `ahat + 1e-4 <= aCSV` and `Bhat + 2e-4 <= BCSV`, using the
existing outward-padded CSV budgets. Thus `readout_controller_contract` derives
the previous conditional non-degradation result from a readout residual bound,
without asking for the initial and cumulative true-gain bounds separately.
**The `1e-4` residual is an admissible hypothesis, not a measured error.** Its
physical justification must cover model mismatch, rounding of the serialized
readings, and the firing-read correction. Count agreement cannot establish it.

The fixed `kappa` is taken from the pinned calibration. This recomputation does
not estimate its physical error or reproduce PR #107's global `eps`, which was
computed across silent reads from all 100 test cells. That `eps` is different
from `eps_kappa_cohort`; the two saved test trains cannot establish it. The
comparison to the published budgets above does not require substituting either
empirical estimate for the unproved physical residual.

### From a peak residual to the gain budget

The new entry uses an explicit corrected-amplitude residual `epsilonPeak`.
For a recorded logarithm `y`, the reconstructed amplitude is `exp(y)`;
the scalar model's amplitude is `response(1) * exp(trueGain)`. The physical
premise bounds their absolute difference by `epsilonPeak`. For a FIRE read,
the reconstructed amplitude includes the early-read correction; it is not
the raw `q_peak` column.

The generic bound is

```text
measuredAmplitude >= L > 0, 0 <= epsilonPeak < L
abs(trueAmplitude - measuredAmplitude) <= epsilonPeak
    => abs(log(trueAmplitude) - log(measuredAmplitude))
         <= epsilonPeak / (L - epsilonPeak).
```

The denominator pays for uncertainty in the true amplitude. Replacing it
with `L` would generally underestimate the error. `PeakError.lean` proves
this inequality and the normalization to scalar log gain. Its correction
variant additionally pays `epsilonKappa` when the additive logarithmic
correction has that uncertainty.

For all twelve recorded reads, `PeakBridge.lean` proves the reconstructed
amplitude is at least `7/10`, using the previously checked gain intervals.
Thus any nonnegative residual satisfying

```text
epsilonPeak <= 7/100010
```

gives log-gain error at most `1e-4`. The concrete illustrative residual
`1/20000` gives the exact bound `1/13999`, below `1e-4`.
`peak_residual_controller_contract` then recovers Ready and retained
reference-cost non-degradation with the same explicit rest-state and
detection-envelope premises. These are admissible budgets in model amplitude
units, **not measured peak errors or a new voltage calibration**.

The measurement ledger is also explicit. With the same reference duration
`t` and correction `kappa` for the physical and reported readings, define

```text
correctedPeak(q,c,t,kappa) = exp(kappa) * (q - 0.1 - (c - 0.1)*exp(-t))
```

If peak and initial-charge readings have errors bounded by `epsilonQ` and
`epsilonC`, their corrected-amplitude difference is bounded by
`exp(kappa) * (epsilonQ + exp(-t)*epsilonC)`. With a separately supplied
scalar-model residual `epsilonModel`, the total is

```text
epsilonModel + exp(kappa) * (epsilonQ + exp(-t)*epsilonC).
```

`gain_error_of_measurements` composes that ledger with the logarithmic bound.
The fixed references do not assert exact physical timing or calibration:
any mismatch in timing, correction, waveform or model must be covered by the
supplied model residual, or a separate correction budget where applicable.
The theorem does not estimate those errors from count agreement. This
illustrative measurement entry is separate from the #109 campaign entry above.

### Recorded sensor-to-controller entry

The generated projection now retains exact `Q`, `C`, `Duration` and `Kappa`
vectors for each port, in addition to the inferred gains. `Q` uses `q_peak`
on silent reads and `q_tc` on the first FIRE. Lean proves their readout
identity, positivity of the logarithm argument and equality of the corrected
peak to `exp(reportedGain)`. The read values come from the pinned CSV,
`Kappa` from its pinned calibration JSON, and `Duration` from the declared
`1/2` or `3/8` read protocol. No independent handwritten numeric table of
readings is introduced.

For each of the twelve samples, Lean also checks:

- `Duration >= 0` and `exp(Kappa) <= 11/10`;
- `0.1 <= C - 1e-7` and `C + 1e-7 <= 0.1001`.

The latter is a margin in the recorded values, not a calibration of the charge
sensor. If its actual error is bounded by `1e-7`, that margin implies the true
resting charge belongs to the required band.

`RecordedMeasurementPremises` supplies actual gain, actual sampled `Q` and
actual resting charge, with the following illustrative bounds:

| Supplied physical premise | Bound |
|---|---:|
| Peak / early-read measurement error | `1e-5` |
| Initial-charge measurement error | `1e-7` |
| Scalar-model discrepancy at those actual readings | `2e-5` |

The model discrepancy still includes any unproved timing and calibration
effects. **These three numbers are admissible hypotheses, not measured errors
or established sensor specifications.** Their composition is checked exactly:

```text
2e-5 + (11/10) * (1e-5 + 1e-7) = 3111/100000000 < 7/100010.
```

`measurement_controller_contract` connects those premises to the recorded
two-level controller. It derives the corrected-amplitude residual, the
log-gain bound and the actual resting-charge band. None of those three is a
separate input field in this entry. The same actual charge is used in the
measurement-error bound and in both physical detection-envelope premises.
Those detection implications remain supplied physical obligations. No claim
is made that the simulated circuit realizes this particular error ledger.

[Replay.lean](PhysicalEvaluator/Replay.lean) actually runs two policies from
lesson `(10,9)`, with overhead one and twenty lesson uses per episode:

| Policy | Final lesson | Trial pulses | Attempts | Objective |
|---|---|---:|---:|---:|
| Preparation first, six-probe budget | `(6,8)` | 94 | 6 | 380 |
| Practice first, twelve-probe budget | `(6,4)` | 148 | 11 | 359 |

Selection costs `381+360=741`. The full recorded train has 21 pulses, which
are included rather than charging only its two shorter certified prefixes.
Selection, recorded train and live-search work total `21+741+159=921` before
live deployments. With this ledger, amortization holds exactly from 37 full
episodes: `14045 <= 14060`. At 36 episodes it fails. The live search starts the
first episode; it is not an extra free run.

Earlier shared calibration is a prepared input in this numerical example.
Charging its acquisition adds to the generic ledger and changes break-even.
Simulation runtime and hardware energy are not pulse counts. The conditional
`replay_matches_certificates`/`certified_replay_nondegradation` and the direct
`replay_matches_envelopes`/`envelope_replay_nondegradation` entry connect this
executable replay to the supplied physical premises, without claiming that
the replay itself establishes them.

The conclusions of the `certified_replay_nondegradation` and
`envelope_replay_nondegradation` lemmas are properties of the fixed decoded
model and do not depend on their physical-premise arguments. They already
follow from `replay_sound` and the discrete controller contract. Supplying the
premises gives a conditional physical interpretation, not additional evidence
that those premises hold. The docstrings make this distinction explicit.

## What still prevents a complete physical closed loop

1. PR #109 supplies leak scans for all 100 test cells. All midpoint estimates
   lie in the original six-cell `h_mu` envelope, but only 67 whole sampled
   brackets do. The campaign entry uses the per-cell enlarged bracket rather
   than treating the six-cell maximum as a universal bound. A sampled bracket
   still does not prove all later threshold behavior or port-2 correspondence.
2. Measured `eps3` replaces the toy residual in the campaign entry. Its fitted
   offsets, declared quadrature margin, noiseless-to-noisy transfer and the
   final-quarter FIRE correction do not establish absolute true gain or
   physical detection envelopes. These remain explicit obligations.
3. A certificate for one recorded prefix does not establish that every later
   physical validation after preparation/reset reproduces those counts, or
   that two physical ports behave as the separable two-block learner under a
   changed pulse order. The digital model remains fixed in these theorems.
4. Native execution of policy selection, validation and memory updates, and
   correspondence between commanded and delivered cost, remain the open
   [handoff obligations](../NATIVE_HANDOFF.md). Native selector reuse alone
   does not discharge them.

## Reproduce

With the repository's pinned Lean 4.35.0 toolchain and Mathlib dependencies:

```sh
lake build
python3 evidence_check.py --check --report evidence-validation.json
python3 gain_check.py --check --report gain-validation.json
git fetch --no-tags --depth=1 origin 7ded279f103dab5beb6c1c671f1acbdf4cff18c0
python3 campaign_check.py --check --report campaign-validation.json
git fetch --no-tags --depth=1 origin 8b11a5f5d2b6843bc6ca1f9ff0b82c30fa99f19d
python3 asymmetric_check.py --check --report asymmetric-validation.json
python3 -m unittest test_asymmetric_check test_repetition_plan
python3 verify_physical.py --report physical-validation.json
lake env lean Trace.lean
```

The module audit checks all declarations in imported project modules,
including private/generated/unused declarations, permitting only `propext`,
`Classical.choice` and `Quot.sound`. [evidence-validation.json](evidence-validation.json)
records twelve data mutations; [gain-validation.json](gain-validation.json)
records six readout-data mutations and generated/source hashes;
[campaign-validation.json](campaign-validation.json) records six campaign-data
mutations, the complete eligible-port list and snapshot provenance;
[physical-validation.json](physical-validation.json) records thirty-two semantic
proof mutations and source hashes. Parser/import failures never count as
successful rejection. CI reproduces the build, all five verifiers, the 16
directional/statistical tests, repetition readiness and the original replay,
preserving their reports. Neither the original replay nor synthetic repetition
records constitute a newly executed physical loop.
