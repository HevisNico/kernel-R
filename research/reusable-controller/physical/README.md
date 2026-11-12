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

## Recorded-data replay

The seven files in [evidence/provenance.json](evidence/provenance.json) are
public extracts from the pinned PR #107 revision. Hashes are checked against
the pinned manifest, and each retained CSV against its metadata hash. No private
binary trace is fetched or re-extracted, and no simulator is rerun.

The selected positive case `t6004` has two in-domain ports, with counts 6 and 4.
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

1. PR #107's scalar peak-to-gain correspondence and transfer of `h_mu` remain
   conditional. `h_mu` is a worst case on six cells, not a bound established
   for each test cell. This work adds no leak scans or new calibration coverage.
2. Numerical room and recorded counts do not alone prove true-state gain/
   threshold bounds or the scalar detection envelope. The conditional
   constructors expose those obligations instead of replacing them with an
   assumed oracle-accuracy field.
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
python3 verify_physical.py --report physical-validation.json
lake env lean Trace.lean
```

The module audit checks all declarations in imported project modules,
including private/generated/unused declarations, permitting only `propext`,
`Classical.choice` and `Quot.sound`. [evidence-validation.json](evidence-validation.json)
records twelve data mutations; [physical-validation.json](physical-validation.json)
records semantic proof mutations and source hashes. Parser/import failures
never count as successful rejection. CI reproduces the build, both verifiers
and the replay, preserving their reports.
