# M3: bounded adaptive search under fixed, inexact evaluation

This discrete controller adjusts its own search policy with proved safeguards,
with assumed evaluator precision in the general contracts.
It selects from a finite family using measured outcomes of actual level-1
searches. Evaluators, acceptance rules, benchmark and tolerances remain fixed.
M1's exact model is unchanged; this is a separate bounded-error extension.
The [native reuse result](NATIVE_ROUNDS.md) supplies a reusable selector,
not a physical implementation of either search level.

## Model and immutable boundary

[NoisySearch.lean](ReusableController/NoisySearch.lean) retains M1's separable
two-block learner and unit candidate edits. A policy chooses the preferred
coordinate, a finite probe budget (`step * rounds`), and whether to stop on an
ambiguous reading. `step` is a batch size of separately validated unit probes;
only the product affects this implementation. It is **not** a larger unchecked
decrement. A failed large decrement would not justify a permanent unit block.

The lesson evaluator reports an integer feasibility margin, with error at most
`tauL` relative to the minimum coordinate slack. Each probe pays its complete
candidate lesson and a declared overhead. The fixed assessment is:

| Reading `r` | Action |
|---|---|
| `r >= tauL` | Certified feasible; commit the unit edit |
| `r + tauL < 0` | Certified infeasible; retain lesson and block that coordinate |
| Otherwise | Indeterminate; retain lesson and bits, charge the probe |

An unavailable unit edit at zero can also block safely. A negative reading alone
is insufficient. The examples include a feasible candidate with reading `-1`
at tolerance one: blocking it would violate `Ready`.

The policy benchmark starts each policy from the same passing lesson and fresh
validation learners, with the same fixed oracle. Its true accounting cost is

`J(policy) = trialPulses + overhead * attempts + deployments * finalLesson.cost`.

The level-2 report approximates this cost within a separate tolerance `tauC`.
These tolerances have different units. Integer ticks are a deliberate discrete
model; conversion from physical readings/costs requires a separate calibration
and rounding bound.

[AdaptiveSystem.lean](ReusableController/AdaptiveSystem.lean) puts both oracles,
both tolerances, learner, initial lesson, policy interpretation and objective
weights in `Evaluation`. `Session fixed` carries only mutable memory; `fixed`
is a type parameter. `choosePolicy`, `searchCurrent` and arbitrary compositions
return `Session fixed`. Assessment and adoption are fixed functions, not
executable fields that a selected policy can replace. This is an API invariant
of these transitions, not protection against replacing the program.

## Checked contracts

[Selection.lean](ReusableController/Selection.lean) evaluates the initial policy
once and each distinct alternative once. The menu has no duplicates; its count
includes the initial policy. Adoption requires

`newReport + 2*tauC <= oldReport` **and** `newReport < oldReport`.

At the exact `2*tauC` threshold, true cost may tie. The extra strict measured
comparison rejects zero-tolerance ties and gives a strictly decreasing natural
potential `(cachedReport + tauC).toNat`. Accuracy and nonnegative true costs
ensure a nonnegative shift. No strict decrease of true cost is claimed.

| Obligation | Checked statements |
|---|---|
| Immutable evaluation and rules | `evaluation_immutable` for any finite action history |
| Valid lesson and sound permanent blocks | `noisy_attempt_contract`, `policy_search_contract`, `any_policy_history_safe`; both bits remain monotone |
| Non-increasing retained benchmark cost | `robust_cost_nondegradation`, `selectRun_trueCost`, `any_policy_history_cost` |
| Separate selection spending | `selectStep_accounting`, `selectRun_spent_monotone`, `selection_total_budget`, `selection_amortization` |
| Finite selection and strict adoption potential | `selectFinish_exhausted`, `selectFinish_stable`, `selectStep_adoption_progress`, `selectRun_adoption_bound` |
| Finite level-1 search and combined budget | `policy_search_contract`, `policy_cost_bound`, `two_level_budget` |
| Selected policy actually executes | `adapt_and_search_contract`, `complete_two_level_result` |

For initial lesson cost `C`, uniform probe bound `F`, probe overhead `h`,
deployments per benchmark `D` and additional validation/report/selection
overhead `v`, each validation pays its full `J+v`, bounded by

`B = F*C + h*F + D*C + v`.

Selection spending is at most `menu.count * B`, including the initial policy
and rejected alternatives. Subsequent live search costs at most `F*C + h*F`
more; `two_level_budget` covers their sum. This bound excludes deployments
after live search, which must be added explicitly as below. These are declared
accounting units; no hardware energy, duration or reset-cost bound is inferred.

Selection preserves the live lesson and bits. Invariants hold for any finite
interleaving of selection and search. Termination/budget of `adaptAndSearch`
follows from the finite menu and each policy's fuel; an external caller can
still request more searches. Ambiguity may consume all fuel without another
edit. M1's exact optimality theorem is **not** asserted for noisy search.

## Executed example with nonzero errors

[AdaptiveExamples.lean](ReusableController/AdaptiveExamples.lean) uses true needs
`(3,3)`, initial lesson `(4,8)`, six probes, overhead one and ten lesson uses per
benchmark episode. The lesson oracle overestimates every true margin by one.
Both policies continue after ambiguity and preserve sound bits.

| Policy | Final lesson | Probes | Trial pulses | True `J` | Cost report | Validation charge |
|---|---|---:|---:|---:|---:|---:|
| Preparation first, initial | `(3,8)` | 6 | 61 | 177 | 178 | 178 |
| Practice first, candidate | `(4,3)` | 6 | 51 | 127 | 126 | 128 |

Here `tauL = tauC = 1` numerically, with separate meanings, and `v = 1`.
The cost reports also have nonzero error. Costs come from executable searches,
not an unrelated table. Practice-first is adopted. Selection spends `306`;
live search costs `51+6=57`, giving `363` for selection plus live search.
Generic bounds are `B=199`, selection `<=398`, and selection plus live `<=476`.

Seven fresh episodes amortize selection: `306 + 7*127 = 1195 <= 7*177 = 1239`.
Six do not: `1068 > 1062`. The live search in `adaptAndSearch` begins the
**first** of those seven episodes. `completed_then_six_episodes_amortize`
explicitly charges it, its ten lesson uses, and six more full episodes. It is
not an eighth free search. Seven episodes are not seven individual lesson uses.

The advantage arises from a finite probe budget under uncertainty on a
separable learner, not an order-dependent physical learner or universal
superiority. With exact evaluation and enough fuel, both orders can reach
the same minimum.

## Second benchmark: a different winner and objective sensitivity

[SecondBenchmark.lean](ReusableController/SecondBenchmark.lean) uses needs
`(2,3)`, initial lesson `(10,6)`, twelve probes, overhead two, and two lesson
uses per episode. Its margin error repeats `-1,+1,+1`; every reading has
nonzero error. The complete family contains all four order/stopping choices.

| Policy | True cost | Report | Validation charge |
|---|---:|---:|---:|
| Practice first, continue (initial) | 167 | 166 | 170 |
| Preparation first, continue | 157 | 156 | 160 |
| Practice first, stop on ambiguity | 123 | 122 | 126 |
| Preparation first, stop on ambiguity | 118 | 119 | 121 |

There are three validated adoptions. Preparation-first with early stopping
wins, unlike the first benchmark. It retains `(4,6)` after six accepted edits
and seven probes, with 84 trial pulses. Selection costs 577; live work costs
98; their sum is 675. `amortization_exact_threshold` proves that selection
breaks even **if and only if** at least twelve episodes are used. The explicit
live-first accounting gives `1993 <= 2004` for twelve episodes.

Changing the deployment count to twenty changes the objective. The four costs
become 293, 265, 321 and 298: preparation-first with continued search now wins.
This illustrates why a policy must be revalidated when the benchmark changes.
These are two constructed examples, not a statistical generalization claim.

## What remains open

- Accuracy is proved for the executable examples and assumed in the general
  contracts. The separate [physical-certificate bridge](physical/README.md)
  derives `tauL = 0` from finite scalar certificates, and `tauC = 0` for an
  exact computed pulse ledger. This is conditional on the physical certificate
  premises; it does not establish a physical cost sensor or a closed loop.
- `needAlong_of_variable_doses` establishes dose-count stability under its
  gain, level and dose-error hypotheses. The circuit tolerance bridge on the
  separate certification work supplies numerical budgets, but does not
  establish every physical premise of the finite read-to-margin certificate.
  True-state gain/threshold bounds, scalar observation correspondence and
  calibration transfer remain explicit obligations. It is not an error bound for an arbitrary
  policy-cost sensor. Physical cost calibration and the recorded-to-future-run
  transfer remain open. No scalar peak-to-gain or calibration-coverage
  assumption is removed by this bridge.
- Non-degradation compares policies on the **same fixed benchmark**, from the
  same initial lesson. It is not a claim about an arbitrary later live state,
  new learner, new oracle or changing objective.
- No physical feedback, memory implementation, fresh-learner/reset mechanism
  or native refinement of the two search levels is supplied. See the
  [handoff obligations](NATIVE_HANDOFF.md).
- The finite family and its interpretation are fixed. This is bounded policy
  selection with safeguards, not unrestricted rewriting of controller code.

## Reproduce and falsification controls

```sh
lake build
lake env lean AdaptiveTrace.lean
python3 verify.py
python3 verify_adaptive.py
```

The default audit covers all imported project declarations, including private,
generated and unused declarations. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed. The [adaptive validation report](adaptive-validation.json)
records source hashes and eleven rejected mutations: weakening `2*tauC` to
`tauC`, accepting zero-error ties, blocking ambiguity, making ambiguity free,
accepting uncertified success, erasing live memory, making baseline or candidate
validation free, retaining a consumed candidate, an unused axiom, and an
admitted robustness proof. Syntax/import failures do not count.
The original six M1 controls remain in [validation.json](validation.json).
