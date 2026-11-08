# Recovery-limited firing rate

This is a separate analytic result about R, not an additional conclusion or
hypothesis of the finite-chain training theorem. Physical firing-rate saturation
here means a limit on output cadence. It is different from terminal jump
saturation in `CompleteThrough`.

## General statement

Fix a cell in any finite network, any router and any initial input queue.
For any supplied finite execution, suppose its actual continuous recovery
coordinate satisfies `b(t) ≤ β` on every flow, with `β > 0`. Every ordered pair
of FIRE dates of that cell satisfies

```text
second - first ≥ D(β) = 1 + log(5/2) / β.
```

This holds for native `Execution`, the larger `WeakExecution` envelope and
the written model's `CrossingExecution`. The crossing result is proved directly
from weak paths, with no finite-chain protocol or global native-refinement
assumption. A READY tangency elsewhere in the network is allowed.

The built-in cap propagates an initial `b ≤ 11/10` along every flow. Therefore
the uniform lower gap is `D(11/10)`. A Lean-checked decimal bracket is

```text
1.8329915 < D(11/10) < 1.8329916.
```

Thus 1.833 is a rounded approximation, not a certified lower bound.
A smaller positive recovery envelope makes this guaranteed gap larger.

## Finite-window consequence

If `M` is the number of firings in the execution interval `[s.time,u.time]`,
Lean proves both forms

```text
(M - 1) * D(β) ≤ u.time - s.time
M ≤ 1 + (u.time - s.time) / D(β).
```

The allowance of one is necessary for a finite observation window, including
a firing exactly on a boundary. Along any family of longer such windows, this
gives the asymptotic ceiling `1/D(β)` (approximately 0.54556 at the built-in
cap). It excludes sustained output periods shorter than `D(β)`.
No claim is made that this upper rate can actually be attained.

This is not a theorem that every excess input pulse is discarded. Main charge
ignores input while protected, but auxiliary sensors may still respond and
change recovery. A width-one pulse can also remain active after reopening.

## Why the bound holds

After FIRE, the main mode is FAST with charge exactly 1. Its equation is
`q' = -log(4)*q`, and its only main departure is at `q=1/4`. This takes
exactly one time unit, across arbitrary interleaved jumps and flow cuts.

During SLOW, `q' = -b(t)*q`. A complete descent from `1/4` to the reopening
level `1/10` requires `∫b(t)dt = log(5/2)`. The actual path envelope gives
`∫b(t)dt ≤ β*duration`. Consequently SLOW takes at least `log(5/2)/β`.

This proof permits MARK to change recovery while SLOW is in progress. The
formula `log(5/2)/b` is an exact duration only when `b` is constant.
An initial bound `b≤β` alone does not provide a general envelope below the
built-in cap, because later MARK phases may increase it.

No FIRE is possible while the cell remains FAST or SLOW. The proof extracts
the first actual main-mode changes and then transfers this protection to the
recorded firing list. It assumes neither an event word nor the desired gap.

## Lean entry points

- [Native proof](../proof/lean/KernelR/HybridResetRate.lean):
  `Execution.emissionTimes_separated_of_recovery_bound`,
  `Execution.emissionTimes_separated`,
  `Execution.firing_count_ceiling_of_recovery_bound`,
  `reset_gap_antitone` and `reset_gap_cap_bounds`.
- [Weak and crossing proof](../proof/lean/KernelR/HybridResetRateCrossing.lean):
  `CrossingExecution.emissionTimes_separated_of_recovery_bound`,
  `CrossingExecution.emissionTimes_separated` and
  `CrossingExecution.firing_count_ceiling_of_recovery_bound`.
- `Execution.RecoveryBound` and `WeakExecution.RecoveryBound` state a bound
  on actual path interiors and endpoints, not a new physical variable.
- The crossing bridge reuses the existing individual-flow strictification
  only for coordinates it preserves exactly: recovery and protected charge.
  It does not identify arbitrary whole weak histories with native histories.

## Scope and review

The statements compare events in existing finite executions. They do not
establish continuation or completion for every arbitrary router and queue.
No source frequency, source amplitude, fabrication box, complete horizon or
network topology is imposed by the spacing statement; its explicit recovery
premise is essential. The uniform specialization starts with `b≤11/10`.

The result is an instance of a refractory rate limit in this particular
model. It does not prove the broader Reset Operator thesis for arbitrary
physical or computational systems, nor experimentally validate a device.

## Reproduction

From `proof/lean` with the pinned Lean/Mathlib environment:

```sh
lake build KernelR.HybridResetRateCrossing
python -m scripts.negative.check_hybrid_reset_rate_negative
lake build
lake build Audit
```

The paired controls check valid uses first and require genuine type errors for
altered contracts. They test interface rejection, not mathematical counterexample
existence. The unchanged project axiom audit checks the new modules through the
umbrella import. See the [validation ledger](VALIDATION_LEDGER.md#recovery-limited-firing-rate-local-validation)
for the exact local checkpoint and distinction from CI results.
