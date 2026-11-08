# Reset duration and terminal saturation

This Lean package studies a scalar load model motivated by the compression and
decoupling tests in the Reset Operator manuscript. A request can trigger a
transition if the residual load allows the system to rearm. Requests and the
sustained forcing continue after a transition fails.

Each scenario fixes the dissipation rate `b > 0`, request interval `τ > 0`,
load impulse `A > 0`, and rearming limit `H > 0`. The parameter `D ≥ H`
is the equilibrium load under full coupling, corresponding to a constant
inflow `bD`. A fraction `λ ∈ [0,1]` of that forcing passes during protection.

At time `nτ`, the load just before the request is `xₙ`. Every request adds
`A`. When `xₙ < H`, the request triggers a transition and enables protection
until the next request. Otherwise the interval evolves under full coupling.
In either mode the continuous path solves `x' = -b(x-E)`, with `E = λD`
during protection and `E = D` during full coupling. Lean checks its derivative
and post-request initial value.

## Exact threshold when protection covers the request period

For a successful request, put `r = exp(-bτ)`. Its next load is

```text
xₙ₊₁ = r(xₙ + A) + (1 - r)λD.
```

The protected map has fixed point `F = λD + A/(exp(bτ)-1)`. Starting from
`x₀ < H`, Lean proves the following outcomes.

| Condition | Outcome |
|---|---|
| `F < H` | Every request fires and the load stays uniformly below the rearming limit. |
| `F = H` | Every request fires, with no uniform positive margin below the limit. |
| `H < F` | The load increases through the successful requests. There is a first blocked request, and all later requests are blocked. |

The last result follows from the dynamics. While requests succeed under
`H < F`, the load grows by at least `(1-r)(F-H) > 0` per interval. Once a
request is blocked, both its post-impulse load and the full-coupling equilibrium
are at least `H`. The subsequent continuous path stays at or above `H`,
including between requests. Request dates still extend to arbitrarily late times.

When `λD < H`, the exact duration threshold is

```text
τcrit = log(1 + A/(H - λD)) / b.
```

Terminal saturation occurs exactly for `τ < τcrit`. If `λD ≥ H`, every
positive duration leads to terminal saturation. The assumption `D ≥ H`
captures maintained forcing strong enough to keep a blocked system above its
rearming limit.

For fixed `b, A, H, τ, λ`, repetition at **every constant forcing level**
`D ≥ H` holds exactly when `λ = 0` and
`τ ≥ log(1 + A/H)/b`. Any fixed positive leakage admits a sufficiently
large constant forcing to prevent repeated transitions.

## Matched examples

All Lean examples start at zero with `b = A = H = 1` and `D = 2`.

| Protection window | Leakage | Proven behavior |
|---|---|---|
| `log 4` | 0 | Every request fires. |
| `log (3/2)` | 0 | Two requests fire. Load grows from 0 to 2/3 to 10/9, so the third and all later requests are blocked. |
| `log 2` | 0 | Every request fires, but there is no uniform positive margin. |
| `log 4` | 1/2 | Terminal saturation occurs. |

## Shorter protection at fixed cadence

The [fixed cadence model](ResetWindow/FixedCadence.lean) separates the request
period `P` from the protection duration `d ∈ [0,P]`. After a successful
request, the drive is reduced to `λD` for `d` and then returns to `D` for
`P-d`. After a blocked request, it stays at `D` throughout. The two successive
flows agree exactly at request endpoints with a single-period recurrence.
Writing `r = exp(-bP)` and `s = exp(-b(P-d))`, its protected fixed point is

```text
F = D (1 - (1 - λ)(s - r)/(1 - r)) + A/(exp(bP)-1).
```

Starting below `H`, terminal saturation occurs exactly when `F > H`.
The continuous load stays above the rearming limit after the first block.
With the same requests and forcing, any further shortening of a window
that leads to terminal saturation also leads to terminal saturation.

At the same period `P = log 4`, with no leakage during protection, full
protection lets every request fire. With `d = log(11/4)`, residual load
grows from 0 to 7/8 to 35/32. The third request and every later request
are blocked. Only the duration changes in this comparison.

## Scope and reproduction

The model uses periodic requests, a fixed load impulse per request and a
constant drive in each scenario. Its necessity result concerns a fixed linear
leakage fraction under arbitrarily large constant forcing. The comparison
formalizes the proposed mechanism in that class. Its empirical application
requires measuring a residual load, the coupling and the rearming limit in
the system being tested.

The statements for full-period protection are `Protocol.terminalSaturation_iff_short_window`,
`Protocol.uniformMargin_iff` and `Protocol.robustRecursion_iff` in
[ResetWindow.lean](ResetWindow.lean). [Examples.lean](ResetWindow/Examples.lean)
contains the matched executions. The package uses the same pinned Lean and
Mathlib versions as the main proof project.

Run these commands from this directory.

```sh
lake exe cache get Mathlib.Analysis.SpecialFunctions.ExpDeriv Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.LinearCombination Mathlib.Tactic.Positivity Mathlib.Tactic.Ring Mathlib.Tactic.NormNum
lake build
```

The default build includes an audit of all project declarations, including
private definitions and proofs. It permits only `propext`, `Classical.choice`
and `Quot.sound` and rejects additional axioms or admitted proofs.
