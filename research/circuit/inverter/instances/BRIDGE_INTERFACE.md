# The ℝ bridge: what the gate checks, and what it must imply

**Development work. The bridge is not written here; this is its interface.**

## Sources

- The gate is `lean/InverterInstanceCheck.lean`. It is free of Mathlib and works over `Rat`, in namespace
  `LearnedCoincidence.MonotoneDNF.InverterInstance`.
- The theorems the gate serves are in `research/circuit/lean/CircuitInverterLeak.lean` (branch
  `proof/inverter-tolerances`, 646f24ec), namespace `KernelR.Circuit`:
  - `inhibited_silence_leaks`;
  - `uninhibited_first_crossing_leaks`.
- `leakyResponse` is defined in `research/circuit/lean/CircuitTiming.lean`.
- The abstract layer is `research/learned-coincidence/InverterTarget.lean` (`InverterTiming.Valid`, `InverterRead`)
  and `InverterLag.lean` (`front_end_lag_window`). It is already discharged in Lean, with no ℝ step:
  - `inverterRead_of_premises` (in the gate library) gives `InverterRead` on both observed reads;
  - `FrontEndFits` is `windowFits ∧ spreadFits`.

## Instantiation

`d : Design`, `m : Measures`, `k : Allowance`. Every `Rat` below is cast to `ℝ`.

| Theorem variable | Value |
|---|---|
| `a'` | `m.aRef` |
| `α` | `m.alpha` |
| `a` | the instance's actual leak (see "measured premises") |
| `referenceInitial` | `0` |
| `nominalHelp` | `box u := if d.h ≤ u ∧ u < d.h + d.hl then d.H0 else 0` |
| `reference` | `leakyResponse a' 0 box` |
| `τ`, `D`, `level` | `d.tau`, `d.D`, `d.level` |
| `L` | `leakBudget d = d.D * d.H0 * d.hl` (the same `L` in both theorems) |
| `ε₀` | `m.eps0` |
| `ηH` | `m.etaH + k.eta` (the allowance is booked once, into ηH) |
| `ηm`, `ηJ` | `m.etaM`, `m.etaJ` |
| `δ` | `m.delta + k.delta` |
| `Q` | `m.Q - k.eta` |
| `early`, `deadline` | `d.h + m.early`, `d.h + d.hl` |

## The Rat premises, and the real hypotheses each must give

| Gate premise (Rat) | Real hypothesis it must imply | Theorem |
|---|---|---|
| `Order`: `0 ≤ tau ≤ h`, `h + hl ≤ D`, `0 < aRef`, `0 ≤ alpha`, `0 ≤ Q − k.eta`, `0 < H0`, `0 ≤ early < hl`, budgets `≥ 0` | `leak'`, `order` (silence), `chargeNonneg`, `order` (firing: `0 ≤ early < deadline`) | both |
| `Order` (with `H0 > 0`, `h + hl ≤ D`) | `leakBudget`: `∀ t ∈ Icc 0 D, t * (0 + ∫ u in 0..t, abs (box u)) ≤ L`, and the same on `Icc 0 deadline` | both |
| `SilenceBefore`: `silenceBudget m k + (m.delta + k.delta) + leakTerm d m < d.level` | `before`: `∀ t ∈ Icc 0 τ, reference t + (ε₀ + ηH + ηm) + δ + α * L < level` (the reference is 0 on `[0, h] ⊇ [0, τ]`) | `inhibited_silence_leaks` |
| `SilenceAfter`: `0 < silenceMargin d m k` | `after`: `∀ t ∈ Icc τ D, reference t + (ε₀ + ηH + ηm) + δ + α * L < level + exp (-(a' + α) * D) * Q` | `inhibited_silence_leaks` |
| `FiringBefore`: `refUpper d m m.early + firingBudget m k + (m.delta + k.delta) + leakTerm d m < d.level` | `before`: `∀ t ∈ Icc 0 early, reference t + (ε₀ + (ηH + ηJ)) + δ + α * L < level` | `uninhibited_first_crossing_leaks` |
| `FiringAfter`: `0 < firingMargin d m k` | `after`: `level + (ε₀ + (ηH + ηJ)) + δ + α * L < reference deadline` | `uninhibited_first_crossing_leaks` |

## Lemmas the bridge needs (all in ℝ, about the design only)

1. **Taylor bounds.** For `0 ≤ x`: `expLo x ≤ Real.exp (-x)` and `Real.exp (-x) ≤ expHi x`.
   - `expLo` is the degree-5 Taylor polynomial of `exp (-x)`, and `expHi` the degree-6 one.
2. **The reference in closed form,** for `0 < a'` and `0 ≤ H0`:
   - `reference t = 0` on `[0, h]`;
   - `reference t = H0 * (1 - exp (-a' * (t - h))) / a'` on `[h, h + hl]`;
   - `reference t = reference (h + hl) * exp (-a' * (t - h - hl))` for `t ≥ h + hl`.
3. **Monotonicity, from 2.** `reference` is nondecreasing on `[0, h + hl]`, and `reference t ≤ reference (h + hl)` on
   `[h + hl, D]`.
4. **From 1 and 2, for `0 ≤ y ≤ hl`:**
   - `reference (h + y) ≤ refUpper d m y`;
   - `refLower d m y ≤ reference (h + y)`.
   - `refUpper` and `refLower` both use `aRef`. Since `0 ≤ k.eta ≤ m.Q`, `expLo ((aRef + alpha) * D) * (m.Q − k.eta)`
     is at most `exp (-(a' + α) * D) * Q`.
5. **`leakBudget`,** from `∫ u in 0..t, abs (box u) ≤ H0 * hl` and `t ≤ D`.

## Measured premises (not the bridge's job: the measurement's claims)

These are the hypotheses that the simulation supplies as numbers. They are not derived in Lean:
- `actualLaw`, with one constant leak `a`;
- `gap`, `|a − a'| ≤ α`;
- integrability;
- `initialError`;
- `helpError` on every prefix;
- `inhibitorySign` and `wrongSignNonneg` (split pointwise: `J⁺` and `J⁻`), with `wrongCharge`;
- `charge` (`Q ≤ ∫₀^τ J⁺`);
- `offCharge`;
- `thresholdError`;
- `actualCont`;
- the latch delay.

The physical open point is `gap`. The cell's leak differs on the two sides of rest. The gate takes `a′` and `α` so
that both measured sides lie in `[a′ − α, a′ + α]`, but `actualLaw` assumes one constant `a`.
