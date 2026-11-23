# The ℝ bridge: what the gate checks, and what it must imply

**Development work.** The bridge was written by the inverter session (`proof/inverter-bridge` 13aba3a). It is
`gate_silence` and `gate_firing` in `research/circuit/lean/CircuitInverterGateProof.lean`, taking the premises below
plus `StateBound` to the varying-leak theorems.

**Checked here (independently, 2026-11-23):**
- On a fresh worktree of 13aba3a: `lake exe cache get`, then `lake build` of the varying-leak, box-reference, Taylor
  and gate-bridge modules, the 9901 gate and its audit (rc 0), then `check_inverter_gate_single.py` (rc 0).
- The script reports:
  - the core-only compile is OK;
  - a Mathlib import into the core module is rejected;
  - the single-source gate audit passed on 128 declarations, with the axioms `propext`, `Classical.choice` and
    `Quot.sound` only;
  - five negative controls are rejected: a project axiom, `sorry`, StateBound weakened, 9901 above the bound, and
    9901 with δ = 0.1.
- The seed-9901 values in `CircuitInverterGateInstance9901.lean` equal this package's.
- The rest of this file is the interface as first written.

## Sources

- The gate's definitions now have one source: `research/circuit/lean/CircuitInverterGate.lean` (namespace
  `KernelR.Circuit.Gate`, core Lean, proof/inverter-bridge 13aba3a). The Mathlib bridge `CircuitInverterGateProof.lean`
  and this package's gate files both import it. The package's former copy, `InverterInstanceCheck.lean`, is retired.
  The abstract layer is in `lean/InverterInstanceTiming.lean`.
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

## Each measured value: its source

Rounding rule:
- up for a budget;
- down for `Q` and for `aLo`;
- nearest for `emit`;
- denominator 10^6.

| `Measures` field | Formula | Source (MEASURE.json `measures.*`, run) |
|---|---|---|
| `aLo`, `aHi` | min and max of the two fitted rates (`aLo` down, `aHi` up) | `leak_above.rate` (R3, help only, fit `x_inf + c e^{-kt}` on [1, 4]), `leak_below.rate` (R4, input only, on [0.5, 4]) |
| `aRef`, `alpha` | `(aLo + aHi)/2`, `(aHi − aLo)/2` | the same |
| `eps0` | max of `abs x` at the slot start and 0.05 tu after the reset, R1 and R2 | `eps0` |
| `etaH` | `max over 200 prefixes t of ∫₀ᵗ abs(H − box)`, max of R1 and R2 | `etaH` |
| `etaM` | `∫₀^D max(−J, 0)`, R2 (input present) | `etaM` |
| `etaJ` | `∫₀^(h+hl) abs J`, R1 (input absent) | `etaJ` |
| `delta` | `abs(x_trip − 0.9)`, with `x_trip` the x at the comparator's first flip on an ideal ramp of 0.1 unit/tu | `delta` (R5) |
| `Q` | `∫₀^τ max(J, 0)`, R2 | `Q` |
| `latchLo`, `latchHi` | latch rise (p crossing 0.9 V) minus the crossing of `x_trip` by x, R1 | `latch_delay_tu` |
| `emit` | latch rise date, R1 | `emit_absent_tu` |
| `early` | a certificate: the largest grid value (1/1000) satisfying `FiringBefore` | computed by `gate.best_early` |
| `k.delta`, `k.eta` (K3) | `3 · 335.03 µV / vunit`; `3 · sqrt(2) · inmw · sqrt(D · tu · tnz) / (cq · vunit)` | `research/circuit/noise.json` |

Integrals are trapezoidal on the saved points (step ≤ 5 ns in R1, R2 and R5; ≤ 20 ns in R3 and R4). `H` and `J` are
the currents through the 0 V ammeters `vah` and `vaj`, in units of x per tu.

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

**[I] Open modelling step.**
- `actualLaw` with one constant `a` is not met: the cell's leak depends on the side of rest.
- The gate's interval check, both measured rates in `[a′ − α, a′ + α]`, is the numeric content of a varying-leak
  lemma, `|a(t) − a′| ≤ α` for the solution of `x′ = −a(t) x + I(t)`.
- That lemma is not proved (the Lean session is writing it).
- Until then, every verdict is conditional; `GATE_*.json` says so in `verdict_status` and `open_premises`.
