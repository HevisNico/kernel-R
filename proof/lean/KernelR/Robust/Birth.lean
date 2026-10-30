import KernelR.Robust.Noise

/-! Birth-section accounting. Existence and guard ordering of the warm-up
execution remain analytic refinement obligations, not hidden assumptions. -/
namespace KernelR.Robust

theorem recovery_after_protected_mark {b dose ν duration : ℝ}
    (hb : 7999 / 100000 ≤ b ∧ b ≤ 8001 / 100000)
    (hd : 1 / 10 - ν * duration / 2 ≤ dose ∧ dose ≤ 1 / 10 + ν * duration / 2) :
    17999 / 100000 - ν * duration / 2 ≤ b + dose ∧
      b + dose ≤ 18001 / 100000 + ν * duration / 2 := by
  constructor <;> linarith [hb.1, hb.2, hd.1, hd.2]

theorem three_noisy_errors {d₀ d₁ d₂ ν t₀ t₁ t₂ : ℝ}
    (h₀ : |d₀ - 3 / 5| ≤ 8 * ν * t₀)
    (h₁ : |d₁ - 3 / 5| ≤ 8 * ν * t₁)
    (h₂ : |d₂ - 3 / 5| ≤ 8 * ν * t₂) :
    |d₀ + d₁ + d₂ - 9 / 5| ≤ 8 * ν * (t₀ + t₁ + t₂) := by
  rw [abs_le] at *
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]

/-- A wider initial band is invariant; the noise radius is not added per pulse. -/
theorem entry_band_invariant {initial forcing decay η ν κ : ℝ}
    (hd : 0 ≤ decay ∧ decay ≤ 1) (hη : 0 ≤ η)
    (hi : |initial| ≤ η + ν / κ)
    (hf : |forcing| ≤ (ν / κ) * (1 - decay)) :
    |decay * initial + forcing| ≤ η + ν / κ := by
  apply ready_error_bound hd hi
  calc
    |forcing| ≤ (ν / κ) * (1 - decay) := hf
    _ ≤ (η + ν / κ) * (1 - decay) := by nlinarith [hd.2]

theorem entry_band_inside_section {q radius : ℝ}
    (hq : |q - 1 / 10| ≤ radius) (hr : radius ≤ 3 / 100) :
    7 / 100 ≤ q ∧ q ≤ 13 / 100 := by
  rw [abs_le] at hq
  constructor <;> linarith [hq.1, hq.2]

inductive WarmupEvent where
  | silent | fire | protectedInput
  deriving DecidableEq

def birthWord : List WarmupEvent :=
  [.silent, .silent, .silent, .fire, .protectedInput] ++ List.replicate 11 .fire

theorem birth_word_length : birthWord.length = 16 := by decide
theorem birth_word_emissions : birthWord.count .fire = 12 := by decide
theorem birth_word_errors : birthWord.count .silent = 3 := by decide
theorem birth_word_protected : birthWord.count .protectedInput = 1 := by decide

end KernelR.Robust
