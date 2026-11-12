import Search.NeedTolerance

/-! The need of a probe with a different nonnegative dose at every write.
This generalizes the scalar gain-ladder contract, not the fixed-dose
hybrid execution constructors or compiled search networks. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- The same silence/firing contract as NeedIs, on an arbitrary log-gain
sequence rather than the arithmetic ladder z0 + k * dose. -/
def NeedAlong (level : ℝ) (z : ℕ → ℝ) (m : ℕ) : Prop :=
  (∀ k : ℕ, k < m → ∀ c, 1 / 10 ≤ c → c ≤ 1 / 10 + 1 / 10000 →
    ¬ PulseFires c (Real.exp (z k)) level) ∧
  (∀ k : ℕ, m ≤ k → ∀ c, 1 / 10 ≤ c → c ≤ 1 / 10 + 1 / 10000 →
    PulseFires c (Real.exp (z k)) level)

theorem needAlong_constant (level dose z₀ : ℝ) (m : ℕ) :
    NeedAlong level (fun k => z₀ + k * dose) m ↔ NeedIs level dose z₀ m := Iff.rfl

theorem pulseFires_mono_logGain {c z w level : ℝ} (order : z ≤ w)
    (fires : PulseFires c (Real.exp z) level) : PulseFires c (Real.exp w) level := by
  obtain ⟨t, ht, reach⟩ := fires
  refine ⟨t, ht, ?_⟩
  rw [readyPulse_from] at reach ⊢
  have drive := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr order) (response_nonnegative ht.1)
  linarith

/-- The original tolerance budget also covers independently varying doses.
The upper and lower constant ladders bound every cumulative sum, and the
existing needIs_of_tolerance theorem supplies their common need. -/
theorem needAlong_of_variable_doses {level level₀ d₀ z₀ a b ℓ : ℝ} {m : ℕ}
    (dose : ℕ → ℝ)
    (fire : 19 / 20 ≤ level) (fire₀ : 19 / 20 ≤ level₀)
    (dosePos : ∀ j, 0 ≤ dose j)
    (gain : |z₀ - needCentre level₀ d₀ m| ≤ a)
    (doseTol : ∀ j, |dose j - d₀| ≤ b)
    (levelTol : |level - level₀| ≤ ℓ)
    (room : a + m * b + 20 / 17 * ℓ + 1 / 8000 < d₀ / 2) :
    NeedAlong level (fun n => z₀ + ∑ j ∈ Finset.range n, dose j) m := by
  have bPos : 0 ≤ b := (abs_nonneg _).trans (doseTol 0)
  have aPos : 0 ≤ a := (abs_nonneg _).trans gain
  have ellPos : 0 ≤ ℓ := (abs_nonneg _).trans levelTol
  have mb : 0 ≤ (m : ℝ) * b := mul_nonneg (Nat.cast_nonneg m) bPos
  have dPos : 0 ≤ d₀ := by linarith
  have lowerTol : |max 0 (d₀ - b) - d₀| ≤ b := by
    rcases le_total 0 (d₀ - b) with h | h
    · rw [max_eq_right h]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [max_eq_left h]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  have upperNeed := needIs_of_tolerance (dose := d₀ + b) fire fire₀ (by positivity)
    gain (show |d₀ + b - d₀| ≤ b by simpa using (abs_of_nonneg bPos).le) levelTol room
  have lowerNeed := needIs_of_tolerance (dose := max 0 (d₀ - b)) fire fire₀
    (le_max_left _ _) gain lowerTol levelTol room
  have bounds (n : ℕ) :
      n * max 0 (d₀ - b) ≤ ∑ j ∈ Finset.range n, dose j ∧
      (∑ j ∈ Finset.range n, dose j) ≤ n * (d₀ + b) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h := abs_le.mp (doseTol n)
      have low : max 0 (d₀ - b) ≤ dose n := max_le (dosePos n) (by linarith [h.1])
      simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      exact ⟨by nlinarith [ih.1], by nlinarith [ih.2, h.2]⟩
  constructor
  · intro n hn c lo hi actual
    exact upperNeed.1 n hn c lo hi (pulseFires_mono_logGain (by linarith [(bounds n).2]) actual)
  · intro n hn c lo hi
    exact pulseFires_mono_logGain (by linarith [(bounds n).1]) (lowerNeed.2 n hn c lo hi)

/-- Equivalent form for a contiguous sequence of actual log-gain states.
The step budget must include every change between two tested states. -/
theorem needAlong_of_step_tolerance {level level₀ d₀ a b ℓ : ℝ} {m : ℕ}
    (z : ℕ → ℝ) (fire : 19 / 20 ≤ level) (fire₀ : 19 / 20 ≤ level₀)
    (stepPos : ∀ j, 0 ≤ z (j + 1) - z j)
    (gain : |z 0 - needCentre level₀ d₀ m| ≤ a)
    (stepTol : ∀ j, |z (j + 1) - z j - d₀| ≤ b)
    (levelTol : |level - level₀| ≤ ℓ)
    (room : a + m * b + 20 / 17 * ℓ + 1 / 8000 < d₀ / 2) :
    NeedAlong level z m := by
  have telescope (n : ℕ) : z 0 + (∑ j ∈ Finset.range n, (z (j + 1) - z j)) = z n := by
    induction n with
    | zero => simp
    | succ n ih => simp only [Finset.sum_range_succ]; linarith
  have h := needAlong_of_variable_doses (fun j => z (j + 1) - z j)
    fire fire₀ stepPos gain stepTol levelTol room
  simpa only [telescope] using h

end RecursiveLearning.Native
