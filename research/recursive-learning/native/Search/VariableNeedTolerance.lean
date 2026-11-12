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

/-- A budget on cumulated doses. Only the distance of each cumulated gain to
the nominal ladder matters, up to the m-th write, and the gain must not fall
below its m-th value afterwards. Nothing is assumed of a single step, so
errors of opposite signs may cancel. -/
theorem needAlong_of_cumulative_tolerance {level level₀ d₀ a B ℓ : ℝ} {m : ℕ}
    (z : ℕ → ℝ) (fire : 19 / 20 ≤ level) (fire₀ : 19 / 20 ≤ level₀)
    (after : ∀ n, m ≤ n → z m ≤ z n)
    (gain : |z 0 - needCentre level₀ d₀ m| ≤ a)
    (cumulative : ∀ n, n ≤ m → |z n - z 0 - n * d₀| ≤ B)
    (levelTol : |level - level₀| ≤ ℓ)
    (room : a + B + 20 / 17 * ℓ + 1 / 8000 < d₀ / 2) :
    NeedAlong level z m := by
  have BPos : 0 ≤ B := (abs_nonneg _).trans (cumulative 0 (Nat.zero_le m))
  have aPos : 0 ≤ a := (abs_nonneg _).trans gain
  have ellPos : 0 ≤ ℓ := (abs_nonneg _).trans levelTol
  have dPos : 0 ≤ d₀ := by linarith
  obtain ⟨gLo, gHi⟩ := abs_le.mp gain
  have ladderRoom : a + B + (m : ℝ) * 0 + 20 / 17 * ℓ + 1 / 8000 < d₀ / 2 := by
    rw [mul_zero, add_zero]
    exact room
  have upperNeed := needIs_of_tolerance (dose := d₀) (z₀ := z 0 + B) (a := a + B) (b := 0)
    fire fire₀ dPos (abs_le.mpr ⟨by linarith, by linarith⟩) (by simp) levelTol ladderRoom
  have lowerNeed := needIs_of_tolerance (dose := d₀) (z₀ := z 0 - B) (a := a + B) (b := 0)
    fire fire₀ dPos (abs_le.mpr ⟨by linarith, by linarith⟩) (by simp) levelTol ladderRoom
  constructor
  · intro n hn c lo hi actual
    have h := abs_le.mp (cumulative n hn.le)
    exact upperNeed.1 n hn c lo hi (pulseFires_mono_logGain (by linarith [h.2]) actual)
  · intro n hn c lo hi
    have h := abs_le.mp (cumulative m le_rfl)
    exact pulseFires_mono_logGain (by linarith [h.1, after n hn]) (lowerNeed.2 m le_rfl c lo hi)

/-- The original tolerance budget also covers independently varying doses.
It is the cumulative budget with `B = m * b`: a bound `b` on every step
bounds every cumulated sum up to the m-th write by `m * b`. -/
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
  have bounds (n : ℕ) : |(∑ j ∈ Finset.range n, dose j) - n * d₀| ≤ n * b := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h := abs_le.mp (doseTol n)
      have i := abs_le.mp ih
      simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      exact abs_le.mpr ⟨by nlinarith [h.1, i.1], by nlinarith [h.2, i.2]⟩
  apply needAlong_of_cumulative_tolerance (B := m * b) _ fire fire₀ ?_ ?_ ?_ levelTol room
  · intro n hn
    have grow : ∑ j ∈ Finset.range m, dose j ≤ ∑ j ∈ Finset.range n, dose j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hn) (fun j _ _ => dosePos j)
    linarith
  · simpa using gain
  · intro n hn
    have scale : (n : ℝ) * b ≤ m * b := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) bPos
    have same : z₀ + ∑ j ∈ Finset.range n, dose j - (z₀ + ∑ j ∈ Finset.range 0, dose j) - n * d₀ =
        (∑ j ∈ Finset.range n, dose j) - n * d₀ := by
      simp
    rw [same]
    exact (bounds n).trans scale

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
