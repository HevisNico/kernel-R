import Search.VariableNeedTolerance
import Mathlib.Data.List.OfFn

/-! Directional cumulative tolerances, fixed independently of campaign data.
Only an upper gain bound is needed before the first FIRE, and only a lower
gain bound is needed at its target index. Initial errors and cumulative errors
therefore have separate silence/firing budgets. The firing budget needs no
extra allowance for the largest resting charge: its worst case is exact rest.
These results concern the scalar model, not a transistor correspondence. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- Direct peak bounds for an arbitrary gain sequence. The only post-target
assumption is that its gain never falls below the gain at the target index. -/
theorem needAlong_of_peak_bounds {level : ℝ} {m : ℕ} (z : ℕ → ℝ)
    (after : ∀ n, m ≤ n → z m ≤ z n)
    (below : ∀ k, k < m → 1 / 10 + 1 / 10000 + Real.exp (z k) * response 1 < level)
    (above : level ≤ 1 / 10 + Real.exp (z m) * response 1) :
    NeedAlong level z m := by
  constructor
  · intro k before c lo hi
    rintro ⟨t, ht, reach⟩
    rw [readyPulse_from] at reach
    have decay := decay_upper (show c - 1 / 10 ≤ 1 / 10000 by linarith)
      (by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) ht.1
    have rise := response_strictMono_pulse.monotoneOn ht
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩) ht.2
    have drive := mul_le_mul_of_nonneg_left rise (Real.exp_pos (z k)).le
    linarith [below k before]
  · intro k later c lo hi
    apply pulseFires_of_peak lo
    have growth := mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (after k later)) response_one_pos.le
    linarith

private theorem resting_log_gap {level : ℝ} (floor : 19 / 20 ≤ level) :
    firingLogGain level - Real.log ((level - 1 / 10 - 1 / 10000) / response 1) ≤
      1 / 8000 := by
  have positive : 0 < level - 1 / 10 - 1 / 10000 := by linarith
  unfold firingLogGain
  rw [Real.log_div (by linarith : level - 1 / 10 ≠ 0) response_one_pos.ne',
    Real.log_div positive.ne' response_one_pos.ne']
  have ratio := Real.log_le_sub_one_of_pos
    (div_pos (show (0 : ℝ) < level - 1 / 10 by linarith) positive)
  rw [Real.log_div (by linarith : level - 1 / 10 ≠ 0) positive.ne'] at ratio
  have bound : (level - 1 / 10) / (level - 1 / 10 - 1 / 10000) - 1 ≤ 1 / 8000 := by
    rw [div_sub_one positive.ne', div_le_iff₀ positive]
    linarith
  linarith

/-- The one-sided offsets may be signed. A large upward deviation at the
target cannot spoil silence at earlier reads; a downward deviation at an
earlier read cannot spoil firing at the target. No opposite-sided cumulative
bound at either set of indices is assumed. Silence is strict, while equality
at the firing boundary is allowed by PulseFires. -/
theorem needAlong_of_asymmetric_cumulative_tolerance
    {level level₀ d₀ aSilent aFire BSilent BFire ℓ : ℝ} {m : ℕ}
    (z : ℕ → ℝ) (fire : 19 / 20 ≤ level) (fire₀ : 19 / 20 ≤ level₀)
    (doseNonnegative : 0 ≤ d₀)
    (after : ∀ n, m ≤ n → z m ≤ z n)
    (gainUpper : z 0 - needCentre level₀ d₀ m ≤ aSilent)
    (gainLower : needCentre level₀ d₀ m - z 0 ≤ aFire)
    (cumulativeUpper : ∀ k, k < m → z k - z 0 - (k : ℝ) * d₀ ≤ BSilent)
    (cumulativeLower : z 0 + (m : ℝ) * d₀ - z m ≤ BFire)
    (levelTol : |level - level₀| ≤ ℓ)
    (silenceRoom : aSilent + BSilent + 20 / 17 * ℓ + 1 / 8000 < d₀ / 2)
    (fireRoom : aFire + BFire + 20 / 17 * ℓ ≤ d₀ / 2) :
    NeedAlong level z m := by
  obtain ⟨shiftLower, shiftUpper⟩ := abs_le.mp (firingLogGain_shift fire fire₀ levelTol)
  dsimp only [needCentre] at gainUpper gainLower
  apply needAlong_of_peak_bounds z after
  · intro k before
    have beforeReal : (k : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt before
    have steps := mul_le_mul_of_nonneg_right beforeReal doseNonnegative
    have cumulative := cumulativeUpper k before
    have gap := resting_log_gap fire
    have under : z k < Real.log ((level - 1 / 10 - 1 / 10000) / response 1) := by
      nlinarith
    have positive : 0 < level - 1 / 10 - 1 / 10000 := by linarith
    have exponential := Real.exp_lt_exp.mpr under
    rw [Real.exp_log (div_pos positive response_one_pos)] at exponential
    have scaled := mul_lt_mul_of_pos_right exponential response_one_pos
    rw [div_mul_cancel₀ _ response_one_pos.ne'] at scaled
    linarith
  · have reach : firingLogGain level ≤ z m := by nlinarith
    have positive : 0 < level - 1 / 10 := by linarith
    have exponential := Real.exp_le_exp.mpr reach
    unfold firingLogGain at exponential
    rw [Real.exp_log (div_pos positive response_one_pos)] at exponential
    have scaled := mul_le_mul_of_nonneg_right exponential response_one_pos.le
    rw [div_mul_cancel₀ _ response_one_pos.ne'] at scaled
    linarith

/-- Every old symmetric cumulative certificate satisfies the directional
rule, without changing its data or weakening its original strict room test. -/
theorem needAlong_of_symmetric_cumulative_via_asymmetric
    {level level₀ d₀ a B ℓ : ℝ} {m : ℕ}
    (z : ℕ → ℝ) (fire : 19 / 20 ≤ level) (fire₀ : 19 / 20 ≤ level₀)
    (after : ∀ n, m ≤ n → z m ≤ z n)
    (gain : |z 0 - needCentre level₀ d₀ m| ≤ a)
    (cumulative : ∀ n, n ≤ m → |z n - z 0 - (n : ℝ) * d₀| ≤ B)
    (levelTol : |level - level₀| ≤ ℓ)
    (room : a + B + 20 / 17 * ℓ + 1 / 8000 < d₀ / 2) :
    NeedAlong level z m := by
  have aNonnegative : 0 ≤ a := (abs_nonneg _).trans gain
  have BNonnegative : 0 ≤ B := (abs_nonneg _).trans (cumulative 0 (Nat.zero_le m))
  have ellNonnegative : 0 ≤ ℓ := (abs_nonneg _).trans levelTol
  apply needAlong_of_asymmetric_cumulative_tolerance
    (aSilent := a) (aFire := a) (BSilent := B) (BFire := B) z fire fire₀
    (by linarith) after (abs_le.mp gain).2
  · have lower := (abs_le.mp gain).1
    linarith
  · intro k before
    exact (abs_le.mp (cumulative k before.le)).2
  · have lower := (abs_le.mp (cumulative m le_rfl)).1
    linarith
  · exact levelTol
  · exact room
  · linarith

/-- An executable finite observation sequence has exactly m false readings
followed by true when it reflects a NeedAlong sequence. Applying the
directional theorem above discharges need; any downstream first-FIRE decoder
can use this list shape without introducing a second physical premise. -/
theorem NeedAlong.finite_readings_shape {level : ℝ} {z : ℕ → ℝ} {m : ℕ}
    (need : NeedAlong level z m)
    (charge : Fin (m + 1) → ℝ) (observed : Fin (m + 1) → Bool)
    (chargeBand : ∀ k, 1 / 10 ≤ charge k ∧ charge k ≤ 1 / 10 + 1 / 10000)
    (correspondence : ∀ k, observed k = true ↔
      PulseFires (charge k) (Real.exp (z k.val)) level) :
    List.ofFn observed = List.replicate m false ++ [true] := by
  have priorObservations : (fun k : Fin m => observed k.castSucc) = fun _ => false := by
    funext k
    have silent := need.1 k.val k.isLt (charge k.castSucc)
      (chargeBand k.castSucc).1 (chargeBand k.castSucc).2
    cases observation : observed k.castSucc with
    | false => rfl
    | true => exact False.elim (silent ((correspondence k.castSucc).mp observation))
  have last : observed (Fin.last m) = true :=
    (correspondence (Fin.last m)).mpr
      (need.2 m le_rfl (charge (Fin.last m)) (chargeBand (Fin.last m)).1 (chargeBand (Fin.last m)).2)
  rw [List.ofFn_succ_last, priorObservations, List.ofFn_const, last]

end RecursiveLearning.Native
