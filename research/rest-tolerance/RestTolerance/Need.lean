import Search.AsymmetricNeedTolerance

/-! Scalar certification for a two-sided pre-read charge band. -/
namespace RecursiveLearning.Native.RestTolerance
open KernelR.Hybrid Set

/-- The legacy upper slack is charged at this same rate: (5/4)(1/10000) = 1/8000. -/
noncomputable def silenceCost (hi : ℝ) : ℝ := 5 / 4 * hi

noncomputable def fireCost (lo : ℝ) : ℝ := 20 / 17 * lo

def ChargeBand (lo hi c : ℝ) : Prop :=
  1 / 10 - lo ≤ c ∧ c ≤ 1 / 10 + hi

def NeedAlongBand (lo hi level : ℝ) (z : ℕ → ℝ) (m : ℕ) : Prop :=
  (∀ k, k < m → ∀ c, ChargeBand lo hi c → ¬ PulseFires c (Real.exp (z k)) level) ∧
  (∀ k, m ≤ k → ∀ c, ChargeBand lo hi c → PulseFires c (Real.exp (z k)) level)

/-- Uniform signed score error throughout the read window. -/
theorem read_score_error {lo hi c gain t : ℝ} (loPos : 0 ≤ lo) (hiPos : 0 ≤ hi)
    (band : ChargeBand lo hi c) (time : 0 ≤ t) :
    readyPulse (1 / 10) gain 0 t - lo ≤ readyPulse c gain 0 t ∧
    readyPulse c gain 0 t ≤ readyPulse (1 / 10) gain 0 t + hi := by
  have factorPos := (Real.exp_pos (-(1 / 2 : ℝ) * t)).le
  have factorLe : Real.exp (-(1 / 2 : ℝ) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have low := mul_le_mul_of_nonneg_right
    (show -lo ≤ c - 1 / 10 by linarith [band.1]) factorPos
  have high := mul_le_mul_of_nonneg_right
    (show c - 1 / 10 ≤ hi by linarith [band.2]) factorPos
  have left := mul_le_mul_of_nonneg_left factorLe loPos
  have right := mul_le_mul_of_nonneg_left factorLe hiPos
  simp only [readyPulse_from, sub_self, zero_mul, add_zero]
  constructor <;> nlinarith

private theorem log_gap {x y cost : ℝ} (xPos : 0 < x) (yPos : 0 < y)
    (budget : x - y ≤ cost * y) :
    Real.log (x / response 1) - Real.log (y / response 1) ≤ cost := by
  have ratio := Real.log_le_sub_one_of_pos (div_pos xPos yPos)
  rw [Real.log_div xPos.ne' yPos.ne'] at ratio
  rw [Real.log_div xPos.ne' response_one_pos.ne', Real.log_div yPos.ne' response_one_pos.ne']
  have bound : x / y - 1 ≤ cost := by
    rw [div_sub_one yPos.ne', div_le_iff₀ yPos]
    exact budget
  linarith

/-- The upper slack cap keeps the shifted silence headroom at least 4/5. -/
theorem silence_log_gap {level hi : ℝ} (floor : 19 / 20 ≤ level)
    (hiPos : 0 ≤ hi) (hiCap : hi ≤ 1 / 20) :
    firingLogGain level - Real.log ((level - 1 / 10 - hi) / response 1) ≤ silenceCost hi := by
  unfold firingLogGain
  apply log_gap (by linarith) (by linarith)
  unfold silenceCost
  nlinarith [mul_nonneg hiPos (show 0 ≤ level - 1 / 10 - hi - 4 / 5 by linarith)]

theorem fire_log_gap {level lo : ℝ} (floor : 19 / 20 ≤ level) (loPos : 0 ≤ lo) :
    Real.log ((level - 1 / 10 + lo) / response 1) - firingLogGain level ≤ fireCost lo := by
  unfold firingLogGain
  apply log_gap (by linarith) (by linarith)
  unfold fireCost
  nlinarith [mul_nonneg loPos (show 0 ≤ level - 1 / 10 - 17 / 20 by linarith)]

theorem needAlong_of_asymmetric_rest_tolerance
    {level level₀ d₀ aSilent aFire BSilent BFire ℓ lo hi : ℝ} {m : ℕ}
    (z : ℕ → ℝ) (fire : 19 / 20 ≤ level) (fire₀ : 19 / 20 ≤ level₀)
    (dosePos : 0 ≤ d₀) (loPos : 0 ≤ lo) (hiPos : 0 ≤ hi) (hiCap : hi ≤ 1 / 20)
    (after : ∀ n, m ≤ n → z m ≤ z n)
    (gainUpper : z 0 - needCentre level₀ d₀ m ≤ aSilent)
    (gainLower : needCentre level₀ d₀ m - z 0 ≤ aFire)
    (cumulativeUpper : ∀ k, k < m → z k - z 0 - (k : ℝ) * d₀ ≤ BSilent)
    (cumulativeLower : z 0 + (m : ℝ) * d₀ - z m ≤ BFire)
    (levelTol : |level - level₀| ≤ ℓ)
    (silenceRoom : aSilent + BSilent + 20 / 17 * ℓ + silenceCost hi < d₀ / 2)
    (fireRoom : aFire + BFire + 20 / 17 * ℓ + fireCost lo ≤ d₀ / 2) :
    NeedAlongBand lo hi level z m := by
  obtain ⟨shiftLower, shiftUpper⟩ := abs_le.mp (firingLogGain_shift fire fire₀ levelTol)
  dsimp only [needCentre] at gainUpper gainLower
  constructor
  · intro k before c band
    rintro ⟨t, ht, reach⟩
    have steps := mul_le_mul_of_nonneg_right
      (show (k : ℝ) + 1 ≤ (m : ℝ) by exact_mod_cast Nat.succ_le_of_lt before) dosePos
    have cumulative := cumulativeUpper k before
    have gap := silence_log_gap fire hiPos hiCap
    have under : z k < Real.log ((level - 1 / 10 - hi) / response 1) := by nlinarith
    have exponential := Real.exp_lt_exp.mpr under
    have headroom : 0 < level - 1 / 10 - hi := by linarith
    rw [Real.exp_log (div_pos headroom response_one_pos)] at exponential
    have scaled := mul_lt_mul_of_pos_right exponential response_one_pos
    rw [div_mul_cancel₀ _ response_one_pos.ne'] at scaled
    have rise := response_strictMono_pulse.monotoneOn ht
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩) ht.2
    have drive := mul_le_mul_of_nonneg_left rise (Real.exp_pos (z k)).le
    have score := (read_score_error (gain := Real.exp (z k)) loPos hiPos band ht.1).2
    simp only [readyPulse_from, sub_self, zero_mul, add_zero] at score
    linarith
  · intro k later c band
    have gap := fire_log_gap fire loPos
    have enough : Real.log ((level - 1 / 10 + lo) / response 1) ≤ z m := by nlinarith
    have exponential := Real.exp_le_exp.mpr (enough.trans (after k later))
    have headroom : 0 < level - 1 / 10 + lo := by linarith
    rw [Real.exp_log (div_pos headroom response_one_pos)] at exponential
    have scaled := mul_le_mul_of_nonneg_right exponential response_one_pos.le
    rw [div_mul_cancel₀ _ response_one_pos.ne'] at scaled
    have score := (read_score_error (gain := Real.exp (z k)) loPos hiPos band
      (show (0 : ℝ) ≤ 1 by norm_num)).1
    simp only [readyPulse_from, sub_self, zero_mul, add_zero] at score
    exact ⟨1, ⟨zero_le_one, le_rfl⟩, by linarith⟩

theorem needAlong_of_cumulative_rest_tolerance
    {level level₀ d₀ a B ℓ lo hi : ℝ} {m : ℕ}
    (z : ℕ → ℝ) (fire : 19 / 20 ≤ level) (fire₀ : 19 / 20 ≤ level₀)
    (loPos : 0 ≤ lo) (hiPos : 0 ≤ hi) (hiCap : hi ≤ 1 / 20)
    (after : ∀ n, m ≤ n → z m ≤ z n)
    (gain : |z 0 - needCentre level₀ d₀ m| ≤ a)
    (cumulative : ∀ n, n ≤ m → |z n - z 0 - (n : ℝ) * d₀| ≤ B)
    (levelTol : |level - level₀| ≤ ℓ)
    (room : a + B + 20 / 17 * ℓ + max (silenceCost hi) (fireCost lo) < d₀ / 2) :
    NeedAlongBand lo hi level z m := by
  have aPos := (abs_nonneg _).trans gain
  have bPos := (abs_nonneg _).trans (cumulative 0 (Nat.zero_le m))
  have ellPos := (abs_nonneg _).trans levelTol
  have costPos : 0 ≤ silenceCost hi := by unfold silenceCost; positivity
  apply needAlong_of_asymmetric_rest_tolerance
    (aSilent := a) (aFire := a) (BSilent := B) (BFire := B) z fire fire₀
    (by linarith [le_max_left (silenceCost hi) (fireCost lo)]) loPos hiPos hiCap after
    (abs_le.mp gain).2
  · linarith [(abs_le.mp gain).1]
  · intro k before
    exact (abs_le.mp (cumulative k before.le)).2
  · linarith [(abs_le.mp (cumulative m le_rfl)).1]
  · exact levelTol
  · linarith [le_max_left (silenceCost hi) (fireCost lo)]
  · linarith [le_max_right (silenceCost hi) (fireCost lo)]

theorem legacy_band_iff {level : ℝ} {z : ℕ → ℝ} {m : ℕ} :
    NeedAlongBand 0 (1 / 10000 + 0) level z m ↔ NeedAlong level z m := by
  simp only [NeedAlongBand, NeedAlong, ChargeBand, sub_zero, add_zero, and_imp]

/-- The original directional theorem, with both expansions of its band set to zero. -/
theorem legacy_asymmetric {level level₀ d₀ aSilent aFire BSilent BFire ℓ : ℝ} {m : ℕ}
    (z : ℕ → ℝ) (fire : 19 / 20 ≤ level) (fire₀ : 19 / 20 ≤ level₀)
    (dosePos : 0 ≤ d₀) (after : ∀ n, m ≤ n → z m ≤ z n)
    (gainUpper : z 0 - needCentre level₀ d₀ m ≤ aSilent)
    (gainLower : needCentre level₀ d₀ m - z 0 ≤ aFire)
    (cumulativeUpper : ∀ k, k < m → z k - z 0 - (k : ℝ) * d₀ ≤ BSilent)
    (cumulativeLower : z 0 + (m : ℝ) * d₀ - z m ≤ BFire)
    (levelTol : |level - level₀| ≤ ℓ)
    (silenceRoom : aSilent + BSilent + 20 / 17 * ℓ + 1 / 8000 < d₀ / 2)
    (fireRoom : aFire + BFire + 20 / 17 * ℓ ≤ d₀ / 2) :
    NeedAlong level z m := by
  apply legacy_band_iff.mp
  apply needAlong_of_asymmetric_rest_tolerance z fire fire₀ dosePos
    (by norm_num) (by norm_num) (by norm_num) after gainUpper gainLower
    cumulativeUpper cumulativeLower levelTol
  · norm_num [silenceCost]
    exact silenceRoom
  · simpa [fireCost] using fireRoom

/-- The original symmetric theorem, with both expansions of its band set to zero. -/
theorem legacy_symmetric {level level₀ d₀ a B ℓ : ℝ} {m : ℕ}
    (z : ℕ → ℝ) (fire : 19 / 20 ≤ level) (fire₀ : 19 / 20 ≤ level₀)
    (after : ∀ n, m ≤ n → z m ≤ z n)
    (gain : |z 0 - needCentre level₀ d₀ m| ≤ a)
    (cumulative : ∀ n, n ≤ m → |z n - z 0 - (n : ℝ) * d₀| ≤ B)
    (levelTol : |level - level₀| ≤ ℓ)
    (room : a + B + 20 / 17 * ℓ + 1 / 8000 < d₀ / 2) :
    NeedAlong level z m := by
  apply legacy_band_iff.mp
  apply needAlong_of_cumulative_rest_tolerance z fire fire₀
    (by norm_num) (by norm_num) (by norm_num) after gain cumulative levelTol
  have costs : max (silenceCost (1 / 10000 + 0)) (fireCost 0) = 1 / 8000 := by
    norm_num [silenceCost, fireCost, max_eq_left]
  rwa [costs]

end RecursiveLearning.Native.RestTolerance
