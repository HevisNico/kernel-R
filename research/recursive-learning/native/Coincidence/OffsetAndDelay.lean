import Thresholds.ParameterTraining

/-! Two refinements of the one-pulse training theorem, both stated in the
existing parameterized semantics with realized thresholds.

A common shift of the two ERROR endpoints leaves the dose unchanged. A
fixed reaction delay after each ERROR endpoint crossing is represented by
the lower levels that the sensor's exponential decay reaches after that
delay, and bounds the departure of the dose from its nominal value by a
multiple of the delay. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- A common shift of the realized ERROR entry and exit charges cancels
from the dose of an exposed ERROR segment. -/
theorem ExposedErrorSpan.dose_common_offset {θ p before after u l δ}
    (span : ExposedErrorSpan θ p before after (u + δ) (l + δ)) :
    after - before = 8 * (u - l) := by
  have h := span.dose
  linarith

private theorem settle_factor_sixteen : Real.exp (-(1 / 2) * (16 - 3 : ℝ)) ≤ 1 / 625 := by
  have series := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 13 / 2 by norm_num) 12
  norm_num [Finset.sum_range_succ] at series
  rw [show -(1 / 2) * (16 - 3 : ℝ) = -(13 / 2) by norm_num, Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num)
    (show (625 : ℝ) ≤ Real.exp (13 / 2) by linarith)

/-- The sixteen-unit schedule with an ERROR exit anywhere within 1/160 of
its nominal level. The sensor still returns to its rest band before the
read. -/
private theorem training_read_at_sixteen {θ ε time gains p}
    (box : @PhysicalBox 1 θ ε)
    (config : (θ 0).thresholds = trainingThresholds p ((θ 0).thresholds.error p)
      ((θ 0).thresholds.auxReady p) (θ 0).thresholds.fire)
    (threshold : 19 / 20 ≤ (θ 0).thresholds.fire ∧ (θ 0).thresholds.fire ≤ 21 / 20)
    (hi : |(θ 0).thresholds.error p - 1 / 10| ≤ 1 / 200)
    (lo : |(θ 0).thresholds.auxReady p - 1 / 40| ≤ 1 / 160)
    (dose : 11 / 20 ≤ 8 * ((θ 0).thresholds.error p - (θ 0).thresholds.auxReady p) ∧
      8 * ((θ 0).thresholds.error p - (θ 0).thresholds.auxReady p) ≤ 77 / 100)
    (gain : 7 / 6 ≤ Real.exp (gains p) ∧ Real.exp (gains p) ≤ 6 / 5)
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)) :
    ∃ T final,
      time + 16 + 3 / 10 < T ∧ T < time + 16 + 9 / 10 ∧
      (∃ e : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p 16) final,
        ParameterCompleteThrough e T) ∧
      ∀ {u} (e : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p 16) u),
        ParameterCompleteThrough e T →
        u.ObservationalEq final ∧ e.emissionTimes 0 = [T] ∧
        u.x 0 (.z p) = gains p + 8 * ((θ 0).thresholds.error p - (θ 0).thresholds.auxReady p) := by
  obtain ⟨lo₁, _⟩ := abs_le.mp lo
  have settled : |(θ 0).thresholds.auxReady p - 1 / 40| *
      Real.exp (-(1 / 2) * (16 - 3 : ℝ)) ≤ 1 / 100000 :=
    (mul_le_mul lo settle_factor_sixteen (Real.exp_pos _).le (by norm_num)).trans (by norm_num)
  exact training_read_every_complete_in_band (time := time) (delay := 16) box config threshold hi
    (by linarith) dose le_rfl settled gain caps

/-- One training pulse and one read when both ERROR endpoints carry a
common shift `δ` and separate small errors `a` and `b`. In every complete
run the log-gain increment is `3/5 + 8 * (a - b)`. The common shift does
not appear in it. -/
theorem training_read_common_offset {θ ε time gains p δ a b}
    (box : @PhysicalBox 1 θ ε)
    (config : (θ 0).thresholds = trainingThresholds p ((θ 0).thresholds.error p)
      ((θ 0).thresholds.auxReady p) (θ 0).thresholds.fire)
    (threshold : 19 / 20 ≤ (θ 0).thresholds.fire ∧ (θ 0).thresholds.fire ≤ 21 / 20)
    (entry : (θ 0).thresholds.error p = 1 / 10 + δ + a)
    (exit : (θ 0).thresholds.auxReady p = 1 / 40 + δ + b)
    (common : |δ| ≤ 1 / 250) (entryError : |a| ≤ 1 / 1000) (exitError : |b| ≤ 1 / 1000)
    (gain : 7 / 6 ≤ Real.exp (gains p) ∧ Real.exp (gains p) ≤ 6 / 5)
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)) :
    ∃ T final,
      time + 16 + 3 / 10 < T ∧ T < time + 16 + 9 / 10 ∧
      (∃ e : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p 16) final,
        ParameterCompleteThrough e T) ∧
      ∀ {u} (e : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p 16) u),
        ParameterCompleteThrough e T →
        u.ObservationalEq final ∧ e.emissionTimes 0 = [T] ∧
        u.x 0 (.z p) = gains p + 3 / 5 + 8 * (a - b) ∧
        |u.x 0 (.z p) - gains p - 3 / 5| ≤ 8 * (|a| + |b|) := by
  obtain ⟨c₁, c₂⟩ := abs_le.mp common
  obtain ⟨a₁, a₂⟩ := abs_le.mp entryError
  obtain ⟨b₁, b₂⟩ := abs_le.mp exitError
  have hi : |(θ 0).thresholds.error p - 1 / 10| ≤ 1 / 200 := by
    rw [entry]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have lo : |(θ 0).thresholds.auxReady p - 1 / 40| ≤ 1 / 160 := by
    rw [exit]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have dose : 11 / 20 ≤ 8 * ((θ 0).thresholds.error p - (θ 0).thresholds.auxReady p) ∧
      8 * ((θ 0).thresholds.error p - (θ 0).thresholds.auxReady p) ≤ 77 / 100 := by
    rw [entry, exit]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨T, final, early, late, existsRun, allRuns⟩ :=
    training_read_at_sixteen (time := time) box config threshold hi lo dose gain caps
  refine ⟨T, final, early, late, existsRun, ?_⟩
  intro u e complete
  obtain ⟨same, fire, learned⟩ := allRuns e complete
  rw [entry, exit] at learned
  have increment : u.x 0 (.z p) - gains p - 3 / 5 = 8 * (a - b) := by linarith
  refine ⟨same, fire, by linarith, ?_⟩
  rw [increment]
  exact abs_le.mpr
    ⟨by linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b],
     by linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b]⟩

/-- With a common shift alone, up to 5% of the nominal ERROR entry level,
every complete run writes exactly the nominal increment `3/5`. -/
theorem training_read_pure_common_offset {θ ε time gains p δ}
    (box : @PhysicalBox 1 θ ε)
    (config : (θ 0).thresholds = trainingThresholds p ((θ 0).thresholds.error p)
      ((θ 0).thresholds.auxReady p) (θ 0).thresholds.fire)
    (threshold : 19 / 20 ≤ (θ 0).thresholds.fire ∧ (θ 0).thresholds.fire ≤ 21 / 20)
    (entry : (θ 0).thresholds.error p = 1 / 10 + δ)
    (exit : (θ 0).thresholds.auxReady p = 1 / 40 + δ)
    (common : |δ| ≤ 1 / 200)
    (gain : 7 / 6 ≤ Real.exp (gains p) ∧ Real.exp (gains p) ≤ 6 / 5)
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)) :
    ∃ T final,
      time + 16 + 3 / 10 < T ∧ T < time + 16 + 9 / 10 ∧
      (∃ e : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p 16) final,
        ParameterCompleteThrough e T) ∧
      ∀ {u} (e : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p 16) u),
        ParameterCompleteThrough e T →
        u.ObservationalEq final ∧ e.emissionTimes 0 = [T] ∧
        u.x 0 (.z p) = gains p + 3 / 5 := by
  obtain ⟨c₁, c₂⟩ := abs_le.mp common
  have hi : |(θ 0).thresholds.error p - 1 / 10| ≤ 1 / 200 := by
    rw [entry]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have lo : |(θ 0).thresholds.auxReady p - 1 / 40| ≤ 1 / 160 := by
    rw [exit]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have dose : 11 / 20 ≤ 8 * ((θ 0).thresholds.error p - (θ 0).thresholds.auxReady p) ∧
      8 * ((θ 0).thresholds.error p - (θ 0).thresholds.auxReady p) ≤ 77 / 100 := by
    rw [entry, exit]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨T, final, early, late, existsRun, allRuns⟩ :=
    training_read_at_sixteen (time := time) box config threshold hi lo dose gain caps
  refine ⟨T, final, early, late, existsRun, ?_⟩
  intro u e complete
  obtain ⟨same, fire, learned⟩ := allRuns e complete
  rw [entry, exit] at learned
  exact ⟨same, fire, by linarith⟩

/-- The level an exponential decay at `rate` reaches a time `d` after it
crossed `level`. -/
noncomputable def delayedLevel (level rate d : ℝ) : ℝ :=
  level * Real.exp (-(rate * d))

/-- A decay that meets `level` at `tCross` is at `delayedLevel level rate d`
after a further time `d`. -/
theorem delayedLevel_of_decay {start rate level tCross d : ℝ}
    (contact : start * Real.exp (-(rate * tCross)) = level) :
    start * Real.exp (-(rate * (tCross + d))) = delayedLevel level rate d := by
  unfold delayedLevel
  rw [← contact, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem delayedLevel_bounds {level rate d : ℝ} (hl : 0 ≤ level) (hr : 0 ≤ rate) (hd : 0 ≤ d) :
    level * (1 - rate * d) ≤ delayedLevel level rate d ∧ delayedLevel level rate d ≤ level := by
  have nonneg : 0 ≤ rate * d := mul_nonneg hr hd
  have lower : 1 - rate * d ≤ Real.exp (-(rate * d)) := by
    linarith [Real.add_one_le_exp (-(rate * d))]
  have upper : Real.exp (-(rate * d)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold delayedLevel
  exact ⟨mul_le_mul_of_nonneg_left lower hl,
    (mul_le_mul_of_nonneg_left upper hl).trans (mul_one level).le⟩

/-- One training pulse and one read when the cell reacts a fixed time `d`
after each ERROR endpoint crossing. The delayed entry happens during
SILENT, at rate `ls`, and the delayed exit during ERROR, at rate `le`. The
realized endpoints are the levels reached after the delay. In every
complete run the increment departs from `3/5` by at most `(12/5) * d`,
for either fabrication box. -/
theorem training_read_reaction_delay {θ ε time gains p d}
    (box : @PhysicalBox 1 θ ε)
    (config : (θ 0).thresholds = trainingThresholds p ((θ 0).thresholds.error p)
      ((θ 0).thresholds.auxReady p) (θ 0).thresholds.fire)
    (threshold : 19 / 20 ≤ (θ 0).thresholds.fire ∧ (θ 0).thresholds.fire ≤ 21 / 20)
    (entry : (θ 0).thresholds.error p = delayedLevel (1 / 10) ((θ 0).ls p) d)
    (exit : (θ 0).thresholds.auxReady p = delayedLevel (1 / 40) ((θ 0).le p) d)
    (reaction : 0 ≤ d ∧ d ≤ 1 / 100)
    (gain : 7 / 6 ≤ Real.exp (gains p) ∧ Real.exp (gains p) ≤ 6 / 5)
    (caps : ∀ q, gains q ≤ Real.log ((θ 0).cap q)) :
    ∃ T final,
      time + 16 + 3 / 10 < T ∧ T < time + 16 + 9 / 10 ∧
      (∃ e : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p 16) final,
        ParameterCompleteThrough e T) ∧
      ∀ {u} (e : ParameterExecution θ (fun _ _ => []) (trainingStart time gains p 16) u),
        ParameterCompleteThrough e T →
        u.ObservationalEq final ∧ e.emissionTimes 0 = [T] ∧
        u.x 0 (.z p) = gains p + 8 * (delayedLevel (1 / 10) ((θ 0).ls p) d -
          delayedLevel (1 / 40) ((θ 0).le p) d) ∧
        -(4 / 5) * ((θ 0).ls p * d) ≤ u.x 0 (.z p) - gains p - 3 / 5 ∧
        u.x 0 (.z p) - gains p - 3 / 5 ≤ (1 / 5) * ((θ 0).le p * d) ∧
        |u.x 0 (.z p) - gains p - 3 / 5| ≤ (12 / 5) * d := by
  obtain ⟨dNonneg, dMax⟩ := reaction
  have lsPos : 0 < (θ 0).ls p := (box.rates_positive 0 p).2.1
  have lePos : 0 < (θ 0).le p := (box.rates_positive 0 p).2.2
  have lsMax : (θ 0).ls p ≤ 3 := (box.coarse_upper 0 p).2.2.1
  have leMax : (θ 0).le p ≤ 11 := (box.coarse_upper 0 p).2.2.2.1
  have lsDelay : (θ 0).ls p * d ≤ 3 * d := mul_le_mul_of_nonneg_right lsMax dNonneg
  have leDelay : (θ 0).le p * d ≤ 11 * d := mul_le_mul_of_nonneg_right leMax dNonneg
  have lsNonneg : 0 ≤ (θ 0).ls p * d := mul_nonneg lsPos.le dNonneg
  have leNonneg : 0 ≤ (θ 0).le p * d := mul_nonneg lePos.le dNonneg
  obtain ⟨entryLow, entryHigh⟩ :=
    delayedLevel_bounds (level := 1 / 10) (by norm_num) lsPos.le dNonneg
  obtain ⟨exitLow, exitHigh⟩ :=
    delayedLevel_bounds (level := 1 / 40) (by norm_num) lePos.le dNonneg
  have hi : |(θ 0).thresholds.error p - 1 / 10| ≤ 1 / 200 := by
    rw [entry]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have lo : |(θ 0).thresholds.auxReady p - 1 / 40| ≤ 1 / 160 := by
    rw [exit]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have dose : 11 / 20 ≤ 8 * ((θ 0).thresholds.error p - (θ 0).thresholds.auxReady p) ∧
      8 * ((θ 0).thresholds.error p - (θ 0).thresholds.auxReady p) ≤ 77 / 100 := by
    rw [entry, exit]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨T, final, early, late, existsRun, allRuns⟩ :=
    training_read_at_sixteen (time := time) box config threshold hi lo dose gain caps
  refine ⟨T, final, early, late, existsRun, ?_⟩
  intro u e complete
  obtain ⟨same, fire, learned⟩ := allRuns e complete
  rw [entry, exit] at learned
  refine ⟨same, fire, learned, by linarith, by linarith, ?_⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end RecursiveLearning.Native
