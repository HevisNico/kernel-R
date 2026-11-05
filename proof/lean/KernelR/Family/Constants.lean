import KernelR.Hybrid

/-! Constants of a family of R cells. Parameter values and structural
admissibility are separate: each theorem requests only the assumptions it uses.
The original kernel is recovered by `nominal`. -/
namespace KernelR.Family
open KernelR.Hybrid

structure Constants where
  a : ℝ
  kappa : ℝ
  rest : ℝ
  fastExit : ℝ
  threshold : ℝ
  auxRest : ℝ
  errorLevel : ℝ
  markExit : ℝ
  auxThreshold : ℝ
  gainFactor : ℝ
  recoveryFactor : ℝ
  recoveryCap : ℝ
  pulseWidth : ℝ
  energyRate : ℝ
  energyTarget : ℝ
  slowWork : ℝ

/-- Sufficient physical sign and level-order assumptions, not protocol margins. -/
structure Admissible (c : Constants) : Prop where
  a_pos : 0 < c.a
  kappa_nonneg : 0 ≤ c.kappa
  rest_pos : 0 < c.rest
  fastExit_gt_rest : c.rest < c.fastExit
  threshold_gt_fastExit : c.fastExit < c.threshold
  auxRest_pos : 0 < c.auxRest
  errorLevel_gt_rest : c.auxRest < c.errorLevel
  markExit_gt_error : c.errorLevel < c.markExit
  auxThreshold_gt_mark : c.markExit < c.auxThreshold
  gainFactor_pos : 0 < c.gainFactor
  recoveryFactor_pos : 0 < c.recoveryFactor
  recoveryCap_pos : 0 < c.recoveryCap
  pulseWidth_pos : 0 < c.pulseWidth
  energyRate_pos : 0 < c.energyRate
  energyTarget_pos : 0 < c.energyTarget
  slowWork_nonneg : 0 ≤ c.slowWork

noncomputable def nominal : Constants where
  a := Hybrid.a
  kappa := 1/2
  rest := 1/10
  fastExit := 1/4
  threshold := 1
  auxRest := 1/40
  errorLevel := 1/10
  markExit := 4/5
  auxThreshold := 1
  gainFactor := 8
  recoveryFactor := 1/2
  recoveryCap := 11/10
  pulseWidth := 1
  energyRate := 10
  energyTarget := 100
  slowWork := 11/10

theorem nominal_admissible : Admissible nominal := by
  constructor <;> norm_num [nominal, Hybrid.a]
  exact Real.log_pos (by norm_num)

/-- Nonnegative fabrication rates; no numerical variability box is imposed. -/
def RatesNonnegative {n} (θ : Fin n → Parameters) : Prop :=
  ∀ i p, 0 ≤ (θ i).lm p ∧ 0 ≤ (θ i).ls p ∧ 0 ≤ (θ i).le p

noncomputable def Constants.errorDose (c : Constants) : ℝ :=
  c.gainFactor * (c.errorLevel - c.auxRest)

noncomputable def Constants.markDose (c : Constants) : ℝ :=
  c.recoveryFactor * (c.auxThreshold - c.markExit)

theorem Admissible.errorDose_pos {c : Constants} (h : Admissible c) : 0 < c.errorDose :=
  mul_pos h.gainFactor_pos (sub_pos.mpr h.errorLevel_gt_rest)

theorem Admissible.markDose_pos {c : Constants} (h : Admissible c) : 0 < c.markDose :=
  mul_pos h.recoveryFactor_pos (sub_pos.mpr h.auxThreshold_gt_mark)

@[simp] theorem nominal_errorDose : nominal.errorDose = 3/5 := by
  norm_num [Constants.errorDose, nominal]

@[simp] theorem nominal_markDose : nominal.markDose = 1/10 := by
  norm_num [Constants.markDose, nominal]

/-- A two-parameter continuum of distinct admissible learning mechanisms. -/
def Constants.withLearningFactors (c : Constants) (gain recovery : ℝ) : Constants :=
  { c with gainFactor := gain, recoveryFactor := recovery }

theorem Admissible.withLearningFactors {c : Constants} (h : Admissible c)
    {gain recovery : ℝ} (hg : 0 < gain) (hr : 0 < recovery) :
    Admissible (c.withLearningFactors gain recovery) := by
  exact { h with gainFactor_pos := hg, recoveryFactor_pos := hr }

theorem withLearningFactors_ne_nominal {gain recovery : ℝ} (h : gain ≠ 8) :
    nominal.withLearningFactors gain recovery ≠ nominal := by
  intro same
  exact h (congrArg Constants.gainFactor same)

/-- A second point changes every exposed fixed constant. Its structural
admissibility does not assert that the nominal pulse protocol works there. -/
noncomputable def alternative : Constants where
  a := Real.log 3
  kappa := 2/5
  rest := 1/5
  fastExit := 1/2
  threshold := 2
  auxRest := 1/50
  errorLevel := 3/25
  markExit := 7/10
  auxThreshold := 6/5
  gainFactor := 5
  recoveryFactor := 1/4
  recoveryCap := 13/10
  pulseWidth := 7/5
  energyRate := 7
  energyTarget := 80
  slowWork := 13/10

theorem alternative_admissible : Admissible alternative := by
  constructor <;> norm_num [alternative]
  exact Real.log_pos (by norm_num)

theorem alternative_doses : alternative.errorDose = 1/2 ∧ alternative.markDose = 1/8 := by
  norm_num [Constants.errorDose, Constants.markDose, alternative]

theorem alternative_ne_nominal : alternative ≠ nominal := by
  intro same
  have := congrArg Constants.threshold same
  norm_num [alternative, nominal] at this

end KernelR.Family
