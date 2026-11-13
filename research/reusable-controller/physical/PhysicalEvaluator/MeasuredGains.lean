import PhysicalEvaluator.Counts

/-! Normalize the reported logarithm of the response-scaled drive into the
scalar model's log gain. Subtracting the same log response leaves cumulative
increments unchanged. Error transfer is conditional on explicit readout-error
bounds: no physical peak-to-gain or firing correspondence is inferred here. -/
namespace ReusableController.PhysicalEvaluator
open RecursiveLearning.Native KernelR.Hybrid

/-- The reported `y` is a log of a response-scaled drive. It is not itself
the scalar log gain unless the response normalization has been removed. -/
noncomputable def scalarGain (y : ℝ) : ℝ := y - Real.log (response 1)

noncomputable def reportedCentre (level dose : ℝ) (m : ℕ) : ℝ :=
  Real.log (level - 1 / 10) - ((m : ℝ) - 1 / 2) * dose

theorem scalarGain_reportedCentre {level : ℝ} (positive : 1 / 10 < level)
    (dose : ℝ) (m : ℕ) :
    scalarGain (reportedCentre level dose m) = needCentre level dose m := by
  have residualPositive : 0 < level - 1 / 10 := by linarith
  unfold scalarGain reportedCentre needCentre firingLogGain
  rw [Real.log_div residualPositive.ne' response_one_pos.ne']
  ring

theorem scalarGain_centre_error {level : ℝ} (positive : 1 / 10 < level)
    (dose y : ℝ) (m : ℕ) :
    |scalarGain y - needCentre level dose m| = |y - reportedCentre level dose m| := by
  rw [← scalarGain_reportedCentre positive dose m]
  congr 1
  unfold scalarGain
  ring

theorem scalarGain_cumulative (y0 yk dose : ℝ) (k : ℕ) :
    scalarGain yk - scalarGain y0 - (k : ℝ) * dose = yk - y0 - (k : ℝ) * dose := by
  unfold scalarGain
  ring

/-- One readout error is paid in the initial centering bound. -/
theorem centre_error_transfer {level dose y trueGain ahat delta0 : ℝ} {m : ℕ}
    (positive : 1 / 10 < level)
    (reported : |y - reportedCentre level dose m| ≤ ahat)
    (readout : |trueGain - scalarGain y| ≤ delta0) :
    |trueGain - needCentre level dose m| ≤ ahat + delta0 := by
  have normalized : |scalarGain y - needCentre level dose m| ≤ ahat := by
    rw [scalarGain_centre_error positive]
    exact reported
  obtain ⟨rlo, rhi⟩ := abs_le.mp readout
  obtain ⟨nlo, nhi⟩ := abs_le.mp normalized
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Both endpoint errors are paid in a cumulative increment. This remains
valid for unequal, sample-dependent readout budgets. -/
theorem cumulative_error_transfer {y0 yk true0 truek dose Bhat delta0 deltak : ℝ}
    {k : ℕ} (reported : |yk - y0 - (k : ℝ) * dose| ≤ Bhat)
    (initialReadout : |true0 - scalarGain y0| ≤ delta0)
    (currentReadout : |truek - scalarGain yk| ≤ deltak) :
    |truek - true0 - (k : ℝ) * dose| ≤ Bhat + deltak + delta0 := by
  have normalized : |scalarGain yk - scalarGain y0 - (k : ℝ) * dose| ≤ Bhat := by
    rw [scalarGain_cumulative]
    exact reported
  obtain ⟨rlo, rhi⟩ := abs_le.mp initialReadout
  obtain ⟨slo, shi⟩ := abs_le.mp currentReadout
  obtain ⟨nlo, nhi⟩ := abs_le.mp normalized
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The finite-vector form retains a separate readout uncertainty at each
sample. In particular the initial sample error appears in every increment. -/
theorem finite_measured_bounds {m : ℕ} {level dose ahat Bhat : ℝ}
    (y trueGain delta : Fin (m + 1) → ℝ)
    (positive : 1 / 10 < level)
    (reportedStart : |y 0 - reportedCentre level dose m| ≤ ahat)
    (reportedCumulative : ∀ k, |y k - y 0 - (k.val : ℝ) * dose| ≤ Bhat)
    (readout : ∀ k, |trueGain k - scalarGain (y k)| ≤ delta k) :
    |trueGain 0 - needCentre level dose m| ≤ ahat + delta 0 ∧
      ∀ k, |trueGain k - trueGain 0 - (k.val : ℝ) * dose| ≤ Bhat + delta k + delta 0 := by
  exact ⟨centre_error_transfer positive reportedStart (readout 0),
    fun k => cumulative_error_transfer (reportedCumulative k) (readout 0) (readout k)⟩

/-- A uniform readout uncertainty gives a certificate only after paying its
full extra budget: `delta` in centering and `2 * delta` in cumulative drift.
Threshold, resting-charge and scalar-observation links are explicit physical
premises. Recorded observations alone do not discharge any of those links. -/
noncomputable def certificate_of_measured_gains {m : ℕ}
    (level0 dose0 ahat Bhat ell delta : ℝ)
    (reportedGain trueGain level charge : Fin (m + 1) → ℝ)
    (observed : Fin (m + 1) → Bool)
    (positive : 1 / 10 < level0)
    (floor : 19 / 20 ≤ level0 - ell)
    (reportedStart : |reportedGain 0 - reportedCentre level0 dose0 m| ≤ ahat)
    (reportedCumulative : ∀ k,
      |reportedGain k - reportedGain 0 - (k.val : ℝ) * dose0| ≤ Bhat)
    (readout : ∀ k, |trueGain k - scalarGain (reportedGain k)| ≤ delta)
    (levelBound : ∀ k, |level k - level0| ≤ ell)
    (chargeBand : ∀ k, 1 / 10 ≤ charge k ∧ charge k ≤ 1 / 10 + 1 / 10000)
    (room : (ahat + delta) + (Bhat + 2 * delta) + 20 / 17 * ell + 1 / 8000 < dose0 / 2)
    (scalarCorrespondence : ∀ k, observed k = true ↔
      PulseFires (charge k) (Real.exp (trueGain k)) (level k)) :
    FiniteProbeCertificate m where
  level0 := level0
  dose0 := dose0
  a := ahat + delta
  B := Bhat + 2 * delta
  ell := ell
  gain := trueGain
  level := level
  charge := charge
  observed := observed
  levelFloor := floor
  gainBound := centre_error_transfer positive reportedStart (readout 0)
  cumulativeBound := by
    intro k
    have bound := cumulative_error_transfer (reportedCumulative k) (readout 0) (readout k)
    linarith
  levelBound := levelBound
  chargeBand := chargeBand
  room := room
  scalarCorrespondence := scalarCorrespondence

end ReusableController.PhysicalEvaluator
