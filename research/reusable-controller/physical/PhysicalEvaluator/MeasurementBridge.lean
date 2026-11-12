import PhysicalEvaluator.PeakBridge
import PhysicalEvaluator.PeakMeasurement

/-! An explicit sensor/model entry to the recorded controller contract.
The numerical sensor and model budgets are admissible hypotheses, not errors
measured by this development. The model discrepancy includes unproved timing,
calibration and scalar-correspondence effects. Gain error, corrected-amplitude
error and resting-charge membership are derived rather than assumed. -/
namespace ReusableController.PhysicalEvaluator
open RecursiveLearning RecursiveLearning.Native KernelR.Hybrid
open RecordedData RecordedGains ReusableController.Adaptive

noncomputable def measurementEpsilon : ℝ := 3111 / 100000000

theorem measurement_epsilon_admissible :
    0 ≤ measurementEpsilon ∧ measurementEpsilon ≤ 7 / 100010 := by
  norm_num [measurementEpsilon]

/-- Declared model plus sensor accounting, including the kappa amplification
of both sensor errors. A nonnegative duration makes the charge-error factor
at most one. No fitted measurement-error estimate enters this inequality. -/
theorem measurement_residual_budget {duration kappa : ℝ}
    (durationNonnegative : 0 ≤ duration) (kappaScale : Real.exp kappa ≤ 11 / 10) :
    1 / 50000 + Real.exp kappa *
      (1 / 100000 + Real.exp (-duration) * (1 / 10000000)) ≤ measurementEpsilon := by
  have decay : Real.exp (-duration) ≤ 1 := by
    calc
      Real.exp (-duration) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have innerNonnegative : 0 ≤ 1 / 100000 + Real.exp (-duration) * (1 / 10000000 : ℝ) := by
    positivity
  have scaled := mul_le_mul_of_nonneg_right kappaScale innerNonnegative
  unfold measurementEpsilon
  nlinarith

structure RecordedMeasurementPremises (m : Nat)
    (reportedGain Q C duration kappa : Fin (m + 1) → ℝ)
    (level0 ell : ℝ) (observed : Fin (m + 1) → Bool) where
  actualGain : Fin (m + 1) → ℝ
  trueQ : Fin (m + 1) → ℝ
  trueC : Fin (m + 1) → ℝ
  peakError : ∀ k, |trueQ k - Q k| ≤ 1 / 100000
  chargeError : ∀ k, |trueC k - C k| ≤ 1 / 10000000
  modelError : ∀ k,
    |response 1 * Real.exp (actualGain k) -
      correctedPeak (trueQ k) (trueC k) (duration k) (kappa k)| ≤ 1 / 50000
  observableSound : ∀ k, observed k = true →
    PulseFires (trueC k) (Real.exp (actualGain k)) (level0 - ell)
  observableComplete : ∀ k,
    PulseFires (trueC k) (Real.exp (actualGain k)) (level0 + ell) → observed k = true

/-- Published arithmetic supplies the four side conditions. The physical
premises contain no independent gain bound, amplitude bound or charge band. -/
noncomputable def RecordedMeasurementPremises.toPeakResidual
    {m reportedGain Q C duration kappa level0 ell observed}
    (w : RecordedMeasurementPremises m reportedGain Q C duration kappa level0 ell observed)
    (recordedAmplitude : ∀ k,
      correctedPeak (Q k) (C k) (duration k) (kappa k) = Real.exp (reportedGain k))
    (chargeMargin : ∀ k,
      1 / 10 ≤ C k - 1 / 10000000 ∧ C k + 1 / 10000000 ≤ 1 / 10 + 1 / 10000)
    (durationNonnegative : ∀ k, 0 ≤ duration k)
    (kappaScale : ∀ k, Real.exp (kappa k) ≤ 11 / 10) :
    RecordedPeakResidualPremises m reportedGain level0 ell measurementEpsilon observed where
  trueGain := w.actualGain
  charge := w.trueC
  epsilonNonnegative := measurement_epsilon_admissible.1
  epsilonAdmissible := measurement_epsilon_admissible.2
  amplitudeResidual := by
    intro k
    rw [← recordedAmplitude k]
    exact (peak_residual_of_measurements (w.modelError k) (w.peakError k) (w.chargeError k)).trans
      (measurement_residual_budget (durationNonnegative k) (kappaScale k))
  chargeBand := by
    intro k
    obtain ⟨lower, upper⟩ := abs_le.mp (w.chargeError k)
    obtain ⟨marginLower, marginUpper⟩ := chargeMargin k
    exact ⟨by linarith, by linarith⟩
  observableSound := w.observableSound
  observableComplete := w.observableComplete

abbrev PreparationMeasurementPremises := RecordedMeasurementPremises 6
  t6004p1Gain t6004p1Q t6004p1C t6004p1Duration t6004p1Kappa
  t6004p1NominalLevel0 t6004p1Ell observedPreparation

abbrev PracticeMeasurementPremises := RecordedMeasurementPremises 4
  t6004p2Gain t6004p2Q t6004p2C t6004p2Duration t6004p2Kappa
  t6004p2NominalLevel0 t6004p2Ell observedPractice

noncomputable def preparationPeakResidualOfMeasurements (w : PreparationMeasurementPremises) :
    PreparationPeakResidualPremises measurementEpsilon :=
  w.toPeakResidual t6004p1CorrectedPeak_eq t6004p1ChargeMargin
    t6004p1DurationNonnegative t6004p1KappaScale

noncomputable def practicePeakResidualOfMeasurements (w : PracticeMeasurementPremises) :
    PracticePeakResidualPremises measurementEpsilon :=
  w.toPeakResidual t6004p2CorrectedPeak_eq t6004p2ChargeMargin
    t6004p2DurationNonnegative t6004p2KappaScale

/-- Full conditional passage from sensor and model premises to the actual
two-level controller contract, with no separately assumed log-gain error or
charge-band membership. Observation-envelope premises still remain physical. -/
theorem measurement_controller_contract {P : Type}
    (p : PreparationMeasurementPremises) (q : PracticeMeasurementPremises)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat)
    (menu : PolicyMenu P) (passes : (lesson.train ⟨6, 4⟩).retained = true) :
    let fixed := certifiedEnvironment
      (preparationEnvelopeCertificate (preparationEnvelopeOfReadout
        (preparationReadoutOfPeakResidual (preparationPeakResidualOfMeasurements p)))).toProbeCertificate
      (practiceEnvelopeCertificate (practiceEnvelopeOfReadout
        (practiceReadoutOfPeakResidual (practicePeakResidualOfMeasurements q)))).toProbeCertificate
      lesson policies overhead deployments validationOverhead
    Ready ⟨6, 4⟩ (adaptAndSearch fixed menu).memory.live ∧
      referenceCost 6 4 lesson policies overhead deployments
        (adaptAndSearch fixed menu).memory.incumbent ≤
          referenceCost 6 4 lesson policies overhead deployments menu.seed :=
  peak_residual_controller_contract (preparationPeakResidualOfMeasurements p)
    (practicePeakResidualOfMeasurements q) lesson policies overhead deployments validationOverhead menu passes

end ReusableController.PhysicalEvaluator
