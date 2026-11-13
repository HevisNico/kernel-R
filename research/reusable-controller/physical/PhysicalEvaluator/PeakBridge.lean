import PhysicalEvaluator.PeakError
import PhysicalEvaluator.ReadoutBridge

/-! Transfer a physical residual on the corrected response amplitude into
the existing log-gain readout contract. For a FIRE read this amplitude is
the early-read reconstruction including kappa, not the raw peak column.
The residual bound remains a physical premise: its admissible magnitude is
proved here, but no claim is made that a circuit actually achieves it. -/
namespace ReusableController.PhysicalEvaluator
open RecursiveLearning RecursiveLearning.Native KernelR.Hybrid
open RecordedData RecordedGains ReusableController.Adaptive

theorem preparation_recorded_amplitude_floor (k : Fin 7) :
    7 / 10 ≤ Real.exp (t6004p1Gain k) := by
  have lower : -(356674943 / 1000000000 : ℝ) ≤ t6004p1Lower k := by
    fin_cases k <;> norm_num [t6004p1Lower]
  have logBound : Real.log (7 / 10 : ℝ) ≤ t6004p1Gain k :=
    (log_seven_tenths_bounds.2.trans lower).trans (t6004p1Gain_bounds k).1
  simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 7 / 10)] using
    Real.exp_le_exp.mpr logBound

theorem practice_recorded_amplitude_floor (k : Fin 5) :
    7 / 10 ≤ Real.exp (t6004p2Gain k) := by
  have lower : -(356674943 / 1000000000 : ℝ) ≤ t6004p2Lower k := by
    fin_cases k <;> norm_num [t6004p2Lower]
  have logBound : Real.log (7 / 10 : ℝ) ≤ t6004p2Gain k :=
    (log_seven_tenths_bounds.2.trans lower).trans (t6004p2Gain_bounds k).1
  simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 7 / 10)] using
    Real.exp_le_exp.mpr logBound

theorem peak_residual_small {epsilonPeak : ℝ}
    (admissible : epsilonPeak ≤ 7 / 100010) : epsilonPeak < 7 / 10 := by
  linarith

theorem peak_residual_ratio_bound {epsilonPeak : ℝ}
    (admissible : epsilonPeak ≤ 7 / 100010) :
    epsilonPeak / (7 / 10 - epsilonPeak) ≤ 1 / 10000 := by
  have denominator : 0 < 7 / 10 - epsilonPeak := by
    have := peak_residual_small admissible
    linarith
  apply (div_le_iff₀ denominator).mpr
  linarith

/-- The epsilon parameter bounds the gap between the actual scalar response
amplitude and the reconstructed amplitude of every recorded read. It must
include extraction, early-read calibration and model-discrepancy errors;
none of them is inferred from the successful count comparison. -/
structure RecordedPeakResidualPremises (m : Nat) (reportedGain : Fin (m + 1) → ℝ)
    (level0 ell epsilonPeak : ℝ) (observed : Fin (m + 1) → Bool) where
  trueGain : Fin (m + 1) → ℝ
  charge : Fin (m + 1) → ℝ
  epsilonNonnegative : 0 ≤ epsilonPeak
  epsilonAdmissible : epsilonPeak ≤ 7 / 100010
  amplitudeResidual : ∀ k,
    |response 1 * Real.exp (trueGain k) - Real.exp (reportedGain k)| ≤ epsilonPeak
  chargeBand : ∀ k, 1 / 10 ≤ charge k ∧ charge k ≤ 1 / 10 + 1 / 10000
  observableSound : ∀ k, observed k = true →
    PulseFires (charge k) (Real.exp (trueGain k)) (level0 - ell)
  observableComplete : ∀ k,
    PulseFires (charge k) (Real.exp (trueGain k)) (level0 + ell) → observed k = true

abbrev PreparationPeakResidualPremises (epsilonPeak : ℝ) :=
  RecordedPeakResidualPremises 6 t6004p1Gain t6004p1NominalLevel0 t6004p1Ell
    epsilonPeak observedPreparation

abbrev PracticePeakResidualPremises (epsilonPeak : ℝ) :=
  RecordedPeakResidualPremises 4 t6004p2Gain t6004p2NominalLevel0 t6004p2Ell
    epsilonPeak observedPractice

/-- Generic transfer retains the explicit physical premises and replaces
only their amplitude residual with the derived log-gain residual. -/
noncomputable def RecordedPeakResidualPremises.toReadout {m reportedGain level0 ell epsilonPeak observed}
    (w : RecordedPeakResidualPremises m reportedGain level0 ell epsilonPeak observed)
    (amplitudeFloor : ∀ k, 7 / 10 ≤ Real.exp (reportedGain k)) :
    RecordedReadoutPremises m reportedGain level0 ell observed where
  trueGain := w.trueGain
  charge := w.charge
  readout := by
    intro k
    have transfer := scalarGain_error_of_amplitude (by norm_num : (0 : ℝ) < 7 / 10)
      (amplitudeFloor k) w.epsilonNonnegative (peak_residual_small w.epsilonAdmissible)
      (w.amplitudeResidual k)
    rw [Real.log_exp] at transfer
    exact transfer.trans (peak_residual_ratio_bound w.epsilonAdmissible)
  chargeBand := w.chargeBand
  observableSound := w.observableSound
  observableComplete := w.observableComplete

noncomputable def preparationReadoutOfPeakResidual {epsilonPeak : ℝ}
    (w : PreparationPeakResidualPremises epsilonPeak) : PreparationReadoutPremises :=
  w.toReadout preparation_recorded_amplitude_floor

noncomputable def practiceReadoutOfPeakResidual {epsilonPeak : ℝ}
    (w : PracticePeakResidualPremises epsilonPeak) : PracticeReadoutPremises :=
  w.toReadout practice_recorded_amplitude_floor

/-- A concrete admissible epsilon, not a measurement of physical error. -/
theorem example_peak_budget :
    (0 : ℝ) ≤ 1 / 20000 ∧ (1 / 20000 : ℝ) ≤ 7 / 100010 ∧
      (1 / 20000 : ℝ) / (7 / 10 - 1 / 20000) = 1 / 13999 := by
  norm_num

/-- Corrected-amplitude residuals imply the existing conditional controller
contract; all resting-charge and observation-envelope obligations remain. -/
theorem peak_residual_controller_contract {P : Type} {epsilonPreparation epsilonPractice : ℝ}
    (p : PreparationPeakResidualPremises epsilonPreparation)
    (q : PracticePeakResidualPremises epsilonPractice)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat)
    (menu : PolicyMenu P) (passes : (lesson.train ⟨6, 4⟩).retained = true) :
    let fixed := certifiedEnvironment
      (preparationEnvelopeCertificate
        (preparationEnvelopeOfReadout (preparationReadoutOfPeakResidual p))).toProbeCertificate
      (practiceEnvelopeCertificate
        (practiceEnvelopeOfReadout (practiceReadoutOfPeakResidual q))).toProbeCertificate
      lesson policies overhead deployments validationOverhead
    Ready ⟨6, 4⟩ (adaptAndSearch fixed menu).memory.live ∧
      referenceCost 6 4 lesson policies overhead deployments
        (adaptAndSearch fixed menu).memory.incumbent ≤
          referenceCost 6 4 lesson policies overhead deployments menu.seed :=
  readout_controller_contract (preparationReadoutOfPeakResidual p)
    (practiceReadoutOfPeakResidual q) lesson policies overhead deployments validationOverhead menu passes

end ReusableController.PhysicalEvaluator
