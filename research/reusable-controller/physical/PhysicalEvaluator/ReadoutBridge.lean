import PhysicalEvaluator.RecordedGains
import PhysicalEvaluator.RecordedBridge

/-! The recorded peak/early-read calculations discharge the centering and
cumulative premises. What remains is an explicit physical readout residual,
the resting-charge band, and the two observation-envelope implications.
Neither a gain-budget premise nor an exact-count premise is supplied here. -/
namespace ReusableController.PhysicalEvaluator
open RecursiveLearning RecursiveLearning.Native KernelR.Hybrid
open RecordedData RecordedGains ReusableController.Adaptive

/-- A bound on true gain relative to the normalized recorded calculation.
It is an external physical premise, not a consequence of matching counts or
of the numerical slack checked for this particular recorded benchmark. -/
structure RecordedReadoutPremises (m : Nat) (reportedGain : Fin (m + 1) → ℝ)
    (level0 ell : ℝ) (observed : Fin (m + 1) → Bool) where
  trueGain : Fin (m + 1) → ℝ
  charge : Fin (m + 1) → ℝ
  readout : ∀ k, |trueGain k - scalarGain (reportedGain k)| ≤ 1 / 10000
  chargeBand : ∀ k, 1 / 10 ≤ charge k ∧ charge k ≤ 1 / 10 + 1 / 10000
  observableSound : ∀ k, observed k = true →
    PulseFires (charge k) (Real.exp (trueGain k)) (level0 - ell)
  observableComplete : ∀ k,
    PulseFires (charge k) (Real.exp (trueGain k)) (level0 + ell) → observed k = true

abbrev PreparationReadoutPremises := RecordedReadoutPremises 6 t6004p1Gain
  t6004p1NominalLevel0 t6004p1Ell observedPreparation

abbrev PracticeReadoutPremises := RecordedReadoutPremises 4 t6004p2Gain
  t6004p2NominalLevel0 t6004p2Ell observedPractice

theorem preparation_readout_gain_bounds (w : PreparationReadoutPremises) :
    |w.trueGain 0 - needCentre t6004p1NominalLevel0 t6004p1Dose0 6| ≤ t6004p1A ∧
      ∀ k, |w.trueGain k - w.trueGain 0 - (k.val : ℝ) * t6004p1Dose0| ≤ t6004p1B := by
  constructor
  · exact (centre_error_transfer (by norm_num [t6004p1NominalLevel0])
      t6004p1Centre (w.readout 0)).trans t6004p1ResidualRoom.1
  · intro k
    have transfer := cumulative_error_transfer (t6004p1Cumulative k) (w.readout 0) (w.readout k)
    have room := t6004p1ResidualRoom.2
    linarith

theorem practice_readout_gain_bounds (w : PracticeReadoutPremises) :
    |w.trueGain 0 - needCentre t6004p2NominalLevel0 t6004p2Dose0 4| ≤ t6004p2A ∧
      ∀ k, |w.trueGain k - w.trueGain 0 - (k.val : ℝ) * t6004p2Dose0| ≤ t6004p2B := by
  constructor
  · exact (centre_error_transfer (by norm_num [t6004p2NominalLevel0])
      t6004p2Centre (w.readout 0)).trans t6004p2ResidualRoom.1
  · intro k
    have transfer := cumulative_error_transfer (t6004p2Cumulative k) (w.readout 0) (w.readout k)
    have room := t6004p2ResidualRoom.2
    linarith

noncomputable def preparationEnvelopeOfReadout (w : PreparationReadoutPremises) :
    PreparationEnvelopePremises where
  gain := w.trueGain
  charge := w.charge
  gainBound := (preparation_readout_gain_bounds w).1
  cumulativeBound := (preparation_readout_gain_bounds w).2
  chargeBand := w.chargeBand
  observableSound := w.observableSound
  observableComplete := w.observableComplete

noncomputable def practiceEnvelopeOfReadout (w : PracticeReadoutPremises) :
    PracticeEnvelopePremises where
  gain := w.trueGain
  charge := w.charge
  gainBound := (practice_readout_gain_bounds w).1
  cumulativeBound := (practice_readout_gain_bounds w).2
  chargeBand := w.chargeBand
  observableSound := w.observableSound
  observableComplete := w.observableComplete

/-- Finite observations are decoded by the same certified controller used
in the envelope bridge. The true needs are six and four under the stated
readout and observation premises; these needs are not count assumptions. -/
theorem readout_controller_contract {P : Type}
    (p : PreparationReadoutPremises) (q : PracticeReadoutPremises)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat)
    (menu : PolicyMenu P) (passes : (lesson.train ⟨6, 4⟩).retained = true) :
    let fixed := certifiedEnvironment
      (preparationEnvelopeCertificate (preparationEnvelopeOfReadout p)).toProbeCertificate
      (practiceEnvelopeCertificate (practiceEnvelopeOfReadout q)).toProbeCertificate
      lesson policies overhead deployments validationOverhead
    Ready ⟨6, 4⟩ (adaptAndSearch fixed menu).memory.live ∧
      referenceCost 6 4 lesson policies overhead deployments
        (adaptAndSearch fixed menu).memory.incumbent ≤
          referenceCost 6 4 lesson policies overhead deployments menu.seed :=
  recorded_envelope_controller_contract (preparationEnvelopeOfReadout p)
    (practiceEnvelopeOfReadout q) lesson policies overhead deployments validationOverhead menu passes

end ReusableController.PhysicalEvaluator
