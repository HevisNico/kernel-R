import PhysicalEvaluator.Controller
import PhysicalEvaluator.RecordedData

/-! The public arithmetic discharges room and threshold-floor premises.
It does not manufacture the remaining physical interpretation of the CSV.
These constructors make the exact remaining premises reviewable. -/
namespace ReusableController.PhysicalEvaluator
open RecursiveLearning RecursiveLearning.Native KernelR.Hybrid
open RecordedData ReusableController.Adaptive

structure RecordedPremises (m : Nat) (level0 dose0 a B ell : ℝ)
    (observed : Fin (m + 1) → Bool) where
  gain : Fin (m + 1) → ℝ
  level : Fin (m + 1) → ℝ
  charge : Fin (m + 1) → ℝ
  gainBound : |gain 0 - needCentre level0 dose0 m| ≤ a
  cumulativeBound : ∀ k, |gain k - gain 0 - (k.val : ℝ) * dose0| ≤ B
  levelBound : ∀ k, |level k - level0| ≤ ell
  chargeBand : ∀ k, 1 / 10 ≤ charge k ∧ charge k ≤ 1 / 10 + 1 / 10000
  scalarCorrespondence : ∀ k, observed k = true ↔
    PulseFires (charge k) (Real.exp (gain k)) (level k)

def observedPreparation (k : Fin 7) : Bool := t6004p1Readings[k.val]!
def observedPractice (k : Fin 5) : Bool := t6004p2Readings[k.val]!

abbrev PreparationPremises := RecordedPremises 6 t6004p1NominalLevel0 t6004p1Dose0
  t6004p1A t6004p1B t6004p1Ell observedPreparation
abbrev PracticePremises := RecordedPremises 4 t6004p2NominalLevel0 t6004p2Dose0
  t6004p2A t6004p2B t6004p2Ell observedPractice

noncomputable def preparationCertificate (w : PreparationPremises) : FiniteProbeCertificate 6 where
  level0 := t6004p1NominalLevel0
  dose0 := t6004p1Dose0
  a := t6004p1A
  B := t6004p1B
  ell := t6004p1Ell
  gain := w.gain
  level := w.level
  charge := w.charge
  observed := observedPreparation
  levelFloor := t6004p1NominalFloor
  gainBound := w.gainBound
  cumulativeBound := w.cumulativeBound
  levelBound := w.levelBound
  chargeBand := w.chargeBand
  room := t6004p1CalibratedRoom
  scalarCorrespondence := w.scalarCorrespondence

noncomputable def practiceCertificate (w : PracticePremises) : FiniteProbeCertificate 4 where
  level0 := t6004p2NominalLevel0
  dose0 := t6004p2Dose0
  a := t6004p2A
  B := t6004p2B
  ell := t6004p2Ell
  gain := w.gain
  level := w.level
  charge := w.charge
  observed := observedPractice
  levelFloor := t6004p2NominalFloor
  gainBound := w.gainBound
  cumulativeBound := w.cumulativeBound
  levelBound := w.levelBound
  chargeBand := w.chargeBand
  room := t6004p2CalibratedRoom
  scalarCorrespondence := w.scalarCorrespondence

theorem recorded_prefixes (p : PreparationPremises) (q : PracticePremises) :
    (preparationCertificate p).readings = t6004p1Prefix ∧
    (practiceCertificate q).readings = t6004p2Prefix := by
  change List.ofFn observedPreparation = t6004p1Prefix ∧
    List.ofFn observedPractice = t6004p2Prefix
  decide

/-- Room/floor are proved from published numerical constants, while the
remaining physical/model correspondence is supplied explicitly above. -/
theorem recorded_controller_contract {P : Type}
    (p : PreparationPremises) (q : PracticePremises)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat)
    (menu : PolicyMenu P) (passes : (lesson.train ⟨6, 4⟩).retained = true) :
    let fixed := certifiedEnvironment (preparationCertificate p) (practiceCertificate q)
      lesson policies overhead deployments validationOverhead
    Ready ⟨6, 4⟩ (adaptAndSearch fixed menu).memory.live ∧
      referenceCost 6 4 lesson policies overhead deployments (adaptAndSearch fixed menu).memory.incumbent ≤
        referenceCost 6 4 lesson policies overhead deployments menu.seed :=
  certified_controller_nondegradation (preparationCertificate p) (practiceCertificate q)
    lesson policies overhead deployments validationOverhead menu passes

/-- Recorded-data entry interface for disturbances that may vary during a
read. No physical constant level is supplied; the lower/upper implications
remain explicit obligations about the actual finite observations. -/
structure RecordedEnvelopePremises (m : Nat) (level0 dose0 a B ell : ℝ)
    (observed : Fin (m + 1) → Bool) where
  gain : Fin (m + 1) → ℝ
  charge : Fin (m + 1) → ℝ
  gainBound : |gain 0 - needCentre level0 dose0 m| ≤ a
  cumulativeBound : ∀ k, |gain k - gain 0 - (k.val : ℝ) * dose0| ≤ B
  chargeBand : ∀ k, 1 / 10 ≤ charge k ∧ charge k ≤ 1 / 10 + 1 / 10000
  observableSound : ∀ k, observed k = true →
    PulseFires (charge k) (Real.exp (gain k)) (level0 - ell)
  observableComplete : ∀ k,
    PulseFires (charge k) (Real.exp (gain k)) (level0 + ell) → observed k = true

abbrev PreparationEnvelopePremises := RecordedEnvelopePremises 6 t6004p1NominalLevel0 t6004p1Dose0
  t6004p1A t6004p1B t6004p1Ell observedPreparation
abbrev PracticeEnvelopePremises := RecordedEnvelopePremises 4 t6004p2NominalLevel0 t6004p2Dose0
  t6004p2A t6004p2B t6004p2Ell observedPractice

noncomputable def preparationEnvelopeCertificate (w : PreparationEnvelopePremises) :
    FiniteEnvelopeCertificate 6 where
  level0 := t6004p1NominalLevel0
  dose0 := t6004p1Dose0
  a := t6004p1A
  B := t6004p1B
  ell := t6004p1Ell
  gain := w.gain
  charge := w.charge
  observed := observedPreparation
  ellNonnegative := by norm_num [t6004p1Ell]
  levelFloor := t6004p1NominalFloor
  gainBound := w.gainBound
  cumulativeBound := w.cumulativeBound
  chargeBand := w.chargeBand
  room := t6004p1CalibratedRoom
  observableSound := w.observableSound
  observableComplete := w.observableComplete

noncomputable def practiceEnvelopeCertificate (w : PracticeEnvelopePremises) :
    FiniteEnvelopeCertificate 4 where
  level0 := t6004p2NominalLevel0
  dose0 := t6004p2Dose0
  a := t6004p2A
  B := t6004p2B
  ell := t6004p2Ell
  gain := w.gain
  charge := w.charge
  observed := observedPractice
  ellNonnegative := by norm_num [t6004p2Ell]
  levelFloor := t6004p2NominalFloor
  gainBound := w.gainBound
  cumulativeBound := w.cumulativeBound
  chargeBand := w.chargeBand
  room := t6004p2CalibratedRoom
  observableSound := w.observableSound
  observableComplete := w.observableComplete

/-- The older exact-level interface can use the envelope's logical witness.
This conversion does not identify that witness with a physical constant. -/
noncomputable def FiniteEnvelopeCertificate.toRecordedPremises {m}
    (certificate : FiniteEnvelopeCertificate m) :
    RecordedPremises m certificate.level0 certificate.dose0 certificate.a certificate.B
      certificate.ell certificate.observed where
  gain := certificate.gain
  level := certificate.effectiveLevel
  charge := certificate.charge
  gainBound := certificate.gainBound
  cumulativeBound := certificate.cumulativeBound
  levelBound := certificate.effectiveLevel_bound
  chargeBand := certificate.chargeBand
  scalarCorrespondence := certificate.effectiveLevel_correspondence

noncomputable def preparationPremisesOfEnvelope (w : PreparationEnvelopePremises) :
    PreparationPremises := (preparationEnvelopeCertificate w).toRecordedPremises

noncomputable def practicePremisesOfEnvelope (w : PracticeEnvelopePremises) :
    PracticePremises := (practiceEnvelopeCertificate w).toRecordedPremises

theorem recorded_envelope_prefixes (p : PreparationEnvelopePremises) (q : PracticeEnvelopePremises) :
    (preparationEnvelopeCertificate p).readings = t6004p1Prefix ∧
    (practiceEnvelopeCertificate q).readings = t6004p2Prefix := by
  change List.ofFn observedPreparation = t6004p1Prefix ∧
    List.ofFn observedPractice = t6004p2Prefix
  decide

/-- The recorded numerical gate and the supplied intra-read envelopes feed
the controller theorem directly, without a constant physical-level premise. -/
theorem recorded_envelope_controller_contract {P : Type}
    (p : PreparationEnvelopePremises) (q : PracticeEnvelopePremises)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat)
    (menu : PolicyMenu P) (passes : (lesson.train ⟨6, 4⟩).retained = true) :
    let fixed := certifiedEnvironment (preparationEnvelopeCertificate p).toProbeCertificate
      (practiceEnvelopeCertificate q).toProbeCertificate lesson policies overhead deployments validationOverhead
    Ready ⟨6, 4⟩ (adaptAndSearch fixed menu).memory.live ∧
      referenceCost 6 4 lesson policies overhead deployments (adaptAndSearch fixed menu).memory.incumbent ≤
        referenceCost 6 4 lesson policies overhead deployments menu.seed :=
  envelope_controller_nondegradation (preparationEnvelopeCertificate p) (practiceEnvelopeCertificate q)
    lesson policies overhead deployments validationOverhead menu passes

end ReusableController.PhysicalEvaluator
