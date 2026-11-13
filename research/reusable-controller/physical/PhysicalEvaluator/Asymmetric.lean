import PhysicalEvaluator.Controller
import Search.AsymmetricNeedTolerance

/-! Finite asymmetric observation envelopes and their controller interface.
The directional scalar rule is fixed in Search.AsymmetricNeedTolerance.
Only a constant mathematical extension is used beyond the last finite read;
no claim is made about a physical gain trajectory after that read. Numerical
eligibility remains separate from reference-to-actual transfer and observation
premises, including their applicability to noisy and reconstructed readings. -/
namespace ReusableController.PhysicalEvaluator
open RecursiveLearning RecursiveLearning.Native KernelR.Hybrid
open ReusableController.Adaptive

structure FiniteAsymmetricCertificate (m : Nat) where
  level0 : ℝ
  dose0 : ℝ
  aSilent : ℝ
  aFire : ℝ
  BSilent : ℝ
  BFire : ℝ
  ell : ℝ
  gain : Fin (m + 1) → ℝ
  charge : Fin (m + 1) → ℝ
  observed : Fin (m + 1) → Bool
  doseNonnegative : 0 ≤ dose0
  ellNonnegative : 0 ≤ ell
  levelFloor : 19 / 20 ≤ level0 - ell
  gainUpper : gain 0 - needCentre level0 dose0 m ≤ aSilent
  gainLower : needCentre level0 dose0 m - gain 0 ≤ aFire
  cumulativeUpper : ∀ k, k.val < m → gain k - gain 0 - (k.val : ℝ) * dose0 ≤ BSilent
  cumulativeLower : gain 0 + (m : ℝ) * dose0 - gain (Fin.last m) ≤ BFire
  chargeBand : ∀ k, 1 / 10 ≤ charge k ∧ charge k ≤ 1 / 10 + 1 / 10000
  silenceRoom : aSilent + BSilent + 20 / 17 * ell + 1 / 8000 < dose0 / 2
  fireRoom : aFire + BFire + 20 / 17 * ell ≤ dose0 / 2
  observableSound : ∀ k, observed k = true →
    PulseFires (charge k) (Real.exp (gain k)) (level0 - ell)
  observableComplete : ∀ k,
    PulseFires (charge k) (Real.exp (gain k)) (level0 + ell) → observed k = true

private noncomputable def FiniteAsymmetricCertificate.clampedGain {m}
    (certificate : FiniteAsymmetricCertificate m) (k : Nat) : ℝ :=
  certificate.gain ⟨min k m, Nat.lt_succ_of_le (Nat.min_le_right k m)⟩

private theorem FiniteAsymmetricCertificate.clampedGain_at {m}
    (certificate : FiniteAsymmetricCertificate m) (k : Fin (m + 1)) :
    certificate.clampedGain k.val = certificate.gain k := by
  have bound : k.val ≤ m := Nat.le_of_lt_succ k.isLt
  simp [clampedGain, Nat.min_eq_left bound]

private theorem FiniteAsymmetricCertificate.clamped_need {m}
    (certificate : FiniteAsymmetricCertificate m) (level : ℝ)
    (floor : 19 / 20 ≤ level) (levelTol : |level - certificate.level0| ≤ certificate.ell) :
    NeedAlong level certificate.clampedGain m := by
  have nominalFloor : 19 / 20 ≤ certificate.level0 := by
    linarith [certificate.levelFloor, certificate.ellNonnegative]
  apply needAlong_of_asymmetric_cumulative_tolerance certificate.clampedGain
    floor nominalFloor certificate.doseNonnegative
  · intro n after
    simp [clampedGain, Nat.min_eq_right after]
  · simpa [clampedGain] using certificate.gainUpper
  · simpa [clampedGain] using certificate.gainLower
  · intro k before
    simpa [clampedGain, Nat.min_eq_left before.le] using
      certificate.cumulativeUpper ⟨k, Nat.lt_succ_of_le before.le⟩ before
  · simpa [clampedGain, Fin.last] using certificate.cumulativeLower
  · exact levelTol
  · exact certificate.silenceRoom
  · exact certificate.fireRoom

theorem FiniteAsymmetricCertificate.silent_before {m}
    (certificate : FiniteAsymmetricCertificate m) (k : Fin (m + 1)) (before : k.val < m) :
    certificate.observed k = false := by
  have tolerance : |certificate.level0 - certificate.ell - certificate.level0| ≤ certificate.ell := by
    simp [sub_sub_cancel_left, abs_of_nonneg certificate.ellNonnegative]
  have need := certificate.clamped_need (certificate.level0 - certificate.ell)
    certificate.levelFloor tolerance
  have silent := need.1 k.val before (certificate.charge k)
    (certificate.chargeBand k).1 (certificate.chargeBand k).2
  rw [certificate.clampedGain_at k] at silent
  cases observation : certificate.observed k with
  | false => rfl
  | true => exact False.elim (silent (certificate.observableSound k observation))

theorem FiniteAsymmetricCertificate.fires_at {m}
    (certificate : FiniteAsymmetricCertificate m) : certificate.observed (Fin.last m) = true := by
  have floor : 19 / 20 ≤ certificate.level0 + certificate.ell := by
    linarith [certificate.levelFloor, certificate.ellNonnegative]
  have tolerance : |certificate.level0 + certificate.ell - certificate.level0| ≤ certificate.ell := by
    simp [abs_of_nonneg certificate.ellNonnegative]
  have need := certificate.clamped_need (certificate.level0 + certificate.ell) floor tolerance
  have fires := need.2 m le_rfl (certificate.charge (Fin.last m))
    (certificate.chargeBand (Fin.last m)).1 (certificate.chargeBand (Fin.last m)).2
  have atLast := certificate.clampedGain_at (Fin.last m)
  change certificate.clampedGain m = certificate.gain (Fin.last m) at atLast
  rw [atLast] at fires
  exact certificate.observableComplete (Fin.last m) fires

def FiniteAsymmetricCertificate.readings {m} (certificate : FiniteAsymmetricCertificate m) : List Bool :=
  List.ofFn certificate.observed

theorem FiniteAsymmetricCertificate.readings_shape {m}
    (certificate : FiniteAsymmetricCertificate m) :
    certificate.readings = List.replicate m false ++ [true] := by
  have priorObservations : (fun k : Fin m => certificate.observed k.castSucc) = fun _ => false := by
    funext k
    exact certificate.silent_before k.castSucc k.isLt
  rw [readings, List.ofFn_succ_last, priorObservations, List.ofFn_const, certificate.fires_at]

theorem FiniteAsymmetricCertificate.firstFire_exact {m}
    (certificate : FiniteAsymmetricCertificate m) : firstFire certificate.readings = some m := by
  rw [certificate.readings_shape, firstFire_false_prefix]

theorem FiniteAsymmetricCertificate.count_exact {m}
    (certificate : FiniteAsymmetricCertificate m) : decodedCount certificate.readings = m := by
  simp [decodedCount, certificate.firstFire_exact]

/-- Every old symmetric finite-envelope certificate embeds without changing
its recorded observations, charge or gain. No old eligible port is excluded
by the directional rule when its existing physical premises hold. -/
noncomputable def FiniteEnvelopeCertificate.toAsymmetric {m}
    (certificate : FiniteEnvelopeCertificate m) : FiniteAsymmetricCertificate m where
  level0 := certificate.level0
  dose0 := certificate.dose0
  aSilent := certificate.a
  aFire := certificate.a
  BSilent := certificate.B
  BFire := certificate.B
  ell := certificate.ell
  gain := certificate.gain
  charge := certificate.charge
  observed := certificate.observed
  doseNonnegative := by
    have aNonnegative := (abs_nonneg _).trans certificate.gainBound
    have BNonnegative := (abs_nonneg _).trans (certificate.cumulativeBound 0)
    linarith [certificate.room, certificate.ellNonnegative]
  ellNonnegative := certificate.ellNonnegative
  levelFloor := certificate.levelFloor
  gainUpper := (abs_le.mp certificate.gainBound).2
  gainLower := by
    have lower := (abs_le.mp certificate.gainBound).1
    linarith
  cumulativeUpper := fun k _ => (abs_le.mp (certificate.cumulativeBound k)).2
  cumulativeLower := by
    have lower := (abs_le.mp (certificate.cumulativeBound (Fin.last m))).1
    simp only [Fin.val_last] at lower
    linarith
  chargeBand := certificate.chargeBand
  silenceRoom := certificate.room
  fireRoom := by linarith [certificate.room]
  observableSound := certificate.observableSound
  observableComplete := certificate.observableComplete

theorem FiniteEnvelopeCertificate.toAsymmetric_readings {m}
    (certificate : FiniteEnvelopeCertificate m) :
    certificate.toAsymmetric.readings = certificate.readings := rfl

theorem accuracy_from_asymmetric {p q : Nat}
    (preparation : FiniteAsymmetricCertificate p) (practice : FiniteAsymmetricCertificate q) :
    LessonAccurate ⟨p, q⟩
      (marginOracle (decodedCount preparation.readings) (decodedCount practice.readings)) 0 := by
  rw [preparation.count_exact, practice.count_exact]
  intro index lesson
  simp [lessonMargin, marginOracle]

def asymmetricOracle {p q : Nat}
    (preparation : FiniteAsymmetricCertificate p) (practice : FiniteAsymmetricCertificate q) : LessonOracle :=
  marginOracle (decodedCount preparation.readings) (decodedCount practice.readings)

/-- This evaluator uses directional certificates directly. It does not
inflate their bounds into a possibly invalid old symmetric certificate. -/
def asymmetricEnvironment {P : Type} {p q : Nat}
    (preparation : FiniteAsymmetricCertificate p) (practice : FiniteAsymmetricCertificate q)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat) :
    Evaluation P where
  need := ⟨p, q⟩
  initialLesson := lesson
  oracle := asymmetricOracle preparation practice
  lessonTolerance := 0
  policies := policies
  report := fun choice =>
    (policyCost (asymmetricOracle preparation practice) 0 (initial lesson)
      overhead deployments (policies choice) : Int)
  costTolerance := 0
  overhead := overhead
  deployments := deployments
  validationOverhead := validationOverhead

theorem asymmetric_environment_sound {P : Type} {p q : Nat}
    (preparation : FiniteAsymmetricCertificate p) (practice : FiniteAsymmetricCertificate q)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat)
    (passes : (lesson.train ⟨p, q⟩).retained = true) :
    (asymmetricEnvironment preparation practice lesson policies overhead deployments validationOverhead).Sound := by
  refine ⟨passes, accuracy_from_asymmetric preparation practice, ?_⟩
  intro choice
  simp [asymmetricEnvironment, Evaluation.trueCost]

theorem asymmetric_cost_eq_reference {P : Type} {p q : Nat}
    (preparation : FiniteAsymmetricCertificate p) (practice : FiniteAsymmetricCertificate q)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat) (choice : P) :
    (asymmetricEnvironment preparation practice lesson policies overhead deployments validationOverhead).trueCost choice =
      referenceCost p q lesson policies overhead deployments choice := by
  simp [Evaluation.trueCost, asymmetricEnvironment, asymmetricOracle,
    preparation.count_exact, practice.count_exact, referenceCost]

theorem asymmetric_controller_contract {P : Type} {p q : Nat}
    (preparation : FiniteAsymmetricCertificate p) (practice : FiniteAsymmetricCertificate q)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat)
    (menu : PolicyMenu P) (passes : (lesson.train ⟨p, q⟩).retained = true) :
    let fixed := asymmetricEnvironment preparation practice lesson policies overhead deployments validationOverhead
    Ready ⟨p, q⟩ (adaptAndSearch fixed menu).memory.live ∧
      referenceCost p q lesson policies overhead deployments (adaptAndSearch fixed menu).memory.incumbent ≤
        referenceCost p q lesson policies overhead deployments menu.seed := by
  dsimp only
  have result := adapt_and_search_contract
    (asymmetricEnvironment preparation practice lesson policies overhead deployments validationOverhead) menu
    (asymmetric_environment_sound preparation practice lesson policies overhead deployments validationOverhead passes)
  refine ⟨result.1, ?_⟩
  simpa only [asymmetric_cost_eq_reference] using result.2.2.2.2

/-- Numerical directional eligibility; no physical gain or charge vector is
stored here. The single reference centering budget is symmetric, while the
two cumulative budgets refer to different directions and index sets. -/
structure AsymmetricEntry (m : Nat) where
  cellId : Nat
  port : Nat
  level0 : ℝ
  dose0 : ℝ
  baseA : ℝ
  baseBSilent : ℝ
  baseBFire : ℝ
  epsilon : ℝ
  ell : ℝ
  observed : Fin (m + 1) → Bool
  doseNonnegative : 0 ≤ dose0
  ellNonnegative : 0 ≤ ell
  levelFloor : 19 / 20 ≤ level0 - ell
  silenceRoom : (baseA + epsilon) + (baseBSilent + 2 * epsilon) +
    20 / 17 * ell + 1 / 8000 < dose0 / 2
  fireRoom : (baseA + epsilon) + (baseBFire + 2 * epsilon) + 20 / 17 * ell ≤ dose0 / 2

structure AsymmetricTransferPremises {m : Nat} (entry : AsymmetricEntry m) where
  referenceGain : Fin (m + 1) → ℝ
  actualGain : Fin (m + 1) → ℝ
  charge : Fin (m + 1) → ℝ
  referenceCentre : |referenceGain 0 - needCentre entry.level0 entry.dose0 m| ≤ entry.baseA
  referenceCumulativeUpper : ∀ k, k.val < m →
    referenceGain k - referenceGain 0 - (k.val : ℝ) * entry.dose0 ≤ entry.baseBSilent
  referenceCumulativeLower :
    referenceGain 0 + (m : ℝ) * entry.dose0 - referenceGain (Fin.last m) ≤ entry.baseBFire
  transferError : ∀ k, |actualGain k - referenceGain k| ≤ entry.epsilon
  chargeBand : ∀ k, 1 / 10 ≤ charge k ∧ charge k ≤ 1 / 10 + 1 / 10000
  observableSound : ∀ k, entry.observed k = true →
    PulseFires (charge k) (Real.exp (actualGain k)) (entry.level0 - entry.ell)
  observableComplete : ∀ k,
    PulseFires (charge k) (Real.exp (actualGain k)) (entry.level0 + entry.ell) → entry.observed k = true

/-- Actual-read errors pay epsilon at initialization and both endpoint
errors in either cumulative direction, exactly as in the symmetric bridge. -/
noncomputable def AsymmetricEntry.certificate {m : Nat} (entry : AsymmetricEntry m)
    (physical : AsymmetricTransferPremises entry) : FiniteAsymmetricCertificate m where
  level0 := entry.level0
  dose0 := entry.dose0
  aSilent := entry.baseA + entry.epsilon
  aFire := entry.baseA + entry.epsilon
  BSilent := entry.baseBSilent + 2 * entry.epsilon
  BFire := entry.baseBFire + 2 * entry.epsilon
  ell := entry.ell
  gain := physical.actualGain
  charge := physical.charge
  observed := entry.observed
  doseNonnegative := entry.doseNonnegative
  ellNonnegative := entry.ellNonnegative
  levelFloor := entry.levelFloor
  gainUpper := by
    have reference := (abs_le.mp physical.referenceCentre).2
    have residual := (abs_le.mp (physical.transferError 0)).2
    linarith
  gainLower := by
    have reference := (abs_le.mp physical.referenceCentre).1
    have residual := (abs_le.mp (physical.transferError 0)).1
    linarith
  cumulativeUpper := by
    intro k before
    have reference := physical.referenceCumulativeUpper k before
    have startError := (abs_le.mp (physical.transferError 0)).1
    have currentError := (abs_le.mp (physical.transferError k)).2
    linarith
  cumulativeLower := by
    have reference := physical.referenceCumulativeLower
    have startError := (abs_le.mp (physical.transferError 0)).2
    have currentError := (abs_le.mp (physical.transferError (Fin.last m))).1
    linarith
  chargeBand := physical.chargeBand
  silenceRoom := entry.silenceRoom
  fireRoom := entry.fireRoom
  observableSound := physical.observableSound
  observableComplete := physical.observableComplete

def AsymmetricEntry.readings {m : Nat} (entry : AsymmetricEntry m) : List Bool :=
  List.ofFn entry.observed

theorem AsymmetricEntry.certificate_readings {m : Nat} (entry : AsymmetricEntry m)
    (physical : AsymmetricTransferPremises entry) :
    (entry.certificate physical).readings = entry.readings := rfl

theorem AsymmetricEntry.firstFire_exact {m : Nat} (entry : AsymmetricEntry m)
    (physical : AsymmetricTransferPremises entry) : firstFire entry.readings = some m :=
  (entry.certificate physical).firstFire_exact

theorem AsymmetricEntry.count_exact {m : Nat} (entry : AsymmetricEntry m)
    (physical : AsymmetricTransferPremises entry) : decodedCount entry.readings = m :=
  (entry.certificate physical).count_exact

theorem asymmetric_entry_controller_contract {P : Type} {p q : Nat}
    (preparation : AsymmetricEntry p) (practice : AsymmetricEntry q)
    (preparationPhysical : AsymmetricTransferPremises preparation)
    (practicePhysical : AsymmetricTransferPremises practice)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat)
    (menu : PolicyMenu P) (passes : (lesson.train ⟨p, q⟩).retained = true) :
    let fixed := asymmetricEnvironment (preparation.certificate preparationPhysical)
      (practice.certificate practicePhysical) lesson policies overhead deployments validationOverhead
    Ready ⟨p, q⟩ (adaptAndSearch fixed menu).memory.live ∧
      referenceCost p q lesson policies overhead deployments (adaptAndSearch fixed menu).memory.incumbent ≤
        referenceCost p q lesson policies overhead deployments menu.seed :=
  asymmetric_controller_contract (preparation.certificate preparationPhysical)
    (practice.certificate practicePhysical) lesson policies overhead deployments validationOverhead menu passes

end ReusableController.PhysicalEvaluator
