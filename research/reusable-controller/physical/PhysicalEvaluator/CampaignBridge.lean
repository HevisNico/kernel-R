import PhysicalEvaluator.Controller

/-! Campaign-wide numerical entries and an explicit physical transfer boundary.
An eligible entry contains the recorded observations and numerical budgets,
but no physical gain/charge trajectory. The transfer premises below must apply
to every actual read, including noisy and early-read reconstructed observations.
A residual established on a noiseless campaign does not discharge those
premises merely because the cell identifier or observed count agrees. -/
namespace ReusableController.PhysicalEvaluator
open RecursiveLearning RecursiveLearning.Native KernelR.Hybrid
open ReusableController.Adaptive

/-- Published identifiers, observations and arithmetic eligibility only.
The enlarged budget pays epsilon once at the initial state and twice in a
cumulative difference. There is no physical-truth field in this record. -/
structure CampaignEntry (m : Nat) where
  cellId : Nat
  port : Nat
  level0 : ℝ
  dose0 : ℝ
  baseA : ℝ
  baseB : ℝ
  epsilon : ℝ
  ell : ℝ
  observed : Fin (m + 1) → Bool
  ellNonnegative : 0 ≤ ell
  levelFloor : 19 / 20 ≤ level0 - ell
  room : (baseA + epsilon) + (baseB + 2 * epsilon) +
    20 / 17 * ell + 1 / 8000 < dose0 / 2

/-- Applicability of a reference residual to the actual finite observation
sequence is explicit. In particular, transferError is not inferred from a
noiseless fit, kappa calibration, campaign membership or a matching count. -/
structure CampaignTransferPremises {m : Nat} (entry : CampaignEntry m) where
  referenceGain : Fin (m + 1) → ℝ
  actualGain : Fin (m + 1) → ℝ
  charge : Fin (m + 1) → ℝ
  referenceCentre : |referenceGain 0 - needCentre entry.level0 entry.dose0 m| ≤ entry.baseA
  referenceCumulative : ∀ k,
    |referenceGain k - referenceGain 0 - (k.val : ℝ) * entry.dose0| ≤ entry.baseB
  transferError : ∀ k, |actualGain k - referenceGain k| ≤ entry.epsilon
  chargeBand : ∀ k, 1 / 10 ≤ charge k ∧ charge k ≤ 1 / 10 + 1 / 10000
  observableSound : ∀ k, entry.observed k = true →
    PulseFires (charge k) (Real.exp (actualGain k)) (entry.level0 - entry.ell)
  observableComplete : ∀ k,
    PulseFires (charge k) (Real.exp (actualGain k)) (entry.level0 + entry.ell) →
      entry.observed k = true

theorem CampaignTransferPremises.transferred_bounds {m : Nat} {entry : CampaignEntry m}
    (physical : CampaignTransferPremises entry) :
    |physical.actualGain 0 - needCentre entry.level0 entry.dose0 m| ≤ entry.baseA + entry.epsilon ∧
      ∀ k, |physical.actualGain k - physical.actualGain 0 - (k.val : ℝ) * entry.dose0| ≤
        entry.baseB + 2 * entry.epsilon := by
  obtain ⟨initialLower, initialUpper⟩ := abs_le.mp (physical.transferError 0)
  constructor
  · obtain ⟨referenceLower, referenceUpper⟩ := abs_le.mp physical.referenceCentre
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro k
    obtain ⟨currentLower, currentUpper⟩ := abs_le.mp (physical.transferError k)
    obtain ⟨referenceLower, referenceUpper⟩ := abs_le.mp (physical.referenceCumulative k)
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Numeric entries become scalar-envelope certificates only with the
separate actual-read transfer and observation obligations. -/
noncomputable def CampaignEntry.certificate {m : Nat} (entry : CampaignEntry m)
    (physical : CampaignTransferPremises entry) : FiniteEnvelopeCertificate m where
  level0 := entry.level0
  dose0 := entry.dose0
  a := entry.baseA + entry.epsilon
  B := entry.baseB + 2 * entry.epsilon
  ell := entry.ell
  gain := physical.actualGain
  charge := physical.charge
  observed := entry.observed
  ellNonnegative := entry.ellNonnegative
  levelFloor := entry.levelFloor
  gainBound := physical.transferred_bounds.1
  cumulativeBound := physical.transferred_bounds.2
  chargeBand := physical.chargeBand
  room := entry.room
  observableSound := physical.observableSound
  observableComplete := physical.observableComplete

def CampaignEntry.readings {m : Nat} (entry : CampaignEntry m) : List Bool :=
  List.ofFn entry.observed

theorem CampaignEntry.certificate_readings {m : Nat} (entry : CampaignEntry m)
    (physical : CampaignTransferPremises entry) :
    (entry.certificate physical).readings = entry.readings := rfl

theorem CampaignEntry.readings_shape {m : Nat} (entry : CampaignEntry m)
    (physical : CampaignTransferPremises entry) :
    entry.readings = List.replicate m false ++ [true] :=
  (entry.certificate physical).readings_shape

theorem CampaignEntry.firstFire_exact {m : Nat} (entry : CampaignEntry m)
    (physical : CampaignTransferPremises entry) : firstFire entry.readings = some m :=
  (entry.certificate physical).firstFire_exact

theorem CampaignEntry.count_exact {m : Nat} (entry : CampaignEntry m)
    (physical : CampaignTransferPremises entry) : decodedCount entry.readings = m :=
  (entry.certificate physical).count_exact

/-- A failed arithmetic room test cannot supply the strict certificate gate,
even when the observed and predicted counts happen to agree. -/
theorem ineligible_budget {baseA baseB epsilon ell dose0 : ℝ}
    (failed : dose0 / 2 ≤ (baseA + epsilon) + (baseB + 2 * epsilon) +
      20 / 17 * ell + 1 / 8000) :
    ¬ ((baseA + epsilon) + (baseB + 2 * epsilon) +
      20 / 17 * ell + 1 / 8000 < dose0 / 2) := not_lt_of_ge failed

theorem campaign_oracle_accurate {p q : Nat}
    (preparation : CampaignEntry p) (practice : CampaignEntry q)
    (preparationPhysical : CampaignTransferPremises preparation)
    (practicePhysical : CampaignTransferPremises practice) :
    LessonAccurate ⟨p, q⟩
      (marginOracle (decodedCount preparation.readings) (decodedCount practice.readings)) 0 :=
  accuracy_from_envelopes (preparation.certificate preparationPhysical)
    (practice.certificate practicePhysical)

/-- Any two eligible campaign entries can feed the same two-block controller
under their own physical transfer premises. Feasibility tolerance is derived
as zero; cost non-degradation concerns its exact commanded-pulse ledger. -/
theorem campaign_controller_contract {P : Type} {p q : Nat}
    (preparation : CampaignEntry p) (practice : CampaignEntry q)
    (preparationPhysical : CampaignTransferPremises preparation)
    (practicePhysical : CampaignTransferPremises practice)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat)
    (menu : PolicyMenu P) (passes : (lesson.train ⟨p, q⟩).retained = true) :
    let fixed := certifiedEnvironment
      (preparation.certificate preparationPhysical).toProbeCertificate
      (practice.certificate practicePhysical).toProbeCertificate
      lesson policies overhead deployments validationOverhead
    Ready ⟨p, q⟩ (adaptAndSearch fixed menu).memory.live ∧
      referenceCost p q lesson policies overhead deployments
        (adaptAndSearch fixed menu).memory.incumbent ≤
          referenceCost p q lesson policies overhead deployments menu.seed :=
  envelope_controller_nondegradation (preparation.certificate preparationPhysical)
    (practice.certificate practicePhysical) lesson policies overhead deployments validationOverhead menu passes

end ReusableController.PhysicalEvaluator
