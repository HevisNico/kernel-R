import PhysicalEvaluator.Counts
import PhysicalEvaluator.Envelope
import ReusableController.AdaptiveSystem

/-! A controller whose feasibility tolerance follows from finite scalar
readout certificates. Costs here count commanded lesson pulses plus declared
overheads; this does not turn the need certificate into an energy meter. -/
namespace ReusableController.PhysicalEvaluator
open RecursiveLearning ReusableController.Adaptive

/-- Missing FIRE observations do not silently become a valid evaluator.
This decoder alone does not certify its inputs; certificates establish the
meaning of the returned counts. -/
def readoutCounts (preparation practice : List Bool) : Option (Nat × Nat) := do
  let p ← firstFire preparation
  let q ← firstFire practice
  pure (p, q)

theorem certified_readout_present {p q : Nat}
    (cp : FiniteProbeCertificate p) (cq : FiniteProbeCertificate q) :
    readoutCounts cp.readings cq.readings = some (p, q) := by
  simp [readoutCounts, cp.firstFire_exact, cq.firstFire_exact]

theorem missing_preparation_refused (practice : List Bool) :
    readoutCounts [] practice = none := rfl

theorem missing_practice_refused (preparation : List Bool) :
    readoutCounts preparation [] = none := by
  simp only [readoutCounts, firstFire]
  cases firstFire preparation <;> rfl

theorem no_fire_refused (n : Nat) (practice : List Bool) :
    readoutCounts (List.replicate n false) practice = none := by
  have absent : firstFire (List.replicate n false) = none := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, firstFire, ih]
  simp [readoutCounts, absent]

def certificateOracle {p q : Nat} (cp : FiniteProbeCertificate p)
    (cq : FiniteProbeCertificate q) : LessonOracle :=
  marginOracle (decodedCount cp.readings) (decodedCount cq.readings)

/-- The reference objective uses the true needs, not unverified reports.
It is pulse accounting in the fixed two-block model, not joules or duration. -/
def referenceCost {P : Type} (p q : Nat) (lesson : Lesson)
    (policies : P → Policy) (overhead deployments : Nat) (choice : P) : Nat :=
  policyCost (marginOracle p q) 0 (initial lesson) overhead deployments (policies choice)

def certifiedEnvironment {P : Type} {p q : Nat}
    (cp : FiniteProbeCertificate p) (cq : FiniteProbeCertificate q)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat) :
    Evaluation P where
  need := ⟨p, q⟩
  initialLesson := lesson
  oracle := certificateOracle cp cq
  lessonTolerance := 0
  policies := policies
  report := fun choice =>
    (policyCost (certificateOracle cp cq) 0 (initial lesson)
      overhead deployments (policies choice) : Int)
  costTolerance := 0
  overhead := overhead
  deployments := deployments
  validationOverhead := validationOverhead

/-- Feasibility precision is derived from the analog tolerance theorem.
Cost precision is zero because this particular evaluator computes its pulse
ledger exactly, not because gain tolerances bound an arbitrary cost sensor. -/
theorem certified_environment_sound {P : Type} {p q : Nat}
    (cp : FiniteProbeCertificate p) (cq : FiniteProbeCertificate q)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat)
    (passes : (lesson.train ⟨p, q⟩).retained = true) :
    (certifiedEnvironment cp cq lesson policies overhead deployments validationOverhead).Sound := by
  refine ⟨passes, accuracy_from_certificates cp cq, ?_⟩
  intro choice
  simp [certifiedEnvironment, Evaluation.trueCost]

theorem certified_cost_eq_reference {P : Type} {p q : Nat}
    (cp : FiniteProbeCertificate p) (cq : FiniteProbeCertificate q)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat)
    (choice : P) :
    (certifiedEnvironment cp cq lesson policies overhead deployments validationOverhead).trueCost choice =
      referenceCost p q lesson policies overhead deployments choice := by
  simp [Evaluation.trueCost, certifiedEnvironment, certificateOracle,
    cp.count_exact, cq.count_exact, referenceCost]

/-- No `LessonAccurate` or `CostAccurate` hypothesis is supplied here. The
physical readout premises remain visible in the two finite certificates. -/
theorem certified_controller_nondegradation {P : Type} {p q : Nat}
    (cp : FiniteProbeCertificate p) (cq : FiniteProbeCertificate q)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat)
    (menu : PolicyMenu P) (passes : (lesson.train ⟨p, q⟩).retained = true) :
    let fixed := certifiedEnvironment cp cq lesson policies overhead deployments validationOverhead
    Ready ⟨p, q⟩ (adaptAndSearch fixed menu).memory.live ∧
      referenceCost p q lesson policies overhead deployments (adaptAndSearch fixed menu).memory.incumbent ≤
        referenceCost p q lesson policies overhead deployments menu.seed := by
  dsimp only
  have result := adapt_and_search_contract
    (certifiedEnvironment cp cq lesson policies overhead deployments validationOverhead) menu
    (certified_environment_sound cp cq lesson policies overhead deployments validationOverhead passes)
  refine ⟨result.1, ?_⟩
  simpa only [certified_cost_eq_reference] using result.2.2.2.2

/-- Readout/calibration acquisition is an additional cost, not a free part
of selection. The bound keeps an explicit caller-supplied acquisition ledger. -/
theorem certified_total_budget {P : Type} {p q : Nat}
    (cp : FiniteProbeCertificate p) (cq : FiniteProbeCertificate q)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat)
    (menu : PolicyMenu P) (passes : (lesson.train ⟨p, q⟩).retained = true)
    (acquisition : Nat) {F : Nat} (fuel : ∀ choice, (policies choice).fuel ≤ F) :
    let fixed := certifiedEnvironment cp cq lesson policies overhead deployments validationOverhead
    acquisition + (adaptAndSearch fixed menu).memory.spent +
      (adaptAndSearch fixed menu).memory.live.work overhead ≤
      acquisition + menu.count * fixed.validationBound F + F * lesson.cost + overhead * F := by
  dsimp only
  have budget := (two_level_budget
    (certifiedEnvironment cp cq lesson policies overhead deployments validationOverhead) menu
    (certified_environment_sound cp cq lesson policies overhead deployments validationOverhead passes)
    fuel).2.2.2
  simpa only [Nat.add_assoc, certifiedEnvironment] using Nat.add_le_add_left budget acquisition

theorem acquisition_break_even {oldCost newCost selection acquisition episodes : Nat}
    (nondegradation : newCost ≤ oldCost)
    (covered : acquisition + selection ≤ episodes * (oldCost - newCost)) :
    acquisition + selection + episodes * newCost ≤ episodes * oldCost := by
  have split := Nat.mul_sub_left_distrib episodes oldCost newCost
  have ordered := Nat.mul_le_mul_left episodes nondegradation
  omega

/-- The same controller guarantee can start from time-varying observation
envelopes; it does not require a constant physical threshold during a read. -/
theorem envelope_controller_nondegradation {P : Type} {p q : Nat}
    (cp : FiniteEnvelopeCertificate p) (cq : FiniteEnvelopeCertificate q)
    (lesson : Lesson) (policies : P → Policy) (overhead deployments validationOverhead : Nat)
    (menu : PolicyMenu P) (passes : (lesson.train ⟨p, q⟩).retained = true) :
    let fixed := certifiedEnvironment cp.toProbeCertificate cq.toProbeCertificate
      lesson policies overhead deployments validationOverhead
    Ready ⟨p, q⟩ (adaptAndSearch fixed menu).memory.live ∧
      referenceCost p q lesson policies overhead deployments (adaptAndSearch fixed menu).memory.incumbent ≤
        referenceCost p q lesson policies overhead deployments menu.seed :=
  certified_controller_nondegradation cp.toProbeCertificate cq.toProbeCertificate
    lesson policies overhead deployments validationOverhead menu passes

/-- A counterexample to inferring arbitrary energy-report accuracy from a
count certificate. The same certificate is compatible with arbitrarily
different cost sensors; an energy transfer theorem needs additional data. -/
theorem count_certificate_does_not_bound_arbitrary_cost {m : Nat}
    (_certificate : FiniteProbeCertificate m) (tau : Nat) :
    ∃ (actual reported : Nat), ¬ ((actual : Int) - tau ≤ reported ∧
      (reported : Int) ≤ (actual : Int) + tau) := by
  refine ⟨tau + 1, 0, ?_⟩
  omega

end ReusableController.PhysicalEvaluator
