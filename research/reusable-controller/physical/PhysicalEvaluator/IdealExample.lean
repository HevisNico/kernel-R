import PhysicalEvaluator.Counts

/-! An inhabited certificate in the ideal scalar model. The gain ladder,
charge, threshold and finite Boolean observations are explicit. Their scalar
correspondence is proved, not supplied as a premise. This example does not
claim that a circuit, a measured CSV, or a physical reset realizes the ladder. -/
namespace ReusableController.PhysicalEvaluator.IdealExample
open RecursiveLearning RecursiveLearning.Native KernelR.Hybrid
open ReusableController.Adaptive

noncomputable def idealGain (m : ℕ) (k : Fin (m + 1)) : ℝ :=
  needCentre 1 (1 / 20) m + (k.val : ℝ) * (1 / 20)

/-- A concrete finite Boolean sequence; it does not decide PulseFires. -/
def idealObserved (m : ℕ) (k : Fin (m + 1)) : Bool := decide (k.val = m)

theorem ideal_need (m : ℕ) : NeedIs 1 (1 / 20) (needCentre 1 (1 / 20) m) m := by
  apply needIs_of_tolerance (level₀ := 1) (d₀ := 1 / 20) (a := 0) (b := 0) (ℓ := 0)
  all_goals norm_num

theorem ideal_scalar_correspondence (m : ℕ) (k : Fin (m + 1)) :
    idealObserved m k = true ↔ PulseFires (1 / 10) (Real.exp (idealGain m k)) 1 := by
  by_cases last : k.val = m
  · have fires : PulseFires (1 / 10) (Real.exp (idealGain m k)) 1 :=
      (ideal_need m).2 k.val (by omega) (1 / 10) (by norm_num) (by norm_num)
    exact ⟨fun _ => fires, fun _ => by simp [idealObserved, last]⟩
  · have before : k.val < m := by omega
    have silent : ¬ PulseFires (1 / 10) (Real.exp (idealGain m k)) 1 :=
      (ideal_need m).1 k.val before (1 / 10) (by norm_num) (by norm_num)
    constructor
    · intro observed
      simp [idealObserved, last] at observed
    · intro fires
      exact False.elim (silent fires)

/-- No hypotheses: zero error and a positive dose leave strict room, and
the independent scalar theorem supplies the observation correspondence. -/
noncomputable def idealCertificate (m : ℕ) : FiniteProbeCertificate m where
  level0 := 1
  dose0 := 1 / 20
  a := 0
  B := 0
  ell := 0
  gain := idealGain m
  level := fun _ => 1
  charge := fun _ => 1 / 10
  observed := idealObserved m
  levelFloor := by norm_num
  gainBound := by simp [idealGain]
  cumulativeBound := by
    intro k
    simp [idealGain]
  levelBound := by intro k; norm_num
  chargeBand := by intro k; norm_num
  room := by norm_num
  scalarCorrespondence := ideal_scalar_correspondence m

theorem two_readings : (idealCertificate 2).readings = [false, false, true] := by
  change List.ofFn (idealObserved 2) = [false, false, true]
  decide

theorem three_readings : (idealCertificate 3).readings = [false, false, false, true] := by
  change List.ofFn (idealObserved 3) = [false, false, false, true]
  decide

theorem two_firstFire : firstFire (idealCertificate 2).readings = some 2 :=
  (idealCertificate 2).firstFire_exact

theorem three_firstFire : firstFire (idealCertificate 3).readings = some 3 :=
  (idealCertificate 3).firstFire_exact

theorem decoded_counts :
    decodedCount (idealCertificate 2).readings = 2 ∧
      decodedCount (idealCertificate 3).readings = 3 :=
  ⟨(idealCertificate 2).count_exact, (idealCertificate 3).count_exact⟩

/-- The concrete scalar certificates yield exact signed-margin evaluation. -/
theorem oracle_accurate : LessonAccurate ⟨2, 3⟩
    (marginOracle (decodedCount (idealCertificate 2).readings)
      (decodedCount (idealCertificate 3).readings)) 0 :=
  accuracy_from_certificates (idealCertificate 2) (idealCertificate 3)

end ReusableController.PhysicalEvaluator.IdealExample
