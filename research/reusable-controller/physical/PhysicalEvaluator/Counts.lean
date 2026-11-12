import Search.VariableNeedTolerance
import ReusableController.NoisySearch
import Mathlib.Data.List.OfFn

/-! A finite scalar-observation certificate derives an exact first-FIRE
count. Post-FIRE physical gains are neither measured nor assumed monotone:
the infinite sequence used inside the tolerance lemma is a constant
extension of the last certified finite sample. The scalar observation link
is an explicit premise, not a transistor correspondence theorem. -/
namespace ReusableController.PhysicalEvaluator
open RecursiveLearning RecursiveLearning.Native KernelR.Hybrid
open ReusableController.Adaptive

/-- All measurements and tolerances stop at sample `m`. Every read may have
its own threshold and resting charge. No exact count or oracle-accuracy
field is supplied. -/
structure FiniteProbeCertificate (m : ℕ) where
  level0 : ℝ
  dose0 : ℝ
  a : ℝ
  B : ℝ
  ell : ℝ
  gain : Fin (m + 1) → ℝ
  level : Fin (m + 1) → ℝ
  charge : Fin (m + 1) → ℝ
  observed : Fin (m + 1) → Bool
  levelFloor : 19 / 20 ≤ level0 - ell
  gainBound : |gain 0 - needCentre level0 dose0 m| ≤ a
  cumulativeBound : ∀ k, |gain k - gain 0 - (k.val : ℝ) * dose0| ≤ B
  levelBound : ∀ k, |level k - level0| ≤ ell
  chargeBand : ∀ k, 1 / 10 ≤ charge k ∧ charge k ≤ 1 / 10 + 1 / 10000
  room : a + B + 20 / 17 * ell + 1 / 8000 < dose0 / 2
  scalarCorrespondence : ∀ k, observed k = true ↔
    PulseFires (charge k) (Real.exp (gain k)) (level k)

private noncomputable def FiniteProbeCertificate.clampedGain {m}
    (certificate : FiniteProbeCertificate m) (k : ℕ) : ℝ :=
  certificate.gain ⟨min k m, Nat.lt_succ_of_le (Nat.min_le_right k m)⟩

private theorem FiniteProbeCertificate.clampedGain_at {m}
    (certificate : FiniteProbeCertificate m) (k : Fin (m + 1)) :
    certificate.clampedGain k.val = certificate.gain k := by
  have bound : k.val ≤ m := Nat.le_of_lt_succ k.isLt
  simp [clampedGain, Nat.min_eq_left bound]

/-- Each application fixes only this read's threshold. Independent threshold
variation between finite samples is therefore retained by the proof. -/
private theorem FiniteProbeCertificate.clamped_need_for_read {m}
    (certificate : FiniteProbeCertificate m) (k : Fin (m + 1)) :
    NeedAlong (certificate.level k) certificate.clampedGain m := by
  have ellNonnegative : 0 ≤ certificate.ell :=
    (abs_nonneg _).trans (certificate.levelBound 0)
  have level0Floor : 19 / 20 ≤ certificate.level0 := by
    linarith [certificate.levelFloor]
  have readFloor : 19 / 20 ≤ certificate.level k := by
    have lower := (abs_le.mp (certificate.levelBound k)).1
    linarith [certificate.levelFloor]
  apply needAlong_of_cumulative_tolerance (a := certificate.a) (B := certificate.B)
    certificate.clampedGain readFloor level0Floor
  · intro n after
    simp [clampedGain, Nat.min_eq_right after]
  · simpa [clampedGain] using certificate.gainBound
  · intro n before
    simpa [clampedGain, Nat.min_eq_left before] using
      certificate.cumulativeBound ⟨n, Nat.lt_succ_of_le before⟩
  · exact certificate.levelBound k
  · exact certificate.room

theorem FiniteProbeCertificate.silent_before {m}
    (certificate : FiniteProbeCertificate m) (k : Fin (m + 1)) (before : k.val < m) :
    certificate.observed k = false := by
  have silent := (certificate.clamped_need_for_read k).1 k.val before (certificate.charge k)
    (certificate.chargeBand k).1 (certificate.chargeBand k).2
  rw [certificate.clampedGain_at k] at silent
  cases observed : certificate.observed k with
  | false => rfl
  | true => exact False.elim (silent ((certificate.scalarCorrespondence k).mp observed))

theorem FiniteProbeCertificate.fires_at {m} (certificate : FiniteProbeCertificate m) :
    certificate.observed (Fin.last m) = true := by
  apply (certificate.scalarCorrespondence (Fin.last m)).mpr
  have fires := (certificate.clamped_need_for_read (Fin.last m)).2 m le_rfl
    (certificate.charge (Fin.last m)) (certificate.chargeBand (Fin.last m)).1
    (certificate.chargeBand (Fin.last m)).2
  have gainAtLast := certificate.clampedGain_at (Fin.last m)
  change certificate.clampedGain m = certificate.gain (Fin.last m) at gainAtLast
  rwa [gainAtLast] at fires

/-- Executable first-FIRE decoder. A trace without any FIRE returns `none`. -/
def firstFire : List Bool → Option ℕ
  | [] => none
  | true :: _ => some 0
  | false :: rest => (firstFire rest).map Nat.succ

/-- A total executable count. Its no-FIRE fallback is the observed length;
the certificate theorem proves that the fallback is never used on certified
traces. No correctness claim is made for uncertified input lists. -/
def decodedCount (observations : List Bool) : ℕ :=
  (firstFire observations).getD observations.length

def FiniteProbeCertificate.readings {m} (certificate : FiniteProbeCertificate m) : List Bool :=
  List.ofFn certificate.observed

theorem FiniteProbeCertificate.readings_shape {m} (certificate : FiniteProbeCertificate m) :
    certificate.readings = List.replicate m false ++ [true] := by
  have priorObservations : (fun k : Fin m => certificate.observed k.castSucc) = fun _ => false := by
    funext k
    exact certificate.silent_before k.castSucc k.isLt
  rw [readings, List.ofFn_succ_last, priorObservations, List.ofFn_const, certificate.fires_at]

theorem firstFire_false_prefix (m : ℕ) :
    firstFire (List.replicate m false ++ [true]) = some m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, firstFire, ih]

theorem FiniteProbeCertificate.firstFire_exact {m} (certificate : FiniteProbeCertificate m) :
    firstFire certificate.readings = some m := by
  rw [certificate.readings_shape, firstFire_false_prefix]

theorem FiniteProbeCertificate.count_exact {m} (certificate : FiniteProbeCertificate m) :
    decodedCount certificate.readings = m := by
  simp [decodedCount, certificate.firstFire_exact]

/-- The oracle computes the signed two-block margin from decoded counts.
The validation index cannot alter the fixed evaluator. -/
def marginOracle (preparationCount practiceCount : ℕ) : LessonOracle :=
  fun _ lesson => min ((lesson.preparation : Int) - (preparationCount : Int))
    ((lesson.practice : Int) - (practiceCount : Int))

/-- Two finite physical-observation certificates derive zero count/margin
error in the stated scalar correspondence. `LessonAccurate` is a conclusion,
not an input or certificate field. -/
theorem accuracy_from_certificates {preparation practice : ℕ}
    (preparationCertificate : FiniteProbeCertificate preparation)
    (practiceCertificate : FiniteProbeCertificate practice) :
    LessonAccurate ⟨preparation, practice⟩
      (marginOracle (decodedCount preparationCertificate.readings)
        (decodedCount practiceCertificate.readings)) 0 := by
  rw [preparationCertificate.count_exact, practiceCertificate.count_exact]
  intro index lesson
  simp [lessonMargin, marginOracle]

end ReusableController.PhysicalEvaluator
