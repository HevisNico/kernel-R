import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! Finite control properties. The supplied observation categories and decoder
are modeled explicitly; no theorem here claims that a learning process discovers them. -/
namespace KernelR.Adaptive

inductive Context where
  | missing | late | notLate
  deriving DecidableEq, Repr

/-- Number of blocks consumed before the first `notLate`, or list exhaustion. -/
def stopAfter : List Context → ℕ
  | [] => 0
  | .notLate :: _ => 1
  | _ :: xs => 1 + stopAfter xs

theorem stopAfter_le_length (xs : List Context) : stopAfter xs ≤ xs.length := by
  induction xs with
  | nil => simp [stopAfter]
  | cons x xs ih => cases x <;> simp_all [stopAfter] <;> omega

theorem stopAfter_pos {xs : List Context} (h : xs ≠ []) : 0 < stopAfter xs := by
  cases xs with
  | nil => contradiction
  | cons x xs => cases x <;> simp [stopAfter]

/-- Once a stopping observation is available, any future observations are irrelevant. -/
theorem future_observations_irrelevant (initial suffix : List Context)
    (h : Context.notLate ∈ initial) :
    stopAfter (initial ++ suffix) = stopAfter initial := by
  induction initial with
  | nil => simp at h
  | cons x xs ih =>
    cases x with
    | missing => simp only [List.mem_cons, reduceCtorEq, false_or] at h
                 simp [stopAfter, ih h]
    | late => simp only [List.mem_cons, reduceCtorEq, false_or] at h
              simp [stopAfter, ih h]
    | notLate => simp [stopAfter]

theorem all_missing_uses_budget (n : ℕ) : stopAfter (List.replicate n .missing) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, stopAfter, ih, Nat.add_comm]

theorem all_late_uses_budget (n : ℕ) : stopAfter (List.replicate n .late) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, stopAfter, ih, Nat.add_comm]

def studentPulses (blocks : ℕ) : ℕ := 3 * blocks
def teacherQueryPulses (blocks : ℕ) : ℕ := 2 * blocks

theorem pulse_budget {xs : List Context} (h : xs.length ≤ 4) : studentPulses (stopAfter xs) ≤ 12 := by
  have hstop := stopAfter_le_length xs
  dsimp [studentPulses]; omega

theorem queries_must_be_counted (blocks : ℕ) :
    studentPulses blocks + teacherQueryPulses blocks = 5 * blocks := by
  simp [studentPulses,teacherQueryPulses]; omega

/-- Grades are read after selection; changing them cannot change the stopping time. -/
def episode (observations : List Context) (grades : List Bool) : ℕ × Bool :=
  let blocks := stopAfter observations
  (blocks, grades[blocks - 1]?.getD false)

theorem no_final_grade_leakage (observations : List Context) (grades₁ grades₂ : List Bool) :
    (episode observations grades₁).1 = (episode observations grades₂).1 := rfl

end KernelR.Adaptive
