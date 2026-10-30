import KernelR.Doses
import KernelR.Calendar

/-! A discrete abstraction of already justified complete input cycles.
This file proves the exact consequences of the cycle words in THEOREM.md.
It does NOT assert that an arbitrary hybrid execution produces those words. -/
namespace KernelR

inductive Cycle where
  | silentError
  | protectedMark
  | fire
  deriving DecidableEq, Repr

def errorCount : List Cycle → ℕ
  | [] => 0
  | .silentError :: xs => 1 + errorCount xs
  | _ :: xs => errorCount xs

def markCount : List Cycle → ℕ
  | [] => 0
  | .protectedMark :: xs => 1 + markCount xs
  | _ :: xs => markCount xs

def fireCount : List Cycle → ℕ
  | [] => 0
  | .fire :: xs => 1 + fireCount xs
  | _ :: xs => fireCount xs

theorem count_partition (xs : List Cycle) :
    errorCount xs + markCount xs + fireCount xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp_all [errorCount,markCount,fireCount] <;> omega

theorem fireCount_append (xs ys : List Cycle) : fireCount (xs ++ ys) = fireCount xs + fireCount ys := by
  induction xs with
  | nil => simp [fireCount]
  | cons x xs ih => cases x <;> simp_all [fireCount] <;> omega

def feedbackWord (inputs : ℕ) : List Cycle :=
  List.replicate (min 3 inputs) .silentError ++ List.replicate (inputs - 3) .fire

def aWarmup : List Cycle := [.silentError,.silentError,.silentError,.fire,.protectedMark] ++ List.replicate 11 .fire
def aTeaching : List Cycle := List.replicate 16 .fire
def bWarmup : List Cycle := [.silentError,.fire,.protectedMark] ++ List.replicate 13 .fire

theorem local_B_counts : (feedbackWord 16).length = 16 ∧ errorCount (feedbackWord 16) = 3 ∧
    markCount (feedbackWord 16) = 0 ∧ fireCount (feedbackWord 16) = 13 := by decide

theorem local_A_counts : (feedbackWord 13).length = 13 ∧ errorCount (feedbackWord 13) = 3 ∧
    markCount (feedbackWord 13) = 0 ∧ fireCount (feedbackWord 13) = 10 := by decide

theorem A_warmup_counts : aWarmup.length = 16 ∧ errorCount aWarmup = 3 ∧
    markCount aWarmup = 1 ∧ fireCount aWarmup = 12 := by decide

theorem B_warmup_counts : bWarmup.length = 16 ∧ errorCount bWarmup = 1 ∧
    markCount bWarmup = 1 ∧ fireCount bWarmup = 14 := by decide

theorem composed_emissions : fireCount (aWarmup ++ aTeaching ++ feedbackWord 13) = 38 ∧
    fireCount (bWarmup ++ feedbackWord 16) = 27 := by decide

noncomputable def logGainAfter (z : ℝ) (xs : List Cycle) : ℝ := z + (errorCount xs : ℝ) * errorDose
noncomputable def recoveryAfter (b : ℝ) (xs : List Cycle) : ℝ := b + (markCount xs : ℝ) * markDose

theorem feedback_gain_identity (z : ℝ) :
    Real.exp (logGainAfter z (feedbackWord 13)) = Real.exp z * Real.exp (9 / 5) := by
  have hc : errorCount (feedbackWord 13) = 3 := local_A_counts.2.1
  simp only [logGainAfter, hc, errorDose_exact]
  norm_num
  exact Real.exp_add _ _

theorem feedback_recovery_unchanged (b : ℝ) : recoveryAfter b (feedbackWord 13) = b := by
  have hc : markCount (feedbackWord 13) = 0 := local_A_counts.2.2.1
  simp [recoveryAfter,hc]

theorem A_recovery_entry {b : ℝ} (hb : (7999 / 100000 : ℝ) ≤ b ∧ b ≤ 8001 / 100000) :
    (17999 / 100000 : ℝ) ≤ recoveryAfter b aWarmup ∧ recoveryAfter b aWarmup ≤ 18001 / 100000 := by
  have hc : markCount aWarmup = 1 := A_warmup_counts.2.2.1
  simpa [recoveryAfter,hc] using recovery_entry hb

/-- The transition-system composition rule. Each phase must have a separate soundness proof. -/
theorem compose_reachability {State : Type*} {R₁ R₂ : State → State → Prop}
    {Birth Section Goal : State → Prop}
    (hentry : ∀ s t, Birth s → R₁ s t → Section t)
    (hfeedback : ∀ s t, Section s → R₂ s t → Goal t)
    {s u t : State} (hs : Birth s) (h₁ : R₁ s u) (h₂ : R₂ u t) : Goal t :=
  hfeedback u t (hentry s u hs h₁) h₂

end KernelR
