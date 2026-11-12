import SelfCertifyingLearning.EpochSafety

/-! A kernel-checked calendar-time example, including a fallback selection
and a physical trajectory witness. Full state values here belong to the
reference model; this checker is not a sensor or an observation-only proof. -/
namespace SelfCertifyingLearning.EpochExamples
open Repair ClosedLoop Epochs EpochSafety

/-- Finite checker for the existing transition laws, not for safety itself. -/
def checkDynamics (c : Config) (state : Nat → Int) (action : Action) : Bool :=
  (List.range (duration c action)).all (fun k => decide (state k - (c.bound : Int) ≤ state (k + 1))) &&
    decide (action = .write →
      min (c.capacity : Int) (state 0 - (c.loss : Int) + (c.dose : Int)) ≤ state c.latency)

theorem checkDynamics_sound {c state action} (checked : checkDynamics c state action = true) :
    Dynamics c state action := by
  simp only [checkDynamics, Bool.and_eq_true, decide_eq_true_eq] at checked
  refine ⟨?_, checked.2⟩
  intro k hk
  have item := List.all_eq_true.mp checked.1 k (List.mem_range.mpr hk)
  simpa using item

def checkExecution (c : Config) : Nat → Nat → (Nat → Int) → Bool
  | 0, _, _ => true
  | n + 1, lower, state =>
    let action := choose c lower
    checkDynamics c state action &&
      checkExecution c n (next c lower action) (fun t => state (duration c action + t))

theorem checkExecution_sound {c n lower state} (checked : checkExecution c n lower state = true) :
    ClosedLoop.Realizes c n lower state := by
  induction n generalizing lower state with
  | zero => trivial
  | succ n ih =>
    simp only [checkExecution, Bool.and_eq_true] at checked
    exact ⟨checkDynamics_sound checked.1, ih checked.2⟩

def checkPlan (state : Nat → Int) : Plan → Bool
  | .complete _ | .blocked _ => true
  | .phase cursor offer tail =>
    checkExecution offer.config offer.decisions (entry cursor offer) (fun t => state (cursor.now + t)) &&
      checkPlan state tail

theorem checkPlan_sound {state plan} (checked : checkPlan state plan = true) :
    EpochSafety.Realizes state plan := by
  induction plan with
  | complete => trivial
  | blocked => trivial
  | phase cursor offer tail ih =>
    simp only [checkPlan, Bool.and_eq_true] at checked
    exact ⟨checkExecution_sound checked.1, ih checked.2⟩

def policy : Policy := ⟨10, 19⟩
def initial : Cursor := ⟨0, 20, 0, 2⟩
def nominal : Offer := ⟨⟨10, 2, 3, 10, 30, 4⟩, 2, 0, 5⟩
def prudent : Offer := ⟨⟨10, 3, 3, 10, 30, 4⟩, 2, 5, 11⟩
def expired : Offer := { nominal with issued := 0, expires := 4 }
def requests : List (List Offer) := [[nominal], [expired, prudent]]
def examplePlan : Plan := run policy initial requests

def world (time : Nat) : Int :=
  [20, 18, 16, 14, 12, 20, 17, 14, 21, 18, 15, 22].getD time 22

theorem fallback_selected : select policy (advance initial nominal) [expired, prudent] = some prudent := by decide

theorem phase_summary : examplePlan.phases = 2 ∧ examplePlan.finish.now = 11 ∧
    examplePlan.finish.lower = 22 ∧ examplePlan.finish.credit = 0 ∧
    examplePlan.switchCost = 2 ∧ examplePlan.writes = 3 := by decide

theorem reference_realizes : EpochSafety.Realizes world examplePlan :=
  checkPlan_sound (by decide)

theorem reference_safe : SafeBetween world 10 0 11 ∧ (22 : Int) ≤ world 11 :=
  composed_safe (run_wellFormed policy initial requests) world (by decide) (by decide) reference_realizes

theorem reference_cost : examplePlan.writes ≤ initial.debt + initial.credit + examplePlan.leakBudget :=
  global_write_bound (run_wellFormed policy initial requests)

/-- Same configuration and new dates: no additional switching charge. -/
theorem renewal_has_no_new_charge : charge (advance initial nominal)
    { nominal with issued := 5, expires := 10 } = 0 := by decide

/-- Calendar admission covers completion, not just the dispatch instant. -/
theorem short_lease_refused : eligible policy (advance initial nominal)
    { prudent with expires := 10 } = false := by decide

theorem unfunded_switch_refused : eligible policy
    { advance initial nominal with credit := 1 } prudent = false := by decide

/-- A phase that spends the next phase's buffer must not be dispatched. -/
theorem handoff_loss_refused : eligible policy initial { nominal with decisions := 1 } = false := by decide

theorem no_contract_blocks : run policy (advance initial nominal) [[expired]] =
    .blocked (advance initial nominal) := by rfl

end SelfCertifyingLearning.EpochExamples
