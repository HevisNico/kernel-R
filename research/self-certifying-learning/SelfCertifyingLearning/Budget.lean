import Std

/-! Discrete repair accounting. Potentials, disturbances and costs are natural
ticks in a fixed common scale. They are not circuit energy measurements. -/
namespace SelfCertifyingLearning

inductive Event where
  | correction
  | disturbance (amount : Nat)
  | idle
  deriving DecidableEq, Repr

def corrections : List Event → Nat
  | [] => 0
  | .correction :: rest => 1 + corrections rest
  | _ :: rest => corrections rest

def injected : List Event → Nat
  | [] => 0
  | .disturbance amount :: rest => amount + injected rest
  | _ :: rest => injected rest

/-- Every transition, including idle time, must respect the accounting.
The constructors do not assert that a physical implementation realizes it. -/
inductive Run (eta : Nat) : Nat → List Event → Nat → Prop where
  | nil (v) : Run eta v [] v
  | correction {v next last rest} (decrease : next + eta ≤ v)
      (tail : Run eta next rest last) : Run eta v (.correction :: rest) last
  | disturbance {v next last rest amount} (increase : next ≤ v + amount)
      (tail : Run eta next rest last) : Run eta v (.disturbance amount :: rest) last
  | idle {v next last rest} (nonincrease : next ≤ v)
      (tail : Run eta next rest last) : Run eta v (.idle :: rest) last

/-- Telescoping ledger, retaining the nonnegative terminal potential. -/
theorem Run.balance {eta initial trace final} (run : Run eta initial trace final) :
    final + eta * corrections trace ≤ initial + injected trace := by
  induction run with
  | nil => simp [corrections, injected]
  | correction decrease tail ih =>
      simp only [corrections, injected, Nat.mul_add, Nat.mul_one]
      omega
  | disturbance increase tail ih =>
      simp only [corrections, injected]
      omega
  | idle nonincrease tail ih =>
      simp only [corrections, injected]
      omega

theorem Run.correction_bound {eta initial trace final} (run : Run eta initial trace final) :
    eta * corrections trace ≤ initial + injected trace := by
  have := run.balance
  omega

inductive RepairPath {State : Type} (repair : State → State → Prop) :
    State → Nat → State → Prop where
  | nil (s) : RepairPath repair s 0 s
  | cons {s t u n} (step : repair s t) (tail : RepairPath repair t n u) :
      RepairPath repair s (n + 1) u

/-- Available corrections plus a strictly decreasing natural rank construct a
finite path to validity. This is existence, not a scheduler-fairness theorem. -/
theorem repair_exists {State : Type} (valid : State → Prop) (repair : State → State → Prop)
    (rank : State → Nat)
    (available : ∀ s, ¬ valid s → ∃ t, repair s t ∧ rank t < rank s) :
    ∀ s, ∃ t n, RepairPath repair s n t ∧ valid t ∧ n ≤ rank s := by
  intro s
  have aux : ∀ n, ∀ s, rank s = n →
      ∃ t steps, RepairPath repair s steps t ∧ valid t ∧ steps ≤ rank s := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro s hs
      classical
      by_cases done : valid s
      · exact ⟨s, 0, .nil s, done, Nat.zero_le _⟩
      · obtain ⟨next, step, lower⟩ := available s done
        obtain ⟨last, steps, path, good, bound⟩ := ih (rank next) (by omega) next rfl
        exact ⟨last, steps + 1, .cons step path, good, by omega⟩
  exact aux (rank s) s rfl

/-- At a terminal state, availability excludes an incorrect deadlock. -/
theorem terminal_valid {State : Type} (valid : State → Prop) (repair : State → State → Prop)
    (available : ∀ s, ¬ valid s → ∃ t, repair s t)
    (s : State) (terminal : ¬ ∃ t, repair s t) : valid s := by
  classical
  apply Classical.byContradiction
  intro bad
  exact terminal (available s bad)

end SelfCertifyingLearning
