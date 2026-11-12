import SelfCertifyingLearning.Composition

/-! A realized discrete coupling, not a circuit or an adaptive controller.
Either level may act when it owes at least three ticks. Its correction
removes three local ticks and creates one in the other level. -/
namespace SelfCertifyingLearning.TwoLevel

abbrev State := Nat × Nat
def rank (s : State) : Nat := s.1 + s.2
def Valid (s : State) : Prop := s.1 < 3 ∧ s.2 < 3

inductive Step : State → State → Prop where
  | left (x y) : Step (x + 3, y) (x, y + 1)
  | right (x y) : Step (x, y + 3) (x + 1, y)

theorem step_balance {s t} (step : Step s t) : rank t + 2 = rank s := by
  cases step <;> simp [rank, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem available (s : State) (bad : ¬ Valid s) : ∃ t, Step s t ∧ rank t < rank s := by
  obtain ⟨x, y⟩ := s
  by_cases leftReady : 3 ≤ x
  · have h : x = (x - 3) + 3 := by omega
    have step : Step (x, y) (x - 3, y + 1) := h ▸ Step.left (x - 3) y
    exact ⟨_, step, by have := step_balance step; omega⟩
  · have rightReady : 3 ≤ y := by simp [Valid] at bad; omega
    have h : y = (y - 3) + 3 := by omega
    have step : Step (x, y) (x + 1, y - 3) := h ▸ Step.right x (y - 3)
    exact ⟨_, step, by have := step_balance step; omega⟩

theorem valid_iff_terminal (s : State) : Valid s ↔ ¬ ∃ t, Step s t := by
  constructor
  · intro good ⟨t, step⟩
    cases step <;> simp only [Valid] at good <;> omega
  · intro terminal
    exact terminal_valid Valid Step (fun s bad => let ⟨t, step, _⟩ := available s bad
      ⟨t, step⟩) s terminal

/-- Every finite ordering of enabled corrections has the same accounting. -/
theorem path_balance {s t n} (path : RepairPath Step s n t) :
    rank t + 2 * n = rank s := by
  induction path with
  | nil => simp
  | cons step tail ih =>
    have := step_balance step
    simp only [Nat.mul_add, Nat.mul_one]
    omega

/-- A valid endpoint exists, and the number of corrections is bounded.
This does not schedule the corrections or prove a real-time deadline. -/
theorem stabilizes (s : State) :
    ∃ t n, RepairPath Step s n t ∧ Valid t ∧ 2 * n ≤ rank s := by
  obtain ⟨t, n, path, good, _⟩ := repair_exists Valid Step rank available s
  exact ⟨t, n, path, good, by have := path_balance path; omega⟩

/-- Concrete path using both levels, rather than an assumed scalar trace. -/
theorem example_path : RepairPath Step (3, 3) 2 (1, 1) :=
  .cons (.left 0 3) (.cons (.right 0 1) (.nil (1, 1)))

end SelfCertifyingLearning.TwoLevel
