import Std

/-! Phase 0 control for the proposed discrete write semantics.
Two cells retire one unit of work and send one unit to the other on every
write. Each write increases its cell's stored value by one. -/

namespace NetworkStability.Control

structure State where
  leftWork : Nat
  rightWork : Nat
  leftWrites : Nat
  rightWrites : Nat

def start : State := ⟨1, 0, 0, 0⟩

inductive Write : State → State → Prop where
  | left (r a b k : Nat) :
      Write ⟨k + 1, r, a, b⟩ ⟨k, r + 1, a + 1, b⟩
  | right (l a b k : Nat) :
      Write ⟨l, k + 1, a, b⟩ ⟨l + 1, k, a, b + 1⟩

def Terminal (s : State) : Prop := ∀ t, ¬ Write s t

inductive Reach : Nat → State → Prop where
  | start : Reach 0 start
  | next {n s t} : Reach n s → Write s t → Reach (n + 1) t

theorem no_positive_margin (wLeft wRight eta : Nat) (pos : 0 < eta) :
    ¬ (eta + wRight ≤ wLeft ∧ eta + wLeft ≤ wRight) := by
  omega

theorem reachable_ledger {n s} (r : Reach n s) :
    s.leftWork + s.rightWork = 1 ∧ s.leftWrites + s.rightWrites = n := by
  induction r with
  | start => decide
  | next _ step ih =>
    cases step <;> simp_all <;> omega

theorem enabled_of_work {s : State} (work : s.leftWork + s.rightWork = 1) :
    ∃ t, Write s t := by
  obtain ⟨l, r, a, b⟩ := s
  cases l with
  | zero =>
    cases r with
    | zero => simp at work
    | succ k => exact ⟨_, Write.right 0 a b k⟩
  | succ k => exact ⟨_, Write.left r a b k⟩

theorem no_reachable_terminal {n s} (r : Reach n s) : ¬ Terminal s := by
  obtain ⟨t, step⟩ := enabled_of_work (reachable_ledger r).1
  exact fun terminal => terminal t step

theorem writes_at_every_length (n : Nat) : ∃ s, Reach n s := by
  induction n with
  | zero => exact ⟨start, Reach.start⟩
  | succ n ih =>
    obtain ⟨s, r⟩ := ih
    obtain ⟨t, step⟩ := enabled_of_work (reachable_ledger r).1
    exact ⟨t, r.next step⟩

theorem exceeds_any_ceiling (ceiling : Nat) :
    ∃ n s, Reach n s ∧ (ceiling < s.leftWrites ∨ ceiling < s.rightWrites) := by
  let n := 2 * ceiling + 1
  obtain ⟨s, r⟩ := writes_at_every_length n
  have total := (reachable_ledger r).2
  refine ⟨n, s, r, ?_⟩
  dsimp [n] at total
  omega

#print axioms no_positive_margin
#print axioms reachable_ledger
#print axioms enabled_of_work
#print axioms no_reachable_terminal
#print axioms writes_at_every_length
#print axioms exceeds_any_ceiling

end NetworkStability.Control
