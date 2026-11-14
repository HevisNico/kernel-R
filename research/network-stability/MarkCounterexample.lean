import MarkFeedback

namespace NetworkStability.MarkFeedback.Control

open AutonomousFeedback (mass)
open AutonomousFeedback.Schedule (Config)

inductive Probe
  | mark
  | test
  | returnPulse
  deriving DecidableEq

/-- The MARK emits a follow-up on its own cell. The other port starts just
below threshold and can see the new recovery count. -/
def fixture (coupling : Int) : Model 1 Probe where
  cell := fun _ => 0
  secondPort := fun p => p == .test
  bias := fun p => if p == .test then -1 else 0
  recoveryWeight := fun p => if p == .test then coupling else 0
  learn := fun _ => true
  mark := fun p fire => (p == .mark) && fire
  route := fun p => if p == .mark then [.returnPulse] else []

def seed : List Probe := [.mark, .test]

def markFirst (coupling : Int) : Config 3 Probe := fifo (fixture coupling) 1 (fun _ => 0) (initial 1 seed) 3

def testFirst (coupling : Int) : Config 3 Probe :=
  let M := fixture coupling
  let s := process M 1 (initial 1 seed) .test [.mark] 0
  fifo M 1 (fun _ => 0) s 2

theorem first_ports_exclusive :
    ((initial 1 seed).pending.map (gain (fixture 1))).Nodup := by decide

theorem mark_changes_other_port_read :
    read (fixture 1) 1 (initial 1 seed) .test 0 = false ∧
    read (fixture 1) 1 (process (fixture 1) 1 (initial 1 seed) .mark [.test] 0) .test 0 = true := by
  decide

theorem fixture_rank : Nonempty (Rank 3 1 (fixture 1) seed) := by
  refine ⟨⟨fun p => if p == .mark then 2 else 1, by decide, ?_, by decide⟩⟩
  intro p
  cases p <;> decide

theorem fixture_reserve : Nonempty (Reserve 3 (fixture 1) seed) := by
  refine ⟨⟨fun p => fun q => if q == .mark then 2 else 1, ?_, ?_⟩⟩
  · intro p fire i
    have possible : i = 0 ∨ i = 1 ∨ i = 2 := by
      have lower := i.isLt
      have values : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
      rcases values with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases possible with rfl | rfl | rfl <;> cases p <;> cases fire <;> decide
  · intro i
    decide

theorem distinct_terminal_memories :
    Path (fixture 1) 1 (initial 1 seed) (markFirst 1) ∧
    Path (fixture 1) 1 (initial 1 seed) (testFirst 1) ∧
    (markFirst 1).pending = [] ∧ (testFirst 1).pending = [] ∧
    (markFirst 1).writes (gain (fixture 1) .test) = 0 ∧
    (testFirst 1).writes (gain (fixture 1) .test) = 1 := by
  refine ⟨fifo_prefix _ _ _ _, .cons (.select _ _ _ (List.Perm.swap _ _ _)) (fifo_prefix _ _ _ _),
    by decide, by decide, by decide, by decide⟩

theorem zero_error_margins_on_both_orders :
    ∀ s : Config 3 Probe, ∀ p : Probe, RoutedCalendar.HasRoom (score (fixture 1) 1 s p) 0 0 := by
  intro s p
  unfold RoutedCalendar.HasRoom
  omega

theorem fifo_misses_reachable_write :
    ∃ t, Path (fixture 1) 1 (initial 1 seed) t ∧
      ∀ n, (fifo (fixture 1) 1 (fun _ => 0) (initial 1 seed) n).writes
        (gain (fixture 1) .test) < t.writes (gain (fixture 1) .test) := by
  refine ⟨testFirst 1, distinct_terminal_memories.2.1, fun n => ?_⟩
  rw [distinct_terminal_memories.2.2.2.2.2]
  by_cases small : n < 3
  · have casesN : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases casesN with rfl | rfl | rfl <;> decide
  · have empty (k : Nat) :
        fifo (fixture 1) 1 (fun _ => 0) (markFirst 1) k = markFirst 1 := by
      induction k with
      | zero => rfl
      | succ k ih => simp only [fifo, ih, fifoStep, distinct_terminal_memories.2.2.1]
    have split : n = 3 + (n - 3) := by omega
    rw [split, fifo_zero_add]
    change (fifo (fixture 1) 1 (fun _ => 0) (markFirst 1) (n - 3)).writes _ < _
    rw [empty, distinct_terminal_memories.2.2.2.2.1]
    decide

end NetworkStability.MarkFeedback.Control
