import ScheduleConfluence
import PerpetualExamples

namespace NetworkStability.AutonomousFeedback.Schedule

private def orderMatters : Model 2 (Fin 2) where
  cell := id
  bias := fun _ => 1
  drive := fun _ => 0
  route := fun p => [p]

/-- Independent FIREs can retain opposite list orders. -/
theorem exact_queue_order_can_differ :
    let s : Config 2 (Fin 2) := ⟨[0, 1], fun _ => 0⟩
    let a := process orderMatters 1 (process orderMatters 1 s 0 [1]) 1 [0]
    let b := process orderMatters 1 (process orderMatters 1 s 1 [0]) 0 [1]
    a.pending ≠ b.pending ∧ Equivalent a b := by
  exact ⟨by decide, different_cells_commute orderMatters 1 _ 0 1 [] (by decide)⟩

theorem counterexample_violates_A :
    ¬ Exclusive ScheduleCounterexample.model (project ScheduleCounterexample.ready) := by unfold Exclusive; decide

theorem counterexample_violates_B :
    ¬ PairMargins ScheduleCounterexample.model 2 (project ScheduleCounterexample.ready) := by
  intro h
  have room := h .warm (by decide) .read (by decide) (by decide) (by decide)
  have bad : ¬ InterleavingRoom
      (cleanScore ScheduleCounterexample.model 2 (project ScheduleCounterexample.ready) .warm)
      0 0 2 1 := by
    unfold InterleavingRoom
    decide
  exact bad room

theorem uniform_ring_exclusive (n : Nat) (bits : Fin (n + 1) → Bool)
    (s : Config (n + 1) Nat) (run : Path (Ring.model n bits) 1 ⟨[0], fun _ => 0⟩ s) :
    Exclusive (Ring.model n bits) s := by
  refine singleton_exclusive (Ring.model n bits) 1 ?_ run (by simp)
  intro p
  unfold Ring.model
  dsimp only
  split <;> simp

theorem uniform_ring_order_independent (n : Nat) (bits : Fin (n + 1) → Bool)
    {a b : Config (n + 1) Nat}
    (pa : Path (Ring.model n bits) 1 ⟨[0], fun _ => 0⟩ a)
    (pb : Path (Ring.model n bits) 1 ⟨[0], fun _ => 0⟩ b)
    (ha : a.pending = []) (hb : b.pending = []) :
    a.writes = b.writes := by
  exact (terminal_memory_unique 2 2 1 1 (Ring.model n bits) [0] (Ring.certificate n bits)
    (fun s path => Or.inl (uniform_ring_exclusive n bits s path)) pa pb ha hb (fun _ => 1)).1

/-- Even without a terminating rank, the one-token phase of the perpetual
ring has no choice of next probe. -/
theorem recirculating_ring_exclusive (n : Nat) (p : Fin (n + 1))
    (s t : Config (n + 1) (Option (Fin (n + 1))))
    (queue : s.pending = [some p]) (path : Path (RecirculatingRing.model n) 1 s t) :
    Exclusive (RecirculatingRing.model n) t := by
  refine singleton_exclusive (RecirculatingRing.model n) 1 ?_ path ?_
  · intro tok
    cases tok <;> simp [RecirculatingRing.model]
  · simp [queue]

end NetworkStability.AutonomousFeedback.Schedule
