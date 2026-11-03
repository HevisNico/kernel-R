import KernelR.HybridNonZeno
import KernelR.HybridUniversalExecution
import KernelR.HybridPrefixBeforeFlow

/-!
# Structure of bounded-time infinite move presentations

The physical event budget implies that a bounded-time presentation eventually
contains only positive flows. Its late finite prefixes are therefore already
saturated at their own dates. Against one complete reference extending strictly
beyond all those dates, their actual states and per-cell FIRE histories agree
with saturated prefixes of that same reference.

This is an intermediate result toward semantic maximality. It does not define
an extension past an infinite presentation's limit or assert that every raw
infinite move list is time-divergent.
-/
namespace KernelR.Hybrid

private theorem bounded_nat_monotone_stabilizes (f : ℕ → ℕ) (orderPreserving : Monotone f)
    (bound : ℕ) (bounded : ∀ k, f k ≤ bound) :
    ∃ K, ∀ k, K ≤ k → f k = f K := by
  have all : ∀ B : ℕ, (∀ k, f k ≤ B) → ∃ K, ∀ k, K ≤ k → f k = f K := by
    intro B
    induction B with
    | zero =>
      intro upper
      refine ⟨0, fun k _ => ?_⟩
      have first := upper 0
      have later := upper k
      omega
    | succ B ih =>
      intro upper
      by_cases attained : ∃ K, f K = B + 1
      · obtain ⟨K, atBound⟩ := attained
        refine ⟨K, fun k after => ?_⟩
        have lower := orderPreserving after
        have higher := upper k
        omega
      · apply ih
        intro k
        have higher := upper k
        have misses : f k ≠ B + 1 := fun equal => attained ⟨k, equal⟩
        omega
  exact all bound bounded

namespace InfiniteExecution

theorem jumpCount_monotone {n θ route} (run : @InfiniteExecution n θ route) :
    Monotone (fun k => (run.finitePrefix k).jumpCount) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [run.prefix_jumpCount_succ]
  omega

/-- Bounded physical dates force the actual physical-jump counter to stabilize.
The bound is obtained from R's existing physical event theorem.
-/
theorem jumpCount_stabilizes_of_time_bounded {n θ ε route F}
    (run : @InfiniteExecution n θ route)
    (birth : BirthState (run.state 0)) (box : PhysicalBox θ ε)
    (fanout : FanoutBound route F) (H : ℝ)
    (bounded : ∀ k, (run.state k).time ≤ H) :
    ∃ K, ∀ k, K ≤ k → (run.finitePrefix k).jumpCount =
      (run.finitePrefix K).jumpCount := by
  obtain ⟨budget, bounds⟩ := run.event_budget birth box fanout H
  exact bounded_nat_monotone_stabilizes _ run.jumpCount_monotone budget
    (fun k => bounds k (bounded k))

theorem eventually_zero_jumpCount_of_time_bounded {n θ ε route F}
    (run : @InfiniteExecution n θ route)
    (birth : BirthState (run.state 0)) (box : PhysicalBox θ ε)
    (fanout : FanoutBound route F) (H : ℝ)
    (bounded : ∀ k, (run.state k).time ≤ H) :
    ∃ K, ∀ k, K ≤ k → (run.move k).jumpCount = 0 := by
  obtain ⟨K, stable⟩ := run.jumpCount_stabilizes_of_time_bounded birth box fanout H bounded
  refine ⟨K, fun k after => ?_⟩
  have current := stable k after
  have next := stable (k + 1) (by omega)
  have balance := run.prefix_jumpCount_succ k
  omega

/-- The suffix has actual positive flows, not merely zero event counts.
The conclusion follows by inspecting the operational Move constructor.
-/
theorem eventually_flow_of_time_bounded {n θ ε route F}
    (run : @InfiniteExecution n θ route)
    (birth : BirthState (run.state 0)) (box : PhysicalBox θ ε)
    (fanout : FanoutBound route F) (H : ℝ)
    (bounded : ∀ k, (run.state k).time ≤ H) :
    ∃ K, ∀ k, K ≤ k → Nonempty (Flow θ (run.state k) (run.state (k + 1))) := by
  obtain ⟨K, none⟩ := run.eventually_zero_jumpCount_of_time_bounded birth box fanout H bounded
  refine ⟨K, fun k after => ?_⟩
  have zero := none k after
  cases actual : run.move k with
  | flow flow => exact ⟨flow⟩
  | jump jump => simp [actual, Move.jumpCount] at zero

/-- A following positive flow derives saturation at a prefix endpoint.
No completeness premise is imposed on the infinite presentation's prefixes.
-/
theorem eventually_complete_of_time_bounded {n θ ε route F}
    (run : @InfiniteExecution n θ route)
    (birth : BirthState (run.state 0)) (box : PhysicalBox θ ε)
    (fanout : FanoutBound route F) (H : ℝ)
    (bounded : ∀ k, (run.state k).time ≤ H) :
    ∃ K, ∀ k, K ≤ k →
      CompleteThrough (run.finitePrefix k) (run.state k).time := by
  obtain ⟨K, flows⟩ := run.eventually_flow_of_time_bounded birth box fanout H bounded
  refine ⟨K, fun k after => ?_⟩
  obtain ⟨flow⟩ := flows k after
  exact ⟨rfl, fun next => flow.no_initial_jump next, flow.initial_pending_strict⟩

/-- Late states of a bounded-time presentation coincide observationally with
saturated actual prefixes of one reference extending past every state date.
This retains the exact ordered per-cell FIRE histories as well as coordinates.
-/
theorem eventually_reference_sections {n θ ε route F}
    (run : @InfiniteExecution n θ route)
    (birth : BirthState (run.state 0)) (box : PhysicalBox θ ε)
    (fanout : FanoutBound route F) {final H}
    (reference : Execution θ route (run.state 0) final)
    (complete : CompleteThrough reference H)
    (strictlyBefore : ∀ k, (run.state k).time < H) :
    ∃ K, ∀ k, K ≤ k → ∃ cutState, ∃ cut : Execution θ route (run.state 0) cutState,
      reference.IsPrefix cut ∧ CompleteThrough cut (run.state k).time ∧
      (run.state k).ObservationalEq cutState ∧
      ∀ i, (run.finitePrefix k).emissionTimes i = cut.emissionTimes i := by
  obtain ⟨K, saturated⟩ := run.eventually_complete_of_time_bounded birth box fanout H
    (fun k => (strictlyBefore k).le)
  refine ⟨K, fun k after => ?_⟩
  obtain ⟨cutState, cut, isCut, cutComplete⟩ := reference.complete_prefix_at
    (run.state k).time (run.time_monotone (Nat.zero_le k))
    (by rw [complete.1]; exact strictlyBefore k)
  have runComplete := saturated k after
  have physical := birth.physical_invariant box
  have same := ((run.finitePrefix k).observational_unique cut box physical runComplete cutComplete).1
  exact ⟨cutState, cut, isCut, cutComplete, same,
    fun i => (run.finitePrefix k).emissionTimes_unique cut box physical runComplete cutComplete i⟩

end InfiniteExecution

#print axioms InfiniteExecution.eventually_complete_of_time_bounded
#print axioms InfiniteExecution.eventually_reference_sections

end KernelR.Hybrid
