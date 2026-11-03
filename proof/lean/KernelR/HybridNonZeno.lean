import KernelR.HybridEventBudget
import KernelR.HybridPhases

/-!
# Physical-event non-Zeno consequences of finite-prefix budgets

An infinite syntactic sequence of moves may only subdivide a flow, so its
move count is not a physical-event count. Infinite physical activity below
means unbounded counts of actual jumps, independently of physical time.
The existing finite-prefix budget then implies that time is unbounded.
No progress or existence premise is smuggled into the event budget.
-/
namespace KernelR.Hybrid

theorem Execution.jumpCount_append {n θ route s u v}
    (left : @Execution n θ route s u) (right : Execution θ route u v) :
    (left.append right).jumpCount = left.jumpCount + right.jumpCount := by
  induction left with
  | nil => simp [Execution.append, Execution.jumpCount]
  | cons move rest ih =>
    simp only [Execution.append, Execution.jumpCount, ih]
    omega

/-- Actual successive admissible moves; no elapsed-time divergence is assumed.
This interface by itself does not define semantic maximality at a limit time.
-/
structure InfiniteExecution {n} (θ : Fin n → Parameters) (route : Router n) where
  state : ℕ → Snapshot n
  move : ∀ k, Move θ route (state k) (state (k + 1))

namespace InfiniteExecution

def finitePrefix {n θ route} (run : @InfiniteExecution n θ route) :
    (k : ℕ) → Execution θ route (run.state 0) (run.state k)
  | 0 => .nil _
  | k + 1 => (run.finitePrefix k).append (.cons (run.move k) (.nil _))

theorem prefix_jumpCount_succ {n θ route} (run : @InfiniteExecution n θ route)
    (k : ℕ) :
    (run.finitePrefix (k + 1)).jumpCount =
      (run.finitePrefix k).jumpCount + (run.move k).jumpCount := by
  simp [finitePrefix, Execution.jumpCount_append, Execution.jumpCount]

/-- This condition concerns event counts only; it is not a time-divergence or
fairness assumption. It separates physical jumps from flow subdivisions.
-/
def InfinitelyManyJumps {n θ route} (run : @InfiniteExecution n θ route) : Prop :=
  ∀ budget : ℕ, ∃ k, budget < (run.finitePrefix k).jumpCount

/-- Chronology follows from the actual moves; it is not an extra run premise. -/
theorem time_monotone {n θ route} (run : @InfiniteExecution n θ route) :
    Monotone (fun k => (run.state k).time) := by
  apply monotone_nat_of_le_succ
  intro k
  exact (Execution.cons (run.move k) (.nil _) :
    Execution θ route (run.state k) (run.state (k + 1))).time_monotone

/-- Every finite horizon admits one uniform physical-event bound across all
prefixes of this run which end by that horizon, including incomplete ones.
-/
theorem event_budget {n θ ε route F} (run : @InfiniteExecution n θ route)
    (birth : BirthState (run.state 0)) (box : PhysicalBox θ ε)
    (fanout : FanoutBound route F) (T : ℝ) :
    ∃ budget : ℕ, ∀ k, (run.state k).time ≤ T →
      (run.finitePrefix k).jumpCount ≤ budget := by
  obtain ⟨budget, bounds⟩ := finite_prefix_event_budget birth box fanout T
  exact ⟨budget, fun k before => bounds _ (run.finitePrefix k) before⟩

/-- Infinitely many physical jumps cannot accumulate below a finite time.
The conclusion is derived from R's physical event budget, not assumed.
-/
theorem time_unbounded_of_infinitely_many_jumps {n θ ε route F}
    (run : @InfiniteExecution n θ route)
    (birth : BirthState (run.state 0)) (box : PhysicalBox θ ε)
    (fanout : FanoutBound route F) (events : run.InfinitelyManyJumps) :
    ∀ T : ℝ, ∃ k, T < (run.state k).time := by
  intro T
  obtain ⟨budget, bounds⟩ := run.event_budget birth box fanout T
  obtain ⟨k, exceeded⟩ := events budget
  refine ⟨k, ?_⟩
  by_contra bounded
  exact (not_lt_of_ge (bounds k (le_of_not_gt bounded))) exceeded

/-- Once enough physical events have occurred, every later prefix is past
the chosen horizon. Actual move chronology strengthens unboundedness to
eventual time divergence.
-/
theorem time_diverges_of_infinitely_many_jumps {n θ ε route F}
    (run : @InfiniteExecution n θ route)
    (birth : BirthState (run.state 0)) (box : PhysicalBox θ ε)
    (fanout : FanoutBound route F) (events : run.InfinitelyManyJumps) :
    ∀ T : ℝ, ∃ K : ℕ, ∀ k, K ≤ k → T < (run.state k).time := by
  intro T
  obtain ⟨K, later⟩ := run.time_unbounded_of_infinitely_many_jumps birth box fanout events T
  exact ⟨K, fun k after => later.trans_le (run.time_monotone after)⟩

/-- No bound on the dates of all prefixes can coexist with infinitely many
physical jumps. This does not prohibit bounded-time, all-flow subdivisions.
-/
theorem no_physical_event_zeno {n θ ε route F}
    (run : @InfiniteExecution n θ route)
    (birth : BirthState (run.state 0)) (box : PhysicalBox θ ε)
    (fanout : FanoutBound route F) :
    ¬ (run.InfinitelyManyJumps ∧ ∃ T : ℝ, ∀ k, (run.state k).time ≤ T) := by
  rintro ⟨events, T, bounded⟩
  obtain ⟨k, later⟩ := run.time_unbounded_of_infinitely_many_jumps birth box fanout events T
  exact (not_lt_of_ge (bounded k)) later

end InfiniteExecution

#print axioms InfiniteExecution.no_physical_event_zeno

end KernelR.Hybrid
