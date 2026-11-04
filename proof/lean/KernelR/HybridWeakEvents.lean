import KernelR.HybridWeakExecution
import KernelR.HybridEvents

/-! Chronology of physical FIREs in the weak comparison envelope. -/
namespace KernelR.Hybrid
open Set

theorem WeakMove.emission_time {n θ route s u} (m : @WeakMove n θ route s u)
    (event : Fin n × ℝ) (he : event ∈ m.ledger.emissions) : event.2 = s.time := by
  cases m with
  | flow f => simp [WeakMove.ledger, WeakFlow.ledger] at he
  | jump j => cases j <;> simp_all [WeakMove.ledger, Jump.ledger, Ledger.zero]

theorem WeakMove.time_monotone {n θ route s u} (m : @WeakMove n θ route s u) : s.time ≤ u.time := by
  cases m with
  | flow f => exact f.positive.le
  | jump j => exact j.time_unchanged.ge

/-- Dates are obtained from actual firings and lie inside the execution interval. -/
theorem WeakExecution.emission_time_bounds {n θ route s u} (e : @WeakExecution n θ route s u)
    (event : Fin n × ℝ) (he : event ∈ e.ledger.emissions) :
    s.time ≤ event.2 ∧ event.2 ≤ u.time := by
  induction e with
  | nil => simp [ledger, Ledger.zero] at he
  | cons step rest ih =>
    have hm : event ∈ step.ledger.emissions ∨ event ∈ rest.ledger.emissions := by
      simpa only [ledger, Ledger.add, List.mem_append] using he
    rcases hm with hm | hm
    · rw [step.emission_time event hm]
      exact ⟨le_rfl, step.time_monotone.trans rest.time_monotone⟩
    · exact ⟨step.time_monotone.trans (ih hm).1, (ih hm).2⟩

/-- Equal-time events retain their actual legal order; no total event priority
is introduced by the chronology statement. -/
theorem WeakExecution.emissions_chronological {n θ route s u} (e : @WeakExecution n θ route s u) :
    e.ledger.emissions.Pairwise (fun x y => x.2 ≤ y.2) := by
  induction e with
  | nil => simp [ledger, Ledger.zero]
  | cons step rest ih =>
    have hs : step.ledger.emissions.Pairwise (fun x y => x.2 ≤ y.2) := by
      cases step with
      | flow f => simp [WeakMove.ledger, WeakFlow.ledger]
      | jump j => cases j <;> simp [WeakMove.ledger, Jump.ledger, Ledger.zero]
    change (step.ledger.emissions ++ rest.ledger.emissions).Pairwise _
    apply List.pairwise_append.mpr
    refine ⟨hs, ih, ?_⟩
    intro x hx y hy
    rw [step.emission_time x hx]
    exact step.time_monotone.trans (rest.emission_time_bounds y hy).1

theorem WeakExecution.emissionTimes_chronological {n θ route s u} (e : @WeakExecution n θ route s u)
    (i : Fin n) : (e.emissionTimes i).Pairwise (· ≤ ·) := by
  exact List.pairwise_map.mpr (e.emissions_chronological.filter _)


end KernelR.Hybrid
