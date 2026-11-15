import NativeStrongStep
import KernelR.HybridWeakInputCycleExistence

namespace NetworkStability.NativeStrong

open KernelR.Hybrid

/-- Transport the isolated weak cycle over the same spectator interval as
the strong leg. The operational queue is unchanged because no FIRE occurs. -/
theorem weak_step_exists {θ : Fin N → Parameters} {route : Router N}
    (box : PhysicalBox θ ε) (s : Snapshot N) (i : Fin N) (port : Port)
    (physical : PhysicalInvariant θ s) (valid : RawValid s)
    (prepared : PreparedSection s i)
    (gain : Real.exp (s.x i (.z port)) ≤ 1)
    (active : s.raw i port = some s.time) (other : ∀ q, q ≠ port → s.raw i q = none)
    (spectators : Spectators s i)
    (future : ∀ token ∈ s.pending, s.time + 15 / 2 ≤ token.due) :
    ∃ (u : Snapshot N) (e : Execution θ route s u),
      u.time = s.time + 15 / 2 ∧ u.pending = s.pending ∧
      e.deliveries = [] ∧ e.ledger.emissions = [] ∧
      (∀ j q, u.x j (.z q) = s.x j (.z q) + if j = i ∧ q = port then 3 / 5 else 0) ∧
      (∀ j, u.x j .b = s.x j .b) ∧
      (∀ j, PreparedSection s j → PreparedSection u j) ∧
      (∀ j q, u.raw j q = none) := by
  let θ₁ : Fin 1 → Parameters := fun _ => θ i
  let a := localView s i
  have start : a.time = s.time := rfl
  have good : PhysicalInvariant θ₁ a :=
    ⟨fun _ => physical.region i, fun _ q => physical.gain_cap i q,
      fun _ => physical.recovery_cap i, fun _ => physical.reserve i⟩
  have raw : RawValid a := fun _ p origin h => valid i p origin h
  have ready (j : Fin 1) : ReadyCoordinates a j :=
    ⟨prepared.ready, prepared.charge, prepared.auxiliary⟩
  have weak : Real.exp (a.x 0 (.z port)) ≤ 7 / 6 := by
    change Real.exp (s.x i (.z port)) ≤ 7 / 6
    linarith
  have logGain : a.x 0 (.z port) ≤ Real.log (6 / 5) + 1 / 1000 := by
    change s.x i (.z port) ≤ _
    have h := Real.exp_le_exp.mp (by simpa using gain : Real.exp (s.x i (.z port)) ≤ Real.exp 0)
    linarith [Real.log_pos (show (1 : ℝ) < 6 / 5 by norm_num)]
  obtain ⟨cycle⟩ := weak_input_cycle_exists (route := EmptyRouter 1) a
    (show PhysicalBox θ₁ ε from ⟨box.1, fun _ q => box.2 i q⟩)
    good raw 0 port ready weak logGain active (fun _ q h => by
      rcases h with h | h
      · exact (h (Subsingleton.elim _ _)).elim
      · exact other q h) (by intro token mem; cases mem)
  have noIssue : issuedBy route i cycle.execution.ledger.emissions = [] := by
    rw [cycle.emissions]
    rfl
  have future' : ∀ token ∈ s.pending ++ issuedBy route i cycle.execution.ledger.emissions,
      cycle.final.time ≤ token.due := by
    rw [noIssue, List.append_nil, cycle.date, start]
    exact future
  obtain ⟨lifted, fired, delivered⟩ := splice_execution s i spectators cycle.execution
    (show s.time ≤ a.time from le_rfl) cycle.deliveries s.pending future'
  have source : splice s i a s.pending = s := by
    have h := quietValues_initial s
    cases s
    simp [splice, a, localView, h]
  let u := splice s i cycle.final (s.pending ++ issuedBy route i cycle.execution.ledger.emissions)
  let e : Execution θ route s u := lifted.cast_source source.symm
  have time : u.time = s.time + 15 / 2 := cycle.date
  refine ⟨u, e, time, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [u, splice, noIssue]
  · exact (Execution.cast_source_deliveries lifted source.symm).trans delivered
  · rw [Execution.cast_source_ledger, fired, cycle.emissions]
    rfl
  · intro j q
    by_cases hj : j = i
    · subst j
      by_cases hp : q = port
      · subst q; simpa [u, splice, a, localView] using cycle.pulse.gain_target
      · simpa [u, splice, a, localView, hp] using cycle.pulse.gain_other q hp
    · simp [u, splice, hj, quietValues]
  · intro j
    by_cases h : j = i
    · subst j; simpa [u, splice, a, localView] using cycle.pulse.recovery_preserved
    · simp [u, splice, h, quietValues]
  · intro j h
    by_cases hj : j = i
    · subst j
      have p : PreparedSection a 0 := ⟨h.ready, h.charge, h.recovery, h.auxiliary⟩
      have r := cycle.pulse.prepared p
      exact ⟨by simpa [u, splice] using r.ready, by simpa [u, splice] using r.charge,
        by simpa [u, splice] using r.recovery, fun q => by simpa [u, splice] using r.auxiliary q⟩
    · have r := quietAt_ready_coordinates s j h.ready_coordinates (by rw [time]; linarith : s.time ≤ u.time)
      exact ⟨by simpa [u, splice, hj, quietAt] using r.ready,
        by simpa [u, splice, hj, quietAt] using r.charge,
        by simpa [u, splice, hj, quietValues] using h.recovery,
        fun q => by simpa [u, splice, hj, quietAt] using r.auxiliary q⟩
  · intro j q
    by_cases h : j = i
    · subst j; simpa [u, splice] using cycle.pulse.raw_finished q
    · simpa [u, splice, h] using spectators.raw j h q

end NetworkStability.NativeStrong
