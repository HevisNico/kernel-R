import KernelR.HybridExecutionTools
import KernelR.HybridSensor

/-! Protected auxiliary phases retain their mode at every discrete snapshot,
not merely on their positive-duration flows. This includes zero-time jumps on
other coordinates. -/
namespace KernelR.Hybrid

theorem Execution.auxFlows_append_sections {n θ route s v u}
    (first : @Execution n θ route s v) (last : Execution θ route v u)
    (i : Fin n) (p : Port) (mode : AuxMode) :
    (first.append last).AuxFlows i p mode ↔
      first.AuxFlows i p mode ∧ last.AuxFlows i p mode := by
  induction first with
  | nil => simp [append, AuxFlows]
  | cons move rest ih => cases move <;> simp [append, AuxFlows, ih, and_assoc]

private theorem Execution.successor_fixed_of_protected_flows {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port) (mode : AuxMode)
    (hne : mode ≠ .ready) (hs : s.aux i p = auxSuccessor mode)
    (hq : s.x i (.m p) = protectedFloor mode) (flows : e.AuxFlows i p mode) :
    u.aux i p = auxSuccessor mode := by
  induction e with
  | nil => exact hs
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      have h : auxSuccessor mode = mode := hs.symm.trans flows.1
      cases mode <;> simp_all [auxSuccessor]
    | jump j =>
      have hv : v.aux i p = auxSuccessor mode := by
        by_contra changed
        cases mode with
        | ready => exact hne rfl
        | mark =>
          have guard := (j.protected_aux_departure i p .silent (by decide) hs changed).1
          rw [hq] at guard
          norm_num [protectedFloor] at guard
        | silent =>
          have guard := (j.protected_aux_departure i p .error (by decide) hs changed).1
          rw [hq] at guard
          norm_num [protectedFloor] at guard
        | error =>
          have guard := (j.ready_aux_departure i p hs changed).1
          rw [hq] at guard
          norm_num [protectedFloor] at guard
      exact ih hv (by rw [j.physical_continuous]; exact hq) flows

/-- A protected phase cannot leave its mode and silently return through
zero-time jumps. The first departure reaches the next mode's entry charge;
another departure needs a different charge and hence a forbidden flow. -/
theorem Execution.aux_states_of_protected_flows {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port) (mode : AuxMode)
    (hne : mode ≠ .ready) (hs : s.aux i p = mode) (hu : u.aux i p = mode)
    (flows : e.AuxFlows i p mode) :
    e.AllStates (fun v => v.aux i p = mode) := by
  rcases e.first_state_change (fun v => v.aux i p) mode
    (fun f => congrFun (congrFun f.aux_fixed i) p) hs with
      states | ⟨v, w, span, exit, rest, he, states, hv, hw⟩
  · exact states
  · have departure := exit.protected_aux_departure i p mode hne hv hw
    have hrest : rest.AuxFlows i p mode := by
      rw [he, Execution.auxFlows_append_sections] at flows
      exact flows.2
    have fixed := rest.successor_fixed_of_protected_flows i p mode hne departure.2
      (by rw [exit.physical_continuous]; exact departure.1) hrest
    have bad : auxSuccessor mode = mode := fixed.symm.trans hu
    cases mode <;> simp_all [auxSuccessor]

end KernelR.Hybrid
