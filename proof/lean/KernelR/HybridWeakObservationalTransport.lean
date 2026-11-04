import KernelR.HybridWeakFlowCuts
import KernelR.HybridObservationalTransport

/-! Queue presentation changes preserve relaxed integral histories, their
actual FIRE lists and saturation at transverse threshold contacts. -/
namespace KernelR.Hybrid

/-- Re-present an actual flow with a permuted initial pending queue. -/
noncomputable def WeakFlow.rebase_observational {n θ s u t} (f : @WeakFlow n θ s u)
    (h : s.ObservationalEq t) : WeakFlow θ t {u with pending:=t.pending} where
  positive := by simpa only [←h.time] using f.positive
  path := f.path
  initial := by simpa only [←h.time] using f.initial.trans h.values
  final := f.final
  main_fixed := f.main_fixed.trans h.main
  aux_fixed := f.aux_fixed.trans h.aux
  raw_fixed := f.raw_fixed.trans h.raw
  queue_fixed := rfl
  continuous := by simpa only [←h.time] using f.continuous
  integrable := by simpa only [←h.time,←h.field] using f.integrable
  mark_integrable := by
    simpa only [←h.time,markAct,←h.main,←h.aux] using f.mark_integrable
  integral_eq := by
    simpa only [←h.time,←h.values,←h.field] using f.integral_eq
  guards := by
    simpa only [←h.time,WeakBeforeGuards,←h.main,←h.aux] using f.guards
  raw_support := by
    simpa only [←h.raw,←h.time] using f.raw_support
  pending_urgent := by
    intro d hd
    exact f.pending_urgent d (h.pending.mem_iff.mpr hd)

/-- The re-presented flow ends in the same physical state. -/
theorem WeakFlow.rebase_observational_final {n θ s u t} (f : @WeakFlow n θ s u)
    (h : s.ObservationalEq t) : u.ObservationalEq {u with pending:=t.pending} := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  exact (List.Perm.of_eq f.queue_fixed).trans h.pending

theorem WeakMove.transport_observational_emissions {n θ route s u t}
    (move : @WeakMove n θ route s u) (h : s.ObservationalEq t) :
    ∃ v, ∃ move' : WeakMove θ route t v,
      u.ObservationalEq v ∧ move'.ledger.emissions = move.ledger.emissions := by
  cases move with
  | flow flow =>
    exact ⟨_, .flow (flow.rebase_observational h), flow.rebase_observational_final h, rfl⟩
  | jump jump =>
    obtain ⟨v, jump', hv, he⟩ := jump.transport_observational_emissions h
    exact ⟨v, .jump jump', hv, he⟩

theorem WeakExecution.transport_observational_emissions_count {n θ route s u t}
    (execution : @WeakExecution n θ route s u) (h : s.ObservationalEq t) :
    ∃ v, ∃ execution' : WeakExecution θ route t v,
      u.ObservationalEq v ∧ execution'.ledger.emissions = execution.ledger.emissions ∧
      execution'.moveCount = execution.moveCount := by
  induction execution generalizing t with
  | nil s => exact ⟨t, .nil t, h, rfl, rfl⟩
  | cons move rest ih =>
    obtain ⟨mid, move', hm, hem⟩ := move.transport_observational_emissions h
    obtain ⟨v, rest', hv, her, hcount⟩ := ih hm
    refine ⟨v, .cons move' rest', hv, ?_, ?_⟩
    · simp only [WeakExecution.ledger, Ledger.add, hem, her]
    · simp only [WeakExecution.moveCount, hcount]

theorem weakCompleteThrough_of_observational {n θ route s u t v T}
    (execution : @WeakExecution n θ route s u) (execution' : WeakExecution θ route t v)
    (h : u.ObservationalEq v) (complete : WeakCompleteThrough execution T) :
    WeakCompleteThrough execution' T := by
  refine ⟨h.time.symm.trans complete.1, ?_, ?_⟩
  · intro w jump positive
    obtain ⟨w', jump', hw, _⟩ := jump.transport_observational_emissions h.symm
    exact complete.2.1 w' jump'
      ((jump.contactTransversal_of_observational jump' h.symm hw).mp positive)
  · intro d hd
    exact complete.2.2 d (h.pending.mem_iff.mpr hd)

/-- Strengthened native transport keeps the certificate on the reference
history; the competing weak history does not supply such a certificate. -/
theorem Execution.transport_observational_transversal {n θ route s u t}
    (execution : @Execution n θ route s u) (h : s.ObservationalEq t)
    (positive : execution.ContactsTransversal) :
    ∃ v, ∃ execution' : Execution θ route t v,
      u.ObservationalEq v ∧ execution'.ledger.emissions = execution.ledger.emissions ∧
      execution'.moveCount = execution.moveCount ∧ execution'.ContactsTransversal := by
  induction execution generalizing t with
  | nil s => exact ⟨t, .nil t, h, rfl, rfl, trivial⟩
  | cons move rest ih =>
    cases move with
    | flow flow =>
      have hm := flow.rebase_observational_final h
      obtain ⟨v, rest', hv, her, hcount, hp⟩ := ih hm positive
      refine ⟨v, .cons (.flow (flow.rebase_observational h)) rest', hv, ?_, ?_, hp⟩
      · simp only [Execution.ledger, Move.ledger, Flow.ledger, Ledger.add, her]
      · simp only [Execution.moveCount, hcount]
    | jump jump =>
      obtain ⟨mid, jump', hm, hem⟩ := jump.transport_observational_emissions h
      obtain ⟨v, rest', hv, her, hcount, hp⟩ := ih hm positive.2
      refine ⟨v, .cons (.jump jump') rest', hv, ?_, ?_, ?_⟩
      · simp only [Execution.ledger, Move.ledger, Ledger.add, hem, her]
      · simp only [Execution.moveCount, hcount]
      · exact ⟨(jump.contactTransversal_of_observational jump' h hm).mp positive.1, hp⟩

end KernelR.Hybrid
