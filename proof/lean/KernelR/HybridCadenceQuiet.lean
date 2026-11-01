import KernelR.HybridCadenceRouter
import KernelR.HybridBoundaryIdle
/-! Physical silence propagates down the actual acyclic cadence contacts. -/
namespace KernelR.Hybrid

theorem Contact.route_source {n} (c : Contact n) {i t d} (hd : d ∈ c.route i t) : i = c.source := by
  classical
  unfold Contact.route at hd
  split_ifs at hd with h
  · exact h.1
  · contradiction

/-- A silent source issues no actual receiving-cell tokens on its contact.
Other ports and contacts remain in the same physical execution. -/
theorem Execution.contact_closed_of_silent_source {n θ route s u} (e : @Execution n θ route s u)
    (c : Contact n) (hs : e.emissionTimes c.source = [])
    (hw : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = c.target) = c.route event.1 event.2) :
    ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ c.target := by
  intro event he d hd hc
  have hm : d ∈ (route event.1 event.2).filter (fun d => d.cell = c.target) := by
    simp only [List.mem_filter,decide_eq_true_eq]
    exact ⟨hd,hc⟩
  rw [hw event he] at hm
  have hsource := c.route_source hm
  have ht : event.2 ∈ e.emissionTimes c.source := by
    apply List.mem_map.mpr
    exact ⟨event,by simp [List.mem_filter,he,hsource],rfl⟩
  rw [hs] at ht
  contradiction

/-- An empty receiving queue stays empty and receives no delivery when no
actual emission routes there. This conclusion needs no complete time horizon. -/
theorem Execution.empty_cell_without_routing {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hs : s.pending.filter (fun d => d.cell = i) = [])
    (hr : ∀ event ∈ e.ledger.emissions, ∀ d ∈ route event.1 event.2, d.cell ≠ i) :
    (∀ p, NoArrivalAt e i p) ∧ u.pending.filter (fun d => d.cell = i) = [] := by
  have hsource : ∀ d ∈ s.pending, d.cell ≠ i := by
    intro d hd hc
    have hm : d ∈ s.pending.filter (fun d => d.cell = i) := by
      simp only [List.mem_filter,decide_eq_true_eq]
      exact ⟨hd,hc⟩
    rw [hs] at hm
    contradiction
  constructor
  · intro p d hd
    rcases e.delivery_provenance d hd with h | ⟨event,he,hw⟩
    · exact Or.inl (hsource d h)
    · exact Or.inl (hr event he d hw)
  · classical
    apply List.filter_eq_nil_iff.mpr
    intro d hd
    simp only [decide_eq_true_eq]
    intro hc
    rcases e.pending_provenance d hd with h | ⟨event,he,hw⟩
    · exact hsource d h hc
    · exact hr event he d hw hc

structure CadenceDownstreamIdle {θ route s u} (e : @Execution 3 θ route s u) where
  a_idle : IdlePrepared e 0
  b_idle : IdlePrepared e 1
  a_raw : ∀ p, u.raw 0 p = none
  b_raw : ∀ p, u.raw 1 p = none
  a_empty : u.pending.filter (fun d => d.cell = 0) = []
  b_empty : u.pending.filter (fun d => d.cell = 1) = []

/-- The proved absence of C outputs propagates through C-to-B-to-A. Both old
cells, every legal interleaving and all future C tokens remain in the trace. -/
theorem Execution.cadence_downstream_idle {θ s u} (forward backward : ℝ → ℝ)
    (e : @Execution 3 θ (cadenceRouter forward backward) s u)
    (ha : PreparedSection s 0) (hqa : s.x 0 .q = 1 / 10) (hra : ∀ p, s.raw 0 p = none)
    (hb : PreparedSection s 1) (hqb : s.x 1 .q = 1 / 10) (hrb : ∀ p, s.raw 1 p = none)
    (hAempty : s.pending.filter (fun d => d.cell = 0) = [])
    (hBempty : s.pending.filter (fun d => d.cell = 1) = [])
    (hCquiet : e.emissionTimes 2 = []) : Nonempty (CadenceDownstreamIdle e) := by
  have hclosedB := e.contact_closed_of_silent_source (cadenceForwardContact forward) hCquiet
    (fun event _ => cadenceRouter.to_b forward backward event.1 event.2)
  have hB := e.empty_cell_without_routing 1 hBempty hclosedB
  obtain ⟨bIdle⟩ := e.idle_prepared 1 hb hqb hrb hB.1
  have hclosedA := e.contact_closed_of_silent_source (cadenceReturnContact backward) bIdle.emissions
    (fun event _ => cadenceRouter.to_a forward backward event.1 event.2)
  have hA := e.empty_cell_without_routing 0 hAempty hclosedA
  obtain ⟨aIdle⟩ := e.idle_prepared 0 ha hqa hra hA.1
  exact ⟨⟨aIdle,bIdle,fun p => (e.raw_absent_of_no_arrival 0 p (hra p) (hA.1 p)).1,
    fun p => (e.raw_absent_of_no_arrival 1 p (hrb p) (hB.1 p)).1,hA.2,hB.2⟩⟩

end KernelR.Hybrid
