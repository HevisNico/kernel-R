import KernelR.HybridErrorSectionCovers
import KernelR.HybridInactiveSectionCovers
import KernelR.HybridCadenceWeakWarmupK

/-! The three weak leaf cycles retain their actual sensor sections and arrivals.
Open gates restrict to their recorded spans; inactive ports are checked on flows. -/
namespace KernelR.Hybrid

@[simp] theorem learningGatesOpen_append {n θ route s v u}
    (first : @Execution n θ route s v) (last : Execution θ route v u) :
    LearningGatesOpen (first.append last) ↔ LearningGatesOpen first ∧ LearningGatesOpen last :=
  first.allFlows_append last _

theorem Execution.error_exposed_of_gate_modes {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (aux : e.AuxFlows i p .error) (main : e.MainFlows i .ready)
    (gates : LearningGatesOpen e) : e.ErrorExposed i p := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow f => exact ⟨⟨aux.1, main.1,
        fun t ht => ⟨(gates.1 t ht i).1, (gates.1 t ht i).2.2 p⟩⟩,
        ih aux.2 main.2 gates.2⟩
    | jump j => exact ih aux main gates

theorem SensorCycle.error_cover_of_ready_gates {n θ route s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (gates : LearningGatesOpen e) (hv : RawValid s)
    (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p)
    (main : cycle.phases.errorPhase.span.AllStates (fun v => v.main i = .ready)) :
    Nonempty (ErrorSectionCover i p e) := by
  let tr := cycle.trigger
  let mk := cycle.phases.markPhase
  let si := cycle.phases.silentPhase
  let er := cycle.phases.errorPhase
  have gt : LearningGatesOpen tr.rest := by
    rw [tr.reconstruct, learningGatesOpen_append] at gates
    exact gates.2
  have gm : LearningGatesOpen mk.rest := by
    rw [mk.reconstruct, learningGatesOpen_append] at gt
    exact gt.2
  have gs : LearningGatesOpen si.rest := by
    rw [si.reconstruct, learningGatesOpen_append] at gm
    exact gm.2
  have ge : LearningGatesOpen er.span := by
    rw [er.reconstruct, learningGatesOpen_append] at gs
    exact gs.1
  have exposed := er.span.error_exposed_of_gate_modes i p er.flows
    (er.span.allStates_main_flows i .ready main) ge
  exact cycle.error_cover_of_exposed exposed (cycle.error_rest_ready hv hr hno)

theorem CadenceWeakResponse.section_covers {θ ε route s p k}
    (c : CadenceWeakResponse θ route s p k) (box : PhysicalBox θ ε)
    (gates : LearningGatesOpen c.execution) (raw : RawValid s)
    (active : s.raw 0 p = some s.time) (q : Port) :
    Nonempty (ErrorSectionCover 0 q c.execution) ∧
      Nonempty (MarkSectionCover 0 q c.execution) := by
  have ready := c.execution.ready_states_of_no_emissions 0 c.initial_ready c.pulse.emissions
  constructor
  · by_cases same : q = p
    · subst q
      exact c.pulse.cycle.error_cover_of_ready_gates gates raw active
        (by simp [NoArrivalAt, c.deliveries]) (c.pulse.cycle.error_states ready).1
    · obtain ⟨cover, _⟩ := c.execution.error_cover_of_zero_open box gates 0 q (c.pulse.error_other q same)
      exact ⟨cover⟩
  · obtain ⟨cover, _⟩ := c.execution.mark_cover_of_zero_open box gates 0 q (c.pulse.mark_zero q)
    exact ⟨cover⟩

theorem CadenceWeakNextSource.section_covers {θ ε route s p k later}
    {response : CadenceWeakResponse θ route s p k}
    (c : CadenceWeakNextSource response later) (box : PhysicalBox θ ε)
    (gates : LearningGatesOpen c.execution) (raw : RawValid s)
    (active : s.raw 0 p = some s.time) (q : Port) :
    Nonempty (ErrorSectionCover 0 q c.execution) ∧
      Nonempty (MarkSectionCover 0 q c.execution) := by
  rw [c.reconstruct, learningGatesOpen_append] at gates
  obtain ⟨⟨error⟩, ⟨mark⟩⟩ := response.section_covers box gates.1 raw active q
  rw [c.reconstruct]
  exact ⟨⟨error.append (.inactive (.jump c.arrival) (.nil _) trivial (.nil _))⟩,
    ⟨mark.append (.inactive (.jump c.arrival) (.nil _) trivial (.nil _))⟩⟩

theorem ConstructedCadenceWeakWarmupK.section_covers {θ ε route s p K}
    (c : ConstructedCadenceWeakWarmupK θ route s p K) (box : PhysicalBox θ ε)
    (gates : LearningGatesOpen c.execution) (raw : RawValid s)
    (active : s.raw 0 p = some s.time) (q : Port) :
    Nonempty (ErrorSectionCover 0 q c.execution) ∧
      Nonempty (MarkSectionCover 0 q c.execution) := by
  rw [c.reconstruct, learningGatesOpen_append, learningGatesOpen_append] at gates
  obtain ⟨⟨e₁⟩, ⟨m₁⟩⟩ := c.sourceFirst.section_covers box gates.1 raw active q
  obtain ⟨⟨e₂⟩, ⟨m₂⟩⟩ := c.sourceSecond.section_covers box gates.2.1
    c.sourceFirst.raw_valid c.sourceFirst.raw_active q
  obtain ⟨⟨e₃⟩, ⟨m₃⟩⟩ := c.sourceThird.section_covers box gates.2.2
    c.sourceSecond.raw_valid c.sourceSecond.raw_active q
  rw [c.reconstruct]
  exact ⟨⟨e₁.append (e₂.append e₃)⟩, ⟨m₁.append (m₂.append m₃)⟩⟩

#print axioms ConstructedCadenceWeakWarmupK.section_covers
end KernelR.Hybrid
