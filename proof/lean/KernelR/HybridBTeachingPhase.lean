import KernelR.HybridCellPreparedTrain
import KernelR.HybridPhysicalInvariant
/-! Physical teaching bootstrap from a current fast-gain birth band, with other-cell traffic retained. -/
namespace KernelR.Hybrid

structure BTeachingPhase {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) where
  emissions : (e.emissionTimes i).length = 14
  error_target : e.ledger.error i p = 3 / 5
  error_other : ∀ q, q ≠ p → e.ledger.error i q = 0
  mark_target : e.ledger.mark i p = 1 / 10
  mark_other : ∀ q, q ≠ p → e.ledger.mark i q = 0
  gain_target : u.x i (.z p) = s.x i (.z p) + 3 / 5
  gain_other : ∀ q, q ≠ p → u.x i (.z q) = s.x i (.z q)
  recovery_gain : u.x i .b = s.x i .b + 1 / 10
  prepared : PreparedSection u i
  charge_rest : u.x i .q = 1 / 10
  raw_finished : ∀ q, u.raw i q = none

theorem CellDeliveryStep.transfer_ready_coordinates {n θ route s u i d ds}
    {e : @Execution n θ route s u} (cut : CellDeliveryStep e i d ds)
    (hs : ReadyCoordinates cut.beforeArrival i) : ReadyCoordinates cut.afterArrival i := by
  have hx := cut.entry.physical_continuous
  have hm := cut.modes_after
  exact ⟨by rw [hm.1]; exact hs.ready,by rw [hx]; exact hs.charge,
    fun p => ⟨by rw [hm.2]; exact (hs.auxiliary p).1,by rw [hx]; exact (hs.auxiliary p).2⟩⟩

theorem CellDeliveryStep.transfer_mark_entry {n θ route s u i d ds}
    {e : @Execution n θ route s u} (cut : CellDeliveryStep e i d ds)
    (hs : MarkEntry cut.beforeArrival i) : MarkEntry cut.afterArrival i := by
  have hx := cut.entry.physical_continuous
  have hm := cut.modes_after
  exact ⟨by rw [hm.1]; exact hs.slow,by rw [hx]; exact hs.charge,
    by rw [hx]; exact hs.recovery,
    fun p => ⟨by rw [hm.2]; exact (hs.auxiliary p).1,by rw [hx]; exact (hs.auxiliary p).2⟩⟩

/-- Sixteen separated received inputs prepare a low-recovery fast-gain cell.
The initial input is already active; all fifteen later arrivals are read from
this same multicell execution. No pulse-case word or desired dose is supplied. -/
theorem Execution.fast_teaching_phase {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : ReadyCoordinates s i)
    (hbrecovery : 7999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 8001 / 100000)
    (hz : Real.log (6 / 5) - 1 / 1000 ≤ s.x i (.z p) ∧ s.x i (.z p) ≤ Real.log (6 / 5) + 1 / 1000)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (next after third : ℝ) (tail : List ℝ) (htail : tail.length = 12)
    (hcalendar : e.cellDeliveries i = (next :: after :: third :: tail).map (fun t => ⟨i,p,t⟩))
    (hspace : (s.time :: next :: after :: third :: tail).Pairwise (fun t v => t + 15 / 2 ≤ v))
    (hupper : after ≤ next + 17 / 2)
    (hquiet : ∀ t ∈ s.time :: next :: after :: third :: tail, t + 15 / 2 ≤ u.time) :
    Nonempty (BTeachingPhase e i p) := by
  have hcal₁ : e.cellDeliveries i = ⟨i,p,next⟩ :: (after :: third :: tail).map (fun t => ⟨i,p,t⟩) := by
    simpa only [List.map_cons] using hcalendar
  obtain ⟨cut₁⟩ := e.first_cell_delivery i _ _ hcal₁
  have hgap₁ : s.time + 15 / 2 ≤ next := (List.pairwise_cons.mp hspace).1 next (by simp)
  obtain ⟨silent⟩ := cut₁.span.silent_pulse_of_invariant hb hf hv i p hs hz.2 hr ho
    cut₁.no_arrivals_before (by rw [cut₁.date.1]; exact hgap₁)
  have ready₁ := cut₁.transfer_ready_coordinates silent.coordinates
  have recovery₁ : 7999 / 100000 ≤ cut₁.afterArrival.x i .b ∧ cut₁.afterArrival.x i .b ≤ 8001 / 100000 := by
    rw [cut₁.entry.physical_continuous,silent.recovery_preserved]
    exact hbrecovery
  have gain₁ : 9 / 5 ≤ Real.exp (cut₁.afterArrival.x i (.z p)) ∧
      Real.exp (cut₁.afterArrival.x i (.z p)) ≤ 12 / 5 := by
    apply fast_learned_gain_bounds
    · rw [cut₁.entry.physical_continuous,silent.gain_target]
      linarith [hz.1]
    · rw [cut₁.entry.physical_continuous,silent.gain_target]
      linarith [hz.2]
  have raw₁ : cut₁.afterArrival.raw i p = some cut₁.afterArrival.time := cut₁.raw_after
  have other₁ : ∀ q, q ≠ p → cut₁.afterArrival.raw i q = none := by
    intro q hq
    rw [cut₁.raw_other i q (Or.inr hq)]
    exact silent.raw_finished q
  let advanced₁ := cut₁.span.append (.cons (.jump cut₁.entry) (.nil _))
  have invariant₁ := advanced₁.physical_invariant hb hf
  have valid₁ := advanced₁.raw_valid hv
  have hcal₂ : cut₁.rest.cellDeliveries i = ⟨i,p,after⟩ :: (third :: tail).map (fun t => ⟨i,p,t⟩) := by
    simpa only [List.map_cons] using cut₁.later
  obtain ⟨cut₂⟩ := cut₁.rest.first_cell_delivery i _ _ hcal₂
  have hspace₁ := (List.pairwise_cons.mp hspace).2
  have hgap₂ : next + 15 / 2 ≤ after := (List.pairwise_cons.mp hspace₁).1 after (by simp)
  obtain ⟨strong⟩ := cut₂.span.first_strong_low_recovery_of_valid hb invariant₁.region valid₁ i p
    ready₁ recovery₁ gain₁ raw₁ other₁ cut₂.no_arrivals_before
    (by rw [cut₁.date.2,cut₂.date.1]; exact ⟨hgap₂,hupper⟩)
  have markEntry₂ := cut₂.transfer_mark_entry strong.mark_entry
  have raw₂ : cut₂.afterArrival.raw i p = some cut₂.afterArrival.time := cut₂.raw_after
  have other₂ : ∀ q, q ≠ p → cut₂.afterArrival.raw i q = none := by
    intro q hq
    rw [cut₂.raw_other i q (Or.inr hq)]
    exact strong.raw_finished q
  let advanced₂ := cut₂.span.append (.cons (.jump cut₂.entry) (.nil _))
  have invariant₂ := advanced₂.physical_invariant hb invariant₁
  have valid₂ := advanced₂.raw_valid valid₁
  have hcal₃ : cut₂.rest.cellDeliveries i = ⟨i,p,third⟩ :: tail.map (fun t => ⟨i,p,t⟩) := by
    simpa only [List.map_cons] using cut₂.later
  obtain ⟨cut₃⟩ := cut₂.rest.first_cell_delivery i _ _ hcal₃
  have hspace₂ := (List.pairwise_cons.mp hspace₁).2
  have hgap₃ : after + 15 / 2 ≤ third := (List.pairwise_cons.mp hspace₂).1 third (by simp)
  obtain ⟨markPulse⟩ := cut₃.span.protected_pulse_of_invariant hb invariant₂ valid₂ i p markEntry₂
    raw₂ other₂ cut₃.no_arrivals_before (by rw [cut₂.date.2,cut₃.date.1]; exact hgap₃)
  have prepared₃ := cut₃.prepared markPulse.prepared
  have gain₃ : 9 / 5 ≤ Real.exp (cut₃.afterArrival.x i (.z p)) ∧
      Real.exp (cut₃.afterArrival.x i (.z p)) ≤ 12 / 5 := by
    rw [cut₃.entry.physical_continuous,markPulse.gain_preserved p,
      cut₂.entry.physical_continuous,strong.gain_preserved p]
    exact gain₁
  have raw₃ : cut₃.afterArrival.raw i p = some cut₃.afterArrival.time := cut₃.raw_after
  have other₃ : ∀ q, q ≠ p → cut₃.afterArrival.raw i q = none := by
    intro q hq
    rw [cut₃.raw_other i q (Or.inr hq)]
    exact markPulse.raw_finished q
  let advanced₃ := cut₃.span.append (.cons (.jump cut₃.entry) (.nil _))
  have invariant₃ := advanced₃.physical_invariant hb invariant₂
  have valid₃ := advanced₃.raw_valid valid₂
  have hspace₃ : (cut₃.afterArrival.time :: tail).Pairwise (fun t v => t + 15 / 2 ≤ v) := by
    rw [cut₃.date.2]
    exact (List.pairwise_cons.mp hspace₂).2
  have hquiet₃ : ∀ t ∈ cut₃.afterArrival.time :: tail, t + 15 / 2 ≤ u.time := by
    rw [cut₃.date.2]
    intro t ht
    exact hquiet t (by simp only [List.mem_cons] at ht ⊢; tauto)
  obtain ⟨train⟩ := prepared_cell_train_of_valid hb i p tail cut₃.rest invariant₃.region valid₃
    prepared₃ gain₃ raw₃ other₃ cut₃.later hspace₃ hquiet₃
  have hztarget : u.x i (.z p) = s.x i (.z p) + 3 / 5 := by
    rw [train.gain_preserved p,cut₃.entry.physical_continuous,markPulse.gain_preserved p,
      cut₂.entry.physical_continuous,strong.gain_preserved p,
      cut₁.entry.physical_continuous,silent.gain_target]
  have hzother : ∀ q, q ≠ p → u.x i (.z q) = s.x i (.z q) := by
    intro q hq
    rw [train.gain_preserved q,cut₃.entry.physical_continuous,markPulse.gain_preserved q,
      cut₂.entry.physical_continuous,strong.gain_preserved q,
      cut₁.entry.physical_continuous,silent.gain_other q hq]
  have hbgain : u.x i .b = s.x i .b + 1 / 10 := by
    rw [train.recovery_preserved,cut₃.entry.physical_continuous,markPulse.recovery_gain,
      cut₂.entry.physical_continuous,strong.recovery_preserved,
      cut₁.entry.physical_continuous,silent.recovery_preserved]
  have hmarkother : ∀ q, q ≠ p → e.ledger.mark i q = 0 := by
    intro q hq
    have hn : NoArrivalAt e i q := by
      intro d hd
      by_cases hi : d.cell = i
      · have hm : d ∈ e.cellDeliveries i := by simp [Execution.cellDeliveries,List.mem_filter,hd,hi]
        rw [hcalendar] at hm
        obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hm
        exact Or.inr (Ne.symm hq)
      · exact Or.inl hi
    have hquiet := e.aux_ready_without_input_band i q (hs.auxiliary q).1 (hs.auxiliary q).2.2 (ho q hq) hn
    exact e.mark_zero_aux i q .ready (by decide) (e.allStates_aux_flows i q .ready hquiet)
  have hmark : e.ledger.mark i p = 1 / 10 := by
    have hsum : e.ledger.recovery i = e.ledger.mark i p := by
      rw [e.recovery_sum_marks i]
      exact Finset.sum_eq_single p (fun q _ hq => hmarkother q hq) (by simp)
    have hbalance := e.recovery_balance i
    rw [hsum] at hbalance
    linarith
  refine ⟨⟨?_,?_,?_,hmark,hmarkother,hztarget,hzother,hbgain,train.prepared,train.charge_rest,train.raw_finished⟩⟩
  · rw [cut₁.emissions,silent.emissions,List.nil_append,cut₂.emissions,strong.emissions,
      cut₃.emissions,markPulse.emissions,List.nil_append,List.length_append,List.length_singleton,train.emissions,htail]
  · have h := e.gain_balance i p
    linarith
  · intro q hq
    have h := e.gain_balance i q
    rw [hzother q hq] at h
    linarith

end KernelR.Hybrid
