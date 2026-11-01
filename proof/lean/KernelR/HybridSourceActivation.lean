import KernelR.HybridTeachingActivation
/-! Zero-time source activation with every READY cell retained. -/
namespace KernelR.Hybrid

structure SourceActivation {n θ route s u i p start ds}
    {e : @Execution n θ route s u} (cut : CellDeliveryStep e i ⟨i,p,start⟩ ds) where
  coordinates : cut.afterArrival.x = s.x
  ready : ∀ k, ReadyCoordinates cut.afterArrival k
  raw_active : cut.afterArrival.raw i p = some cut.afterArrival.time
  raw_other : ∀ k q, k ≠ i ∨ q ≠ p → cut.afterArrival.raw k q = none
  before_emissions : cut.span.ledger.emissions = []
  advanced_emissions : (cut.span.append (.cons (.jump cut.entry) (.nil _))).ledger.emissions = []

theorem CellDeliveryStep.source_activation {n θ route s u i p start ds}
    {e : @Execution n θ route s u} (cut : CellDeliveryStep e i ⟨i,p,start⟩ ds)
    (hs : ∀ k, ReadyCoordinates s k) (hr : ∀ k q, s.raw k q = none)
    (ht : s.time = start)
    (hfuture : ∀ d ∈ s.pending, d.cell ≠ i → start < d.due) :
    Nonempty (SourceActivation cut) := by
  have hbefore : cut.beforeArrival.time = s.time := cut.date.1.trans ht.symm
  have hspanx := cut.span.zero_duration_continuous hbefore
  have hmain : ∀ k, cut.span.AllStates (fun v => v.main k = .ready) := by
    intro k
    exact cut.span.zero_duration_ready_main hbefore k (hs k).ready (by linarith [(hs k).charge.2])
  have haux : ∀ k q, cut.span.AllStates (fun v => v.aux k q = .ready) := by
    intro k q
    exact cut.span.zero_duration_ready_aux hbefore k q ((hs k).auxiliary q).1 (by
      linarith [((hs k).auxiliary q).2.2])
  have hem : cut.span.ledger.emissions = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro event he
    have hn := cut.span.no_emissions_of_ready_states event.1 (hmain event.1)
    have hm : event.2 ∈ cut.span.emissionTimes event.1 := by
      apply List.mem_map.mpr
      exact ⟨event,by simp [List.mem_filter,he],rfl⟩
    rw [hn] at hm
    contradiction
  have hd : (⟨i,p,start⟩ : Delivery n) ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
  let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
  have hadv : advanced.ledger.emissions = [] := by
    simp only [advanced,Execution.emissions_append,Execution.ledger,Move.ledger,Ledger.add,Ledger.zero,
      hem,cut.entry.no_emissions_of_delivery _ hd,List.append_nil]
  have hx : cut.afterArrival.x = s.x := cut.entry.physical_continuous.trans hspanx
  have hready : ∀ k, ReadyCoordinates cut.afterArrival k := by
    intro k
    refine ⟨?_,by rw [hx]; exact (hs k).charge,?_⟩
    · rw [cut.modes_after.1]
      exact cut.span.allStates_final (hmain k)
    · intro q
      refine ⟨?_,by rw [hx]; exact ((hs k).auxiliary q).2⟩
      rw [cut.modes_after.2]
      exact cut.span.allStates_final (haux k q)
  have hnoOther : ∀ k, k ≠ i → ∀ q, NoArrivalAt advanced k q := by
    intro k hk
    apply advanced.no_arrival_before_due k
    · intro d hd hc
      rw [cut.date.2]
      exact hfuture d hd (by simpa only [hc] using hk)
    · intro event he
      rw [hadv] at he
      contradiction
  refine ⟨⟨hx,hready,cut.raw_after,?_,hem,hadv⟩⟩
  intro k q hneq
  by_cases hk : k = i
  · subst k
    have hq : q ≠ p := by simpa only [ne_self_iff_false,false_or] using hneq
    rw [cut.raw_other i q (Or.inr hq)]
    exact (cut.span.raw_absent_of_no_arrival i q (hr i q) (cut.no_arrivals_before q)).1
  · exact (advanced.raw_absent_of_no_arrival k q (hr k q) (hnoOther k hk q)).1

theorem SourceActivation.prepared {n θ route s u i p start ds}
    {e : @Execution n θ route s u} {cut : CellDeliveryStep e i ⟨i,p,start⟩ ds}
    (act : SourceActivation cut) (k : Fin n) (hs : PreparedSection s k) :
    PreparedSection cut.afterArrival k := by
  exact ⟨(act.ready k).ready,(act.ready k).charge,
    by rw [act.coordinates]; exact hs.recovery,(act.ready k).auxiliary⟩

theorem SourceActivation.pending {n θ route s u i p start ds}
    {e : @Execution n θ route s u} {cut : CellDeliveryStep e i ⟨i,p,start⟩ ds}
    (act : SourceActivation cut)
    (hq : (s.pending.filter (fun d => d.cell = i)).Perm (⟨i,p,start⟩ :: ds)) :
    (cut.afterArrival.pending.filter (fun d => d.cell = i)).Perm ds := by
  let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
  have hdel : advanced.cellDeliveries i = [⟨i,p,start⟩] := by
    simp only [advanced,Execution.cellDeliveries,Execution.deliveries_append,List.filter_append,
      Execution.deliveries,Move.deliveries,cut.delivery,List.append_nil]
    change cut.span.cellDeliveries i ++ List.filter (fun d : Delivery n => d.cell = i) [⟨i,p,start⟩] = _
    rw [cut.no_earlier]
    simp
  exact advanced.cell_pending_perm_of_prefix i [⟨i,p,start⟩] ds
    (by simpa only [List.singleton_append] using hq) (List.Perm.of_eq hdel)
    (by intro event he; rw [act.advanced_emissions] at he; contradiction)

theorem SourceActivation.future {n θ route s u i p start ds}
    {e : @Execution n θ route s u} {cut : CellDeliveryStep e i ⟨i,p,start⟩ ds}
    (act : SourceActivation cut) (k : Fin n) (bound : ℝ)
    (hf : ∀ d ∈ s.pending, d.cell = k → bound ≤ d.due) :
    ∀ d ∈ cut.afterArrival.pending, d.cell = k → bound ≤ d.due := by
  let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
  intro d hd hc
  rcases advanced.pending_provenance d hd with h | ⟨event,he,_⟩
  · exact hf d h hc
  · rw [act.advanced_emissions] at he
    contradiction

theorem SourceActivation.empty {n θ route s u i p start ds}
    {e : @Execution n θ route s u} {cut : CellDeliveryStep e i ⟨i,p,start⟩ ds}
    (act : SourceActivation cut) (k : Fin n)
    (hf : s.pending.filter (fun d => d.cell = k) = []) :
    cut.afterArrival.pending.filter (fun d => d.cell = k) = [] := by
  let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
  classical
  apply List.filter_eq_nil_iff.mpr
  intro d hd
  simp only [decide_eq_true_eq]
  intro hc
  rcases advanced.pending_provenance d hd with h | ⟨event,he,_⟩
  · have hm : d ∈ s.pending.filter (fun d => d.cell = k) := by
      simp only [List.mem_filter,decide_eq_true_eq]
      exact ⟨h,hc⟩
    rw [hf] at hm
    contradiction
  · rw [act.advanced_emissions] at he
    contradiction

end KernelR.Hybrid
