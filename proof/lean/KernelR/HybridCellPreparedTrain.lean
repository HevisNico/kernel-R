import KernelR.HybridCellInputs
/-! Prepared physical inputs with variable gaps, inside the complete multicell trace. -/
namespace KernelR.Hybrid

/-- Prepared inputs may have any gaps at least 7.5. Other cells' deliveries and
all their legal events remain in the same original execution. -/
theorem prepared_cell_train_of_valid {n θ ε route} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) : ∀ (times : List ℝ) {s u : Snapshot n} (e : Execution θ route s u)
    (_hi : UpperRegion s) (_hv : RawValid s) (_hs : PreparedSection s i)
    (_hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (_hr : s.raw i p = some s.time) (_ho : ∀ q, q ≠ p → s.raw i q = none)
    (_hcalendar : e.cellDeliveries i = times.map (fun t => ⟨i,p,t⟩))
    (_hspace : (s.time :: times).Pairwise (fun t v => t + 15 / 2 ≤ v))
    (_hquiet : ∀ t ∈ s.time :: times, t + 15 / 2 ≤ u.time),
    Nonempty (PreparedTrain e i (times.length + 1)) := by
  intro times
  induction times with
  | nil =>
    intro s u e hi hv hs hz hr ho hcalendar hspace hquiet
    have hn : ∀ q, NoArrivalAt e i q := (e.cellDeliveries_empty_iff i).mp (by simpa using hcalendar)
    obtain ⟨pulse⟩ := e.learned_mid_pulse_of_valid hb hi hv i p hs hz hr ho hn (hquiet s.time (by simp))
    exact ⟨⟨by rw [pulse.emissions]; rfl,pulse.error_zero,pulse.mark_zero,pulse.gain_preserved,
      pulse.recovery_preserved,pulse.prepared,pulse.charge_rest,pulse.raw_finished⟩⟩
  | cons next times ih =>
    intro s u e hi hv hs hz hr ho hcalendar hspace hquiet
    have hcal : e.cellDeliveries i = ⟨i,p,next⟩ :: times.map (fun t => ⟨i,p,t⟩) := by simpa using hcalendar
    obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcal
    have hdate := cut.date
    have hgap : s.time + 15 / 2 ≤ next := (List.pairwise_cons.mp hspace).1 next (by simp)
    obtain ⟨pulse⟩ := cut.span.learned_mid_pulse_of_valid hb hi hv i p hs hz hr ho
      cut.no_arrivals_before (by rw [hdate.1]; exact hgap)
    have hnext := cut.prepared pulse.prepared
    have hznext : 9 / 5 ≤ Real.exp (cut.afterArrival.x i (.z p)) ∧
        Real.exp (cut.afterArrival.x i (.z p)) ≤ 12 / 5 := by
      rw [cut.entry.physical_continuous,pulse.gain_preserved p]
      exact hz
    have hrnext : cut.afterArrival.raw i p = some cut.afterArrival.time := cut.raw_after
    have honext : ∀ q, q ≠ p → cut.afterArrival.raw i q = none := by
      intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
    have hspaceNext : (cut.afterArrival.time :: times).Pairwise (fun t v => t + 15 / 2 ≤ v) := by
      rw [hdate.2]
      exact (List.pairwise_cons.mp hspace).2
    have hquietNext : ∀ t ∈ cut.afterArrival.time :: times, t + 15 / 2 ≤ u.time := by
      rw [hdate.2]
      intro t ht
      exact hquiet t (List.mem_cons_of_mem _ ht)
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    have hinext := advanced.upper_region hb hi
    have hvnext := advanced.raw_valid hv
    obtain ⟨train⟩ := ih cut.rest hinext hvnext hnext hznext hrnext honext cut.later hspaceNext hquietNext
    have hg : ∀ q, u.x i (.z q) = s.x i (.z q) := by
      intro q
      rw [train.gain_preserved q,cut.entry.physical_continuous,pulse.gain_preserved q]
    refine ⟨⟨?_,?_,?_,hg,?_,train.prepared,train.charge_rest,train.raw_finished⟩⟩
    · rw [cut.emissions,List.length_append,pulse.emissions,train.emissions]
      simp only [List.length_cons,List.length_nil]
      omega
    · intro q
      have h := e.gain_balance i q
      rw [hg q] at h
      linarith
    · intro q
      have hsplit := e.mark_split cut.span cut.entry cut.rest cut.reconstruct i q
      rw [pulse.mark_zero q,train.mark_zero q] at hsplit
      simpa only [zero_add] using hsplit
    · rw [train.recovery_preserved,cut.entry.physical_continuous,pulse.recovery_preserved]

theorem prepared_cell_train {n θ ε route born} (hborn : @BirthState n born) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) : ∀ (times : List ℝ) {s u : Snapshot n} (e : Execution θ route s u)
    (_past : Execution θ route born s) (_hs : PreparedSection s i)
    (_hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (_hr : s.raw i p = some s.time) (_ho : ∀ q, q ≠ p → s.raw i q = none)
    (_hcalendar : e.cellDeliveries i = times.map (fun t => ⟨i,p,t⟩))
    (_hspace : (s.time :: times).Pairwise (fun t v => t + 15 / 2 ≤ v))
    (_hquiet : ∀ t ∈ s.time :: times, t + 15 / 2 ≤ u.time),
    Nonempty (PreparedTrain e i (times.length + 1)) := by
  intro times s u e past hs hz hr ho hcalendar hspace hquiet
  exact prepared_cell_train_of_valid hb i p times e (past.upper_region hb hborn.upper_region)
    (past.raw_valid hborn.raw_valid) hs hz hr ho hcalendar hspace hquiet

end KernelR.Hybrid
