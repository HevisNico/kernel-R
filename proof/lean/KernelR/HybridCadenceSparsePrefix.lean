import KernelR.HybridSparseLearnedPulse
import KernelR.HybridBoundaryIdle

/-! Actual sparse receiving inputs are consumed up to a designated dense
arrival, which remains active with its original cell memories preserved. -/
namespace KernelR.Hybrid

structure CadenceSparsePrefix {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (sparseDates : List ℝ) (firstStrong : ℝ)
    (denseFuture : List (Delivery n)) where
  entry : Snapshot n
  head : Execution θ route s entry
  rest : Execution θ route entry u
  reconstruct : e = head.append rest
  date : entry.time = firstStrong
  prepared : PreparedSection entry i
  charge_rest : entry.x i .q = 1 / 10
  gain_preserved : ∀ q, entry.x i (.z q) = s.x i (.z q)
  recovery_preserved : entry.x i .b = s.x i .b
  emissions : head.emissionTimes i =
    sparseDates.map (fun t => t + restLatency (Real.exp (s.x i (.z p))))
  error_zero : ∀ q, head.ledger.error i q = 0
  mark_zero : ∀ q, head.ledger.mark i q = 0
  raw_active : entry.raw i p = some entry.time
  raw_other : ∀ q, q ≠ p → entry.raw i q = none
  calendar : rest.cellDeliveries i = denseFuture

/-- A quiet prepared cell can wait arbitrarily long or zero time for its
first actual receiving-cell delivery. Other cells retain their real traffic. -/
theorem Execution.quiet_prepared_delivery_prefix {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (date : ℝ) (future : List (Delivery n))
    (hs : PreparedSection s i) (hq : s.x i .q = 1 / 10)
    (hr : ∀ q, s.raw i q = none)
    (hcalendar : e.cellDeliveries i = ⟨i,p,date⟩ :: future) :
    Nonempty (CadenceSparsePrefix e i p [] date future) := by
  obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcalendar
  obtain ⟨idle⟩ := cut.span.idle_prepared i hs hq hr cut.no_arrivals_before
  have hmain := cut.span.ready_without_input i hs.ready (by rw [hq]) hr cut.no_arrivals_before
  let head := cut.span.append (.cons (.jump cut.entry) (.nil _))
  have hgain : ∀ q, cut.afterArrival.x i (.z q) = s.x i (.z q) := by
    intro q
    rw [cut.entry.physical_continuous,idle.gain_preserved q]
  have hd : (⟨i,p,date⟩ : Delivery n) ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
  refine ⟨{
    entry := cut.afterArrival
    head := head
    rest := cut.rest
    reconstruct := ?_
    date := cut.date.2
    prepared := cut.prepared idle.prepared
    charge_rest := by rw [cut.entry.physical_continuous,idle.charge_rest]
    gain_preserved := hgain
    recovery_preserved := by rw [cut.entry.physical_continuous,idle.recovery_preserved]
    emissions := ?_
    error_zero := ?_
    mark_zero := ?_
    raw_active := cut.raw_after
    raw_other := ?_
    calendar := cut.later
  }⟩
  · calc
      e = cut.span.append (.cons (.jump cut.entry) cut.rest) := cut.reconstruct
      _ = _ := by simp only [head,Execution.append_assoc,Execution.append]
  · simp [head,Execution.emissionTimes_append,Execution.emissionTimes_cons,Move.ledger,
      cut.entry.no_emissions_of_delivery _ hd,idle.emissions]
    rfl
  · intro q
    have h := head.gain_balance i q
    rw [hgain q] at h
    linarith
  · intro q
    have hz := cut.span.mark_zero_ready i q (cut.span.allStates_main_flows i .ready hmain)
    simp [head,Execution.mark_append,Execution.ledger,Move.ledger,Ledger.add,Ledger.zero,cut.entry.mark_zero,hz]
  · intro q hq
    rw [cut.raw_other i q (Or.inr hq)]
    exact (cut.span.raw_absent_of_no_arrival i q (hr q) (cut.no_arrivals_before q)).1

/-- This internal active-input layer consumes each sparse pulse through its
proved return, while the designated next dense delivery is left fresh. -/
theorem sparse_prepared_active_prefix {n θ ε route} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) : ∀ (remaining : List ℝ) (firstStrong : ℝ)
    (future : List (Delivery n)) {s u : Snapshot n} (e : Execution θ route s u)
    (_hi : UpperRegion s) (_hv : RawValid s) (_hs : PreparedSection s i)
    (_hq : s.x i .q = 1 / 10)
    (_hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (_hr : s.raw i p = some s.time) (_ho : ∀ q, q ≠ p → s.raw i q = none)
    (_hcalendar : e.cellDeliveries i = remaining.map (fun t => ⟨i,p,t⟩) ++ ⟨i,p,firstStrong⟩ :: future)
    (_hspace : (s.time :: (remaining ++ [firstStrong])).Pairwise (fun t v => t + 7 ≤ v)),
    Nonempty (CadenceSparsePrefix e i p (s.time :: remaining) firstStrong future) := by
  intro remaining
  induction remaining with
  | nil =>
    intro firstStrong future s u e hi hv hs hq hz hr ho hcalendar hspace
    have hcal : e.cellDeliveries i = ⟨i,p,firstStrong⟩ :: future := by simpa using hcalendar
    obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcal
    have hgap : s.time + 7 ≤ firstStrong := (List.pairwise_cons.mp hspace).1 firstStrong (by simp)
    obtain ⟨pulse⟩ := cut.span.sparse_learned_pulse_of_valid hb hi hv i p hs hz hr ho
      cut.no_arrivals_before (by rw [cut.date.1]; exact hgap)
    have hem := pulse.sparse_emission_at_rest hb hi p hs hq hz hr ho cut.no_arrivals_before
      (by rw [cut.date.1]; exact hgap)
    let head := cut.span.append (.cons (.jump cut.entry) (.nil _))
    have hgain : ∀ q, cut.afterArrival.x i (.z q) = s.x i (.z q) := by
      intro q
      rw [cut.entry.physical_continuous,pulse.gain_preserved q]
    have hd : (⟨i,p,firstStrong⟩ : Delivery n) ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
    refine ⟨{
      entry := cut.afterArrival
      head := head
      rest := cut.rest
      reconstruct := ?_
      date := cut.date.2
      prepared := cut.prepared pulse.prepared
      charge_rest := by rw [cut.entry.physical_continuous,pulse.charge_rest]
      gain_preserved := hgain
      recovery_preserved := by rw [cut.entry.physical_continuous,pulse.recovery_preserved]
      emissions := ?_
      error_zero := ?_
      mark_zero := ?_
      raw_active := cut.raw_after
      raw_other := ?_
      calendar := cut.later
    }⟩
    · calc
        e = cut.span.append (.cons (.jump cut.entry) cut.rest) := cut.reconstruct
        _ = _ := by simp only [head,Execution.append_assoc,Execution.append]
    · simp [head,Execution.emissionTimes_append,Execution.emissionTimes_cons,Move.ledger,
        cut.entry.no_emissions_of_delivery _ hd,hem]
      rfl
    · intro q
      have h := head.gain_balance i q
      rw [hgain q] at h
      linarith
    · intro q
      simp [head,Execution.mark_append,Execution.ledger,Move.ledger,Ledger.add,Ledger.zero,
        cut.entry.mark_zero,pulse.mark_zero q]
    · intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
  | cons next remaining ih =>
    intro firstStrong future s u e hi hv hs hq hz hr ho hcalendar hspace
    have hcal : e.cellDeliveries i = ⟨i,p,next⟩ ::
        (remaining.map (fun t => ⟨i,p,t⟩) ++ ⟨i,p,firstStrong⟩ :: future) := by simpa using hcalendar
    obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcal
    have hgap : s.time + 7 ≤ next := (List.pairwise_cons.mp hspace).1 next (by simp)
    obtain ⟨pulse⟩ := cut.span.sparse_learned_pulse_of_valid hb hi hv i p hs hz hr ho
      cut.no_arrivals_before (by rw [cut.date.1]; exact hgap)
    have hem := pulse.sparse_emission_at_rest hb hi p hs hq hz hr ho cut.no_arrivals_before
      (by rw [cut.date.1]; exact hgap)
    have hnext := cut.prepared pulse.prepared
    have hqnext : cut.afterArrival.x i .q = 1 / 10 := by rw [cut.entry.physical_continuous,pulse.charge_rest]
    have hx : cut.afterArrival.x i (.z p) = s.x i (.z p) := by rw [cut.entry.physical_continuous,pulse.gain_preserved p]
    have hznext : 9 / 5 ≤ Real.exp (cut.afterArrival.x i (.z p)) ∧
        Real.exp (cut.afterArrival.x i (.z p)) ≤ 12 / 5 := by rw [hx]; exact hz
    have honext : ∀ q, q ≠ p → cut.afterArrival.raw i q = none := by
      intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
    have hspaceNext : (cut.afterArrival.time :: (remaining ++ [firstStrong])).Pairwise (fun t v => t + 7 ≤ v) := by
      rw [cut.date.2]
      exact (List.pairwise_cons.mp hspace).2
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    obtain ⟨warm⟩ := ih firstStrong future cut.rest (advanced.upper_region hb hi) (advanced.raw_valid hv)
      hnext hqnext hznext cut.raw_after honext cut.later hspaceNext
    let head := cut.span.append (.cons (.jump cut.entry) warm.head)
    have hgain : ∀ q, warm.entry.x i (.z q) = s.x i (.z q) := by
      intro q
      rw [warm.gain_preserved q,cut.entry.physical_continuous,pulse.gain_preserved q]
    have hd : (⟨i,p,next⟩ : Delivery n) ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
    refine ⟨{
      entry := warm.entry
      head := head
      rest := warm.rest
      reconstruct := ?_
      date := warm.date
      prepared := warm.prepared
      charge_rest := warm.charge_rest
      gain_preserved := hgain
      recovery_preserved := by rw [warm.recovery_preserved,cut.entry.physical_continuous,pulse.recovery_preserved]
      emissions := ?_
      error_zero := ?_
      mark_zero := ?_
      raw_active := warm.raw_active
      raw_other := warm.raw_other
      calendar := warm.calendar
    }⟩
    · calc
        e = cut.span.append (.cons (.jump cut.entry) cut.rest) := cut.reconstruct
        _ = cut.span.append (.cons (.jump cut.entry) (warm.head.append warm.rest)) :=
          congrArg (fun actual => cut.span.append (.cons (.jump cut.entry) actual)) warm.reconstruct
        _ = _ := by simp only [head,Execution.append_assoc,Execution.append]
    · have hw : warm.head.emissionTimes i =
          (next :: remaining).map (fun t => t + restLatency (Real.exp (s.x i (.z p)))) := by
        simpa only [hx,cut.date.2] using warm.emissions
      simp [head,Execution.emissionTimes_append,Execution.emissionTimes_cons,Move.ledger,
        cut.entry.no_emissions_of_delivery _ hd,hem,hw]
    · intro q
      have h := head.gain_balance i q
      rw [hgain q] at h
      linarith
    · intro q
      simp [head,Execution.mark_append,Execution.ledger,Move.ledger,Ledger.add,
        cut.entry.mark_zero,pulse.mark_zero q,warm.mark_zero q]

/-- A sparse receiving prefix begins from an idle prepared cell; all the
specified sparse deliveries emit, and the next dense arrival remains active. -/
theorem sparse_prepared_receiving_prefix {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s)
    (i : Fin n) (p : Port) (sparseDates : List ℝ) (firstStrong : ℝ) (future : List (Delivery n))
    (hs : PreparedSection s i) (hq : s.x i .q = 1 / 10)
    (hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : ∀ q, s.raw i q = none)
    (hcalendar : e.cellDeliveries i = sparseDates.map (fun t => ⟨i,p,t⟩) ++ ⟨i,p,firstStrong⟩ :: future)
    (hspace : (sparseDates ++ [firstStrong]).Pairwise (fun t v => t + 7 ≤ v)) :
    Nonempty (CadenceSparsePrefix e i p sparseDates firstStrong future) := by
  cases sparseDates with
  | nil =>
    exact e.quiet_prepared_delivery_prefix i p firstStrong future hs hq hr (by simpa using hcalendar)
  | cons first tail =>
    have hcal : e.cellDeliveries i = ⟨i,p,first⟩ ::
        (tail.map (fun t => ⟨i,p,t⟩) ++ ⟨i,p,firstStrong⟩ :: future) := by simpa using hcalendar
    obtain ⟨quiet⟩ := e.quiet_prepared_delivery_prefix i p first
      (tail.map (fun t => ⟨i,p,t⟩) ++ ⟨i,p,firstStrong⟩ :: future) hs hq hr hcal
    have hznext : 9 / 5 ≤ Real.exp (quiet.entry.x i (.z p)) ∧
        Real.exp (quiet.entry.x i (.z p)) ≤ 12 / 5 := by rw [quiet.gain_preserved p]; exact hz
    have hspaceNext : (quiet.entry.time :: (tail ++ [firstStrong])).Pairwise (fun t v => t + 7 ≤ v) := by
      rw [quiet.date]
      exact hspace
    obtain ⟨warm⟩ := sparse_prepared_active_prefix hb i p tail firstStrong future quiet.rest
      (quiet.head.upper_region hb hi) (quiet.head.raw_valid hv) quiet.prepared quiet.charge_rest hznext
      quiet.raw_active quiet.raw_other quiet.calendar hspaceNext
    let head := quiet.head.append warm.head
    have hgain : ∀ q, warm.entry.x i (.z q) = s.x i (.z q) := by
      intro q
      rw [warm.gain_preserved q,quiet.gain_preserved q]
    refine ⟨{
      entry := warm.entry
      head := head
      rest := warm.rest
      reconstruct := ?_
      date := warm.date
      prepared := warm.prepared
      charge_rest := warm.charge_rest
      gain_preserved := hgain
      recovery_preserved := by rw [warm.recovery_preserved,quiet.recovery_preserved]
      emissions := ?_
      error_zero := ?_
      mark_zero := ?_
      raw_active := warm.raw_active
      raw_other := warm.raw_other
      calendar := warm.calendar
    }⟩
    · calc
        e = quiet.head.append quiet.rest := quiet.reconstruct
        _ = quiet.head.append (warm.head.append warm.rest) :=
          congrArg (fun actual => quiet.head.append actual) warm.reconstruct
        _ = _ := by rw [← Execution.append_assoc]
    · have hw : warm.head.emissionTimes i =
          (first :: tail).map (fun t => t + restLatency (Real.exp (s.x i (.z p)))) := by
        simpa only [quiet.gain_preserved p,quiet.date] using warm.emissions
      simp only [head,Execution.emissionTimes_append,quiet.emissions,List.map_nil,List.nil_append]
      exact hw
    · intro q
      have h := head.gain_balance i q
      rw [hgain q] at h
      linarith
    · intro q
      simp only [head,Execution.mark_append,quiet.mark_zero q,warm.mark_zero q,add_zero]

/-- Own nominal-plus-three-dose gain is retained through the whole sparse
prefix; no desired firing count or pulse case is assumed. -/
theorem Execution.cadence_sparse_prefix {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (sparseDates : List ℝ) (firstStrong : ℝ) (future : List (Delivery n))
    (hs : PreparedSection s i) (hq : s.x i .q = 1 / 10)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hr : ∀ q, s.raw i q = none)
    (hcalendar : e.cellDeliveries i = sparseDates.map (fun t => ⟨i,p,t⟩) ++ ⟨i,p,firstStrong⟩ :: future)
    (hspace : (sparseDates ++ [firstStrong]).Pairwise (fun t v => t + 7 ≤ v)) :
    Nonempty (CadenceSparsePrefix e i p sparseDates firstStrong future) := by
  have hg := learned_gain_bounds hz.1 hz.2
  exact sparse_prepared_receiving_prefix e hb hf.region hv i p sparseDates firstStrong future hs hq
    ⟨hg.1,by linarith [hg.2]⟩ hr hcalendar hspace

end KernelR.Hybrid
