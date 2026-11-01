import KernelR.HybridPreparedCalendar
import KernelR.HybridResidualLatency
/-! The first physical residual may advance one emission; prepared successors share the rest latency. -/
namespace KernelR.Hybrid

/-- The actual first learned output retains its original residual charge. -/
theorem LearnedPulse.residual_calendar {n θ ε route s u i} {e : @Execution n θ route s u}
    (pulse : LearnedPulse e i) (hb : PhysicalBox θ ε) (hi : UpperRegion s)
    (p : Port) (hs : PreparedSection s i) (hq : 1 / 10 ≤ s.x i .q)
    (hg : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15 / 2 ≤ u.time) :
    ∃ first : ℝ, 3 / 10 < first ∧ first < 9 / 10 ∧
      first ≤ restLatency (Real.exp (s.x i (.z p))) ∧ e.emissionTimes i = [s.time + first] := by
  let first := pulse.trigger.beforeFire.time - s.time
  have hlo : s.time + 3 / 10 < pulse.trigger.beforeFire.time := by
    simpa only [pulse.trigger.entry.time_unchanged] using pulse.trigger.early
  have hhi : pulse.trigger.beforeFire.time < s.time + 9 / 10 := by
    simpa only [pulse.trigger.entry.time_unchanged] using pulse.trigger.deadline
  refine ⟨first,by dsimp [first]; linarith,by dsimp [first]; linarith,
    pulse.latency_le_rest hb hi p hs hq hg hr ho hno ht,?_⟩
  rw [pulse.emissions]
  congr 1
  dsimp [first]
  ring

/-- A separated prepared train with a nonnegative initial residual has one
possibly advanced first latency. Its later inputs start at exact rest, so all
remaining actual outputs share the same real response-root latency. -/
theorem prepared_cell_residual_calendar_of_valid {n θ ε route} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) (times : List ℝ) {s u : Snapshot n} (e : Execution θ route s u)
    (hi : UpperRegion s) (hv : RawValid s) (hs : PreparedSection s i)
    (hq : 1 / 10 ≤ s.x i .q)
    (hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hcalendar : e.cellDeliveries i = times.map (fun t => ⟨i,p,t⟩))
    (hspace : (s.time :: times).Pairwise (fun t v => t + 15 / 2 ≤ v))
    (hquiet : ∀ t ∈ s.time :: times, t + 15 / 2 ≤ u.time) :
    ∃ first : ℝ, 3 / 10 < first ∧ first < 9 / 10 ∧
      first ≤ restLatency (Real.exp (s.x i (.z p))) ∧
      e.emissionTimes i = (s.time + first) :: times.map (fun t => t + restLatency (Real.exp (s.x i (.z p)))) := by
  cases times with
  | nil =>
    have hn : ∀ q, NoArrivalAt e i q := (e.cellDeliveries_empty_iff i).mp (by simpa using hcalendar)
    obtain ⟨pulse⟩ := e.learned_mid_pulse_of_valid hb hi hv i p hs hz hr ho hn (hquiet s.time (by simp))
    obtain ⟨first,hlo,hhi,hle,hem⟩ := pulse.residual_calendar hb hi p hs hq hz hr ho hn (hquiet s.time (by simp))
    exact ⟨first,hlo,hhi,hle,by simpa only [List.map_nil] using hem⟩
  | cons next tail =>
    have hcal : e.cellDeliveries i = ⟨i,p,next⟩ :: tail.map (fun t => ⟨i,p,t⟩) := by simpa using hcalendar
    obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcal
    have hdate := cut.date
    have hgap : s.time + 15 / 2 ≤ next := (List.pairwise_cons.mp hspace).1 next (by simp)
    obtain ⟨pulse⟩ := cut.span.learned_mid_pulse_of_valid hb hi hv i p hs hz hr ho
      cut.no_arrivals_before (by rw [hdate.1]; exact hgap)
    obtain ⟨first,hlo,hhi,hle,hem⟩ := pulse.residual_calendar hb hi p hs hq hz hr ho
      cut.no_arrivals_before (by rw [hdate.1]; exact hgap)
    have hnext := cut.prepared pulse.prepared
    have hx : cut.afterArrival.x i (.z p) = s.x i (.z p) := by
      rw [cut.entry.physical_continuous,pulse.gain_preserved p]
    have hqnext : cut.afterArrival.x i .q = 1 / 10 := by
      rw [cut.entry.physical_continuous,pulse.charge_rest]
    have hznext : 9 / 5 ≤ Real.exp (cut.afterArrival.x i (.z p)) ∧
        Real.exp (cut.afterArrival.x i (.z p)) ≤ 12 / 5 := by rw [hx]; exact hz
    have hrnext : cut.afterArrival.raw i p = some cut.afterArrival.time := cut.raw_after
    have honext : ∀ q, q ≠ p → cut.afterArrival.raw i q = none := by
      intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
    have hspaceNext : (cut.afterArrival.time :: tail).Pairwise (fun t v => t + 15 / 2 ≤ v) := by
      rw [hdate.2]
      exact (List.pairwise_cons.mp hspace).2
    have hquietNext : ∀ t ∈ cut.afterArrival.time :: tail, t + 15 / 2 ≤ u.time := by
      rw [hdate.2]
      intro t ht
      exact hquiet t (List.mem_cons_of_mem _ ht)
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    have htail := prepared_cell_calendar_of_valid hb i p tail cut.rest
      (advanced.upper_region hb hi) (advanced.raw_valid hv) hnext hqnext hznext hrnext honext
      cut.later hspaceNext hquietNext
    rw [hx,hdate.2] at htail
    refine ⟨first,hlo,hhi,hle,?_⟩
    rw [cut.emissions,hem,htail]
    rfl

end KernelR.Hybrid
