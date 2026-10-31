import KernelR.HybridArrivals
import KernelR.HybridProtectedPulse
/-! Exact physical counts and prepared-section preservation for a finite period-eight source train. -/
namespace KernelR.Hybrid

theorem DeliveryStep.prepared {n θ route s u d ds} {e : @Execution n θ route s u}
    (cut : DeliveryStep e d ds) (i : Fin n) (hs : PreparedSection cut.beforeArrival i) :
    PreparedSection cut.afterArrival i := by
  have hx := cut.entry.physical_continuous
  have hm := cut.modes_after
  exact ⟨by rw [hm.1]; exact hs.ready,
    by rw [hx]; exact hs.charge,by rw [hx]; exact hs.recovery,
    by rw [hm.2,hx]; exact hs.auxiliary⟩

theorem DeliveryStep.ready_coordinates {n θ route s u d ds} {e : @Execution n θ route s u}
    (cut : DeliveryStep e d ds) (i : Fin n) (hs : ReadyCoordinates cut.beforeArrival i) :
    ReadyCoordinates cut.afterArrival i := by
  have hx := cut.entry.physical_continuous
  have hm := cut.modes_after
  exact ⟨by rw [hm.1]; exact hs.ready,by rw [hx]; exact hs.charge,
    by rw [hm.2,hx]; exact hs.auxiliary⟩

theorem DeliveryStep.mark_entry {n θ route s u d ds} {e : @Execution n θ route s u}
    (cut : DeliveryStep e d ds) (i : Fin n) (hs : MarkEntry cut.beforeArrival i) :
    MarkEntry cut.afterArrival i := by
  have hx := cut.entry.physical_continuous
  have hm := cut.modes_after
  exact ⟨by rw [hm.1]; exact hs.slow,
    by rw [hx]; exact hs.charge,by rw [hx]; exact hs.recovery,
    by rw [hm.2,hx]; exact hs.auxiliary⟩

theorem Jump.no_emissions_of_delivery {n route s u} (j : @Jump n route s u)
    (d : Delivery n) (hd : d ∈ j.deliveries) : j.ledger.emissions = [] := by
  cases j <;> simp_all [Jump.deliveries,Jump.ledger,Ledger.zero]

theorem DeliveryStep.emissions {n θ route s u d ds} {e : @Execution n θ route s u}
    (cut : DeliveryStep e d ds) (i : Fin n) :
    e.emissionTimes i = cut.span.emissionTimes i ++ cut.rest.emissionTimes i := by
  have hd : d ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
  calc
    e.emissionTimes i = (cut.span.append (.cons (.jump cut.entry) cut.rest)).emissionTimes i :=
      congrArg (fun actual => actual.emissionTimes i) cut.reconstruct
    _ = _ := by simp [Execution.emissionTimes_append,Execution.emissionTimes_cons,
      Move.ledger,cut.entry.no_emissions_of_delivery d hd]

structure PreparedTrain {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) (count : ℕ) where
  emissions : (e.emissionTimes i).length = count
  error_zero : ∀ p, e.ledger.error i p = 0
  mark_zero : ∀ p, e.ledger.mark i p = 0
  gain_preserved : ∀ p, u.x i (.z p) = s.x i (.z p)
  recovery_preserved : u.x i .b = s.x i .b
  prepared : PreparedSection u i
  charge_rest : u.x i .q = 1 / 10
  raw_finished : ∀ p, u.raw i p = none

/-- Once prepared, every input of an actual isolated period-eight train emits
once. The delivery cuts and all pulse cases are selected from the execution. -/
theorem prepared_train {n θ ε route born} (hborn : @BirthState n born) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) : ∀ (count : ℕ) {s u : Snapshot n} (e : Execution θ route s u)
    (_past : Execution θ route born s) (_hs : PreparedSection s i)
    (_hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (_hr : s.raw i p = some s.time) (_ho : ∀ q, q ≠ p → s.raw i q = none)
    (_hcalendar : e.deliveries = sourceTrain i p (s.time + 8) 8 count)
    (_ht : s.time + 8 * count + 15 / 2 ≤ u.time), Nonempty (PreparedTrain e i (count + 1)) := by
  intro count
  induction count with
  | zero =>
    intro s u e past hs hz hr ho hcalendar ht
    have hn : ∀ q, NoArrivalAt e i q := by
      intro q
      simp [NoArrivalAt,hcalendar,sourceTrain]
    obtain ⟨pulse⟩ := e.learned_mid_pulse past hborn hb i p hs hz hr ho hn (by simpa using ht)
    exact ⟨⟨by rw [pulse.emissions]; rfl,pulse.error_zero,pulse.mark_zero,pulse.gain_preserved,
      pulse.recovery_preserved,pulse.prepared,pulse.charge_rest,pulse.raw_finished⟩⟩
  | succ count ih =>
    intro s u e past hs hz hr ho hcalendar ht
    have hcalendar' : e.deliveries = ⟨i,p,s.time + 8⟩ :: sourceTrain i p (s.time + 8 + 8) 8 count := by
      simpa only [sourceTrain_succ] using hcalendar
    obtain ⟨cut⟩ := e.first_delivery _ _ hcalendar'
    have hdate := cut.date
    obtain ⟨pulse⟩ := cut.span.learned_mid_pulse past hborn hb i p hs hz hr ho
      (cut.no_arrivals_before i) (by have h := hdate.1; dsimp at h; linarith)
    have hnext := cut.prepared i pulse.prepared
    have hznext : 9 / 5 ≤ Real.exp (cut.afterArrival.x i (.z p)) ∧
        Real.exp (cut.afterArrival.x i (.z p)) ≤ 12 / 5 := by
      rw [cut.entry.physical_continuous,pulse.gain_preserved p]
      exact hz
    have hrnext : cut.afterArrival.raw i p = some cut.afterArrival.time := cut.raw_after
    have honext : ∀ q, q ≠ p → cut.afterArrival.raw i q = none := by
      intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
    have hnextCal : cut.rest.deliveries = sourceTrain i p (cut.afterArrival.time + 8) 8 count := by
      rw [cut.later,hdate.2]
    have hnextTime : cut.afterArrival.time + 8 * count + 15 / 2 ≤ u.time := by
      rw [hdate.2]
      push_cast at ht
      linarith
    let progressed := past.append (cut.span.append (.cons (.jump cut.entry) (.nil _)))
    obtain ⟨train⟩ := ih cut.rest progressed hnext hznext hrnext honext hnextCal hnextTime
    have hg : ∀ q, u.x i (.z q) = s.x i (.z q) := by
      intro q
      rw [train.gain_preserved q,cut.entry.physical_continuous,pulse.gain_preserved q]
    refine ⟨⟨?_,?_,?_,hg,?_,train.prepared,train.charge_rest,train.raw_finished⟩⟩
    · rw [cut.emissions i,List.length_append,pulse.emissions,train.emissions]
      simp only [List.length_singleton]
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

end KernelR.Hybrid
