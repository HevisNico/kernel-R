import KernelR.HybridCadenceWeakStages
import KernelR.HybridResidualLatency
import KernelR.HybridCellInputs
/-! Three actual period-four silent inputs with quantitative carried charge. -/
namespace KernelR.Hybrid

noncomputable def cadenceStageCap (stage : ℕ) : ℝ :=
  if stage = 0 then 1 / 10 else if stage = 1 then 3 / 20 else if stage = 2 then 1 / 5 else 3 / 10

theorem cadenceStageCap_input (k : Fin 3) : cadenceStageCap k.val = cadenceWeakInputCap k := by
  fin_cases k <;> norm_num [cadenceStageCap,cadenceWeakInputCap]

theorem cadenceStageCap_output (k : Fin 3) : cadenceWeakOutputCap k = cadenceStageCap (k.val + 1) := by
  fin_cases k <;> norm_num [cadenceStageCap,cadenceWeakOutputCap]

theorem CellDeliveryStep.cadence_ready_coordinates {n θ route s u i d ds cap}
    {e : @Execution n θ route s u} (cut : CellDeliveryStep e i d ds)
    (hs : CadenceReadyCoordinates cut.beforeArrival i cap) : CadenceReadyCoordinates cut.afterArrival i cap := by
  have hx := cut.entry.physical_continuous
  have hm := cut.modes_after
  exact ⟨by rw [hm.1]; exact hs.ready,
    by rw [hx]; exact hs.charge,
    fun p => ⟨by rw [hm.2]; exact (hs.auxiliary p).1,by rw [hx]; exact (hs.auxiliary p).2⟩⟩

structure CadenceSilentWarmup {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (weakTimes : List ℝ) (future : List (Delivery n)) where
  entry : Snapshot n
  head : Execution θ route s entry
  rest : Execution θ route entry u
  reconstruct : e = head.append rest
  date : entry.time = weakTimes.getLastD s.time
  coordinates : CadenceReadyCoordinates entry i (3 / 10)
  gain_target : entry.x i (.z p) = s.x i (.z p) + (3 / 5) * weakTimes.length
  gain_other : ∀ q, q ≠ p → entry.x i (.z q) = s.x i (.z q)
  recovery_preserved : entry.x i .b = s.x i .b
  emissions : head.emissionTimes i = []
  error_target : head.ledger.error i p = (3 / 5) * weakTimes.length
  error_other : ∀ q, q ≠ p → head.ledger.error i q = 0
  mark_zero : ∀ q, head.ledger.mark i q = 0
  raw_active : entry.raw i p = some entry.time
  raw_other : ∀ q, q ≠ p → entry.raw i q = none
  calendar : rest.cellDeliveries i = future
  charge_lower : 1 / 10 ≤ s.x i .q → 1 / 10 ≤ entry.x i .q
  physical : PhysicalInvariant θ entry
  raw_valid : RawValid entry

/-- Actual receiving-cell cuts derive all silent cases and learning doses.
The three distinct scalar charge caps are preserved across the real arrivals;
the subsequent strong input and all other-cell traffic remain in the trace. -/
theorem cadence_silent_warmup {n θ ε route} (hb : @PhysicalBox n θ ε) (i : Fin n) (p : Port) :
    ∀ (weakTimes : List ℝ) (stage : ℕ) (future : List (Delivery n))
    {s u : Snapshot n} (e : Execution θ route s u)
    (_hf : PhysicalInvariant θ s) (_hv : RawValid s)
    (_hs : CadenceReadyCoordinates s i (cadenceStageCap stage))
    (_hstage : stage + weakTimes.length = 3)
    (_hz : s.x i (.z p) ≤ Real.log (3 / 10) + (3 / 5) * stage + 1 / 100000)
    (_hr : s.raw i p = some s.time) (_ho : ∀ q, q ≠ p → s.raw i q = none)
    (_hcalendar : e.cellDeliveries i = weakTimes.map (fun t => ⟨i,p,t⟩) ++ future)
    (_hspace : (s.time :: weakTimes).Pairwise (fun t v => t + 4 ≤ v)),
    Nonempty (CadenceSilentWarmup e i p weakTimes future) := by
  intro weakTimes
  induction weakTimes with
  | nil =>
    intro stage future s u e hf hv hs hstage hz hr ho hcalendar hspace
    have hstage' : stage = 3 := by simp only [List.length_nil,Nat.add_zero] at hstage; exact hstage
    have hcoords : CadenceReadyCoordinates s i (3 / 10) := by simpa [cadenceStageCap,hstage'] using hs
    exact ⟨⟨s,.nil _,e,rfl,rfl,hcoords,by simp,fun _ _ => rfl,rfl,rfl,
      by simp [Execution.ledger,Ledger.zero],fun _ _ => rfl,fun _ => rfl,hr,ho,
      by simpa only [List.map_nil,List.nil_append] using hcalendar,fun h => h,hf,hv⟩⟩
  | cons next weakTimes ih =>
    intro stage future s u e hf hv hs hstage hz hr ho hcalendar hspace
    have hstage' : stage ≤ 2 := by simp only [List.length_cons] at hstage; omega
    let k : Fin 3 := ⟨stage,by omega⟩
    have hinput : cadenceStageCap stage = cadenceWeakInputCap k := cadenceStageCap_input k
    have houtput : cadenceWeakOutputCap k = cadenceStageCap (stage + 1) := cadenceStageCap_output k
    have hcal : e.cellDeliveries i = ⟨i,p,next⟩ :: (weakTimes.map (fun t => ⟨i,p,t⟩) ++ future) := by
      simpa only [List.map_cons,List.cons_append] using hcalendar
    obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcal
    have hgap : s.time + 4 ≤ next := (List.pairwise_cons.mp hspace).1 next (by simp)
    obtain ⟨pulse⟩ := cut.span.cadence_weak_stage hb hf hv i p k
      (by rw [← hinput]; exact hs) (by simpa only [k] using hz) hr ho cut.no_arrivals_before
      (by rw [cut.date.1]; exact hgap)
    have hnext := cut.cadence_ready_coordinates pulse.coordinates
    rw [houtput] at hnext
    have hznext : cut.afterArrival.x i (.z p) ≤
        Real.log (3 / 10) + (3 / 5) * (stage + 1 : ℕ) + 1 / 100000 := by
      rw [cut.entry.physical_continuous,pulse.gain_target]
      push_cast
      linarith
    have hrnext : cut.afterArrival.raw i p = some cut.afterArrival.time := cut.raw_after
    have honext : ∀ q, q ≠ p → cut.afterArrival.raw i q = none := by
      intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    have hspaceNext : (cut.afterArrival.time :: weakTimes).Pairwise (fun t v => t + 4 ≤ v) := by
      rw [cut.date.2]
      exact (List.pairwise_cons.mp hspace).2
    obtain ⟨warm⟩ := ih (stage + 1) future cut.rest (advanced.physical_invariant hb hf) (advanced.raw_valid hv)
      hnext (by simp only [List.length_cons] at hstage; omega) hznext hrnext honext cut.later hspaceNext
    let head := cut.span.append (.cons (.jump cut.entry) warm.head)
    have hd : (⟨i,p,next⟩ : Delivery n) ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
    have hem : head.emissionTimes i = [] := by
      simp [head,Execution.emissionTimes_append,Execution.emissionTimes_cons,Move.ledger,
        cut.entry.no_emissions_of_delivery _ hd,pulse.emissions,warm.emissions]
    have hgain : warm.entry.x i (.z p) = s.x i (.z p) + (3 / 5) * (next :: weakTimes).length := by
      rw [warm.gain_target,cut.entry.physical_continuous,pulse.gain_target]
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      ring
    have hother : ∀ q, q ≠ p → warm.entry.x i (.z q) = s.x i (.z q) := by
      intro q hq
      rw [warm.gain_other q hq,cut.entry.physical_continuous,pulse.gain_other q hq]
    refine ⟨{
      entry := warm.entry
      head := head
      rest := warm.rest
      reconstruct := ?_
      date := ?_
      coordinates := warm.coordinates
      gain_target := hgain
      gain_other := hother
      recovery_preserved := ?_
      emissions := hem
      error_target := ?_
      error_other := ?_
      mark_zero := ?_
      raw_active := warm.raw_active
      raw_other := warm.raw_other
      calendar := warm.calendar
      charge_lower := ?_
      physical := head.physical_invariant hb hf
      raw_valid := head.raw_valid hv
    }⟩
    · calc
        e = cut.span.append (.cons (.jump cut.entry) cut.rest) := cut.reconstruct
        _ = cut.span.append (.cons (.jump cut.entry) (warm.head.append warm.rest)) :=
          congrArg (fun actual => cut.span.append (.cons (.jump cut.entry) actual)) warm.reconstruct
        _ = _ := by simp only [head,Execution.append_assoc,Execution.append]
    · rw [warm.date,cut.date.2,List.getLastD_cons]
    · rw [warm.recovery_preserved,cut.entry.physical_continuous,pulse.recovery_preserved]
    · have h := head.gain_balance i p
      rw [hgain] at h
      linarith
    · intro q hq
      have h := head.gain_balance i q
      rw [hother q hq] at h
      linarith
    · intro q
      simp [head,Execution.mark_append,Execution.ledger,Move.ledger,Ledger.add,
        cut.entry.mark_zero,pulse.mark_zero q,warm.mark_zero q]
    · intro hq
      have hready := head.ready_states_of_no_emissions i hs.ready hem
      exact head.ready_charge_ge_rest i (head.allStates_main_flows i .ready hready) hq

abbrev CadenceWeakWarmup {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (future : List (Delivery n)) :=
  CadenceSilentWarmup e i p [644,648,652] future

/-- Starting with the actual fresh source at 640, the inputs at 644, 648 and
652 select the three preceding silent spans. The first strong entry is reached
with gain increase 1.8, unchanged recovery and real charge in [0.1,0.3]. -/
theorem Execution.cadence_weak_warmup {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : ReadyCoordinates s i) (hq : s.x i .q = 1 / 10)
    (hz : s.x i (.z p) ≤ Real.log (3 / 10) + 1 / 100000)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (future : List (Delivery n)) (ht : s.time = 640)
    (hcalendar : e.cellDeliveries i = ⟨i,p,644⟩ :: ⟨i,p,648⟩ :: ⟨i,p,652⟩ :: future) :
    Nonempty (CadenceWeakWarmup e i p future) := by
  have hcoords : CadenceReadyCoordinates s i (cadenceStageCap 0) := by
    refine ⟨hs.ready,⟨hs.charge.1,?_⟩,hs.auxiliary⟩
    rw [hq]
    norm_num [cadenceStageCap]
  apply cadence_silent_warmup hb i p [644,648,652] 0 future e hf hv hcoords (by simp)
    (by simpa only [Nat.cast_zero,mul_zero,add_zero] using hz) hr ho ?_ ?_
  · simpa only [List.map_cons,List.map_nil,List.cons_append,List.nil_append] using hcalendar
  · rw [ht]
    norm_num [List.pairwise_cons]

end KernelR.Hybrid
