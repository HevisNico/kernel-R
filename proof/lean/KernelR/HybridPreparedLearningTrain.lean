import KernelR.HybridCellPreparedTrain
import KernelR.HybridWarmup
import KernelR.HybridResidualLatency
/-! Three actual silent learning inputs followed by a prepared learned train. -/
namespace KernelR.Hybrid

structure PreparedSilentWarmup {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (weakTimes future : List ℝ) where
  entry : Snapshot n
  head : Execution θ route s entry
  rest : Execution θ route entry u
  reconstruct : e = head.append rest
  date : entry.time = weakTimes.getLastD s.time
  prepared : PreparedSection entry i
  gain_target : entry.x i (.z p) = s.x i (.z p) + (3 / 5) * weakTimes.length
  gain_other : ∀ q, q ≠ p → entry.x i (.z q) = s.x i (.z q)
  recovery_preserved : entry.x i .b = s.x i .b
  emissions : head.emissionTimes i = []
  mark_zero : ∀ q, head.ledger.mark i q = 0
  raw_active : entry.raw i p = some entry.time
  raw_other : ∀ q, q ≠ p → entry.raw i q = none
  calendar : rest.cellDeliveries i = future.map (fun t => ⟨i,p,t⟩)
  charge_lower : 1 / 10 ≤ s.x i .q → 1 / 10 ≤ entry.x i .q

abbrev PreparedLearningWarmup {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (next1 next2 firstStrong : ℝ) (future : List ℝ) :=
  PreparedSilentWarmup e i p [next1,next2,firstStrong] future

/-- Nominal low gain selects the silent cases; the supplied list only specifies
actual incoming dates. Every other cell remains in the same execution. -/
theorem prepared_silent_warmup {n θ ε route} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) : ∀ (weakTimes : List ℝ) (stage : ℕ) (future : List ℝ)
    {s u : Snapshot n} (e : Execution θ route s u)
    (_hf : PhysicalInvariant θ s) (_hv : RawValid s) (_hs : PreparedSection s i)
    (_hstage : stage + weakTimes.length = 3)
    (_hz : Real.log (3 / 10) + (3 / 5) * stage - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + (3 / 5) * stage + 1 / 100000)
    (_hr : s.raw i p = some s.time) (_ho : ∀ q, q ≠ p → s.raw i q = none)
    (_hcalendar : e.cellDeliveries i = (weakTimes ++ future).map (fun t => ⟨i,p,t⟩))
    (_hspace : (s.time :: (weakTimes ++ future)).Pairwise (fun t v => t + 15 / 2 ≤ v)),
    Nonempty (PreparedSilentWarmup e i p weakTimes future) := by
  intro weakTimes
  induction weakTimes with
  | nil =>
    intro stage future s u e hf hv hs hstage hz hr ho hcalendar hspace
    exact ⟨⟨s,.nil _,e,rfl,rfl,hs,by simp,fun _ _ => rfl,rfl,rfl,fun _ => rfl,hr,ho,
      by simpa only [List.nil_append] using hcalendar,fun h => h⟩⟩
  | cons next weakTimes ih =>
    intro stage future s u e hf hv hs hstage hz hr ho hcalendar hspace
    have hstage' : stage ≤ 2 := by simp only [List.length_cons] at hstage; omega
    have hsilent := low_training_headroom hstage' hz.2
    have hcal : e.cellDeliveries i = ⟨i,p,next⟩ :: (weakTimes ++ future).map (fun t => ⟨i,p,t⟩) := by
      simpa only [List.cons_append,List.map_cons] using hcalendar
    obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcal
    have hgap : s.time + 15 / 2 ≤ next := (List.pairwise_cons.mp hspace).1 next (by simp)
    obtain ⟨pulse⟩ := cut.span.silent_pulse_of_invariant hb hf hv i p hs.ready_coordinates hsilent hr ho
      cut.no_arrivals_before (by rw [cut.date.1]; exact hgap)
    have hnext := cut.prepared (pulse.prepared hs)
    have hznext : Real.log (3 / 10) + (3 / 5) * (stage + 1 : ℕ) - 1 / 100000 ≤ cut.afterArrival.x i (.z p) ∧
        cut.afterArrival.x i (.z p) ≤ Real.log (3 / 10) + (3 / 5) * (stage + 1 : ℕ) + 1 / 100000 := by
      rw [cut.entry.physical_continuous,pulse.gain_target]
      push_cast
      constructor <;> linarith [hz.1,hz.2]
    have hrnext : cut.afterArrival.raw i p = some cut.afterArrival.time := cut.raw_after
    have honext : ∀ q, q ≠ p → cut.afterArrival.raw i q = none := by
      intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    have hspaceNext : (cut.afterArrival.time :: (weakTimes ++ future)).Pairwise (fun t v => t + 15 / 2 ≤ v) := by
      rw [cut.date.2]
      exact (List.pairwise_cons.mp hspace).2
    obtain ⟨warm⟩ := ih (stage + 1) future cut.rest (advanced.physical_invariant hb hf) (advanced.raw_valid hv)
      hnext (by simp only [List.length_cons] at hstage; omega) hznext hrnext honext cut.later hspaceNext
    let head := cut.span.append (.cons (.jump cut.entry) warm.head)
    have hd : (⟨i,p,next⟩ : Delivery n) ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
    have hem : head.emissionTimes i = [] := by
      simp [head,Execution.emissionTimes_append,Execution.emissionTimes_cons,Move.ledger,
        cut.entry.no_emissions_of_delivery _ hd,pulse.emissions,warm.emissions]
    refine ⟨{
      entry := warm.entry
      head := head
      rest := warm.rest
      reconstruct := ?_
      date := ?_
      prepared := warm.prepared
      gain_target := ?_
      gain_other := ?_
      recovery_preserved := ?_
      emissions := hem
      mark_zero := ?_
      raw_active := warm.raw_active
      raw_other := warm.raw_other
      calendar := warm.calendar
      charge_lower := ?_
    }⟩
    · calc
        e = cut.span.append (.cons (.jump cut.entry) cut.rest) := cut.reconstruct
        _ = cut.span.append (.cons (.jump cut.entry) (warm.head.append warm.rest)) :=
          congrArg (fun actual => cut.span.append (.cons (.jump cut.entry) actual)) warm.reconstruct
        _ = _ := by simp only [head,Execution.append_assoc,Execution.append]
    · rw [warm.date,cut.date.2,List.getLastD_cons]
    · rw [warm.gain_target,cut.entry.physical_continuous,pulse.gain_target]
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      ring
    · intro q hq
      rw [warm.gain_other q hq,cut.entry.physical_continuous,pulse.gain_other q hq]
    · rw [warm.recovery_preserved,cut.entry.physical_continuous,pulse.recovery_preserved]
    · intro q
      simp [head,Execution.mark_append,Execution.ledger,Move.ledger,Ledger.add,
        cut.entry.mark_zero,pulse.mark_zero q,warm.mark_zero q]
    · intro hq
      have hready := head.ready_states_of_no_emissions i hs.ready hem
      exact head.ready_charge_ge_rest i (head.allStates_main_flows i .ready hready) hq

/-- The three incoming dates mark the next physical arrivals, not supplied
pulse cases. Their silent behavior and resulting strong entry are proved. -/
theorem Execution.prepared_learning_warmup {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s) (i : Fin n) (p : Port)
    (hs : PreparedSection s i)
    (hz : Real.log (3 / 10) - 1 / 100000 ≤ s.x i (.z p) ∧ s.x i (.z p) ≤ Real.log (3 / 10) + 1 / 100000)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (next1 next2 firstStrong : ℝ) (tail : List ℝ)
    (hcalendar : e.cellDeliveries i = (next1 :: next2 :: firstStrong :: tail).map (fun t => ⟨i,p,t⟩))
    (hspace : (s.time :: next1 :: next2 :: firstStrong :: tail).Pairwise (fun t v => t + 15 / 2 ≤ v)) :
    Nonempty (PreparedLearningWarmup e i p next1 next2 firstStrong tail) := by
  exact prepared_silent_warmup hb i p [next1,next2,firstStrong] 0 tail e hf hv hs (by simp)
    (by simpa only [Nat.cast_zero,mul_zero,add_zero] using hz) hr ho hcalendar hspace

structure PreparedLearningTrain {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (count : ℕ) where
  emissions : (e.emissionTimes i).length = count
  error_target : e.ledger.error i p = 9 / 5
  error_other : ∀ q, q ≠ p → e.ledger.error i q = 0
  mark_zero : ∀ q, e.ledger.mark i q = 0
  gain_target : u.x i (.z p) = s.x i (.z p) + 9 / 5
  gain_other : ∀ q, q ≠ p → u.x i (.z q) = s.x i (.z q)
  recovery_preserved : u.x i .b = s.x i .b
  prepared : PreparedSection u i
  charge_rest : u.x i .q = 1 / 10
  raw_finished : ∀ q, u.raw i q = none

/-- Three silent low-gain inputs raise the actual gain into the learned band.
Every later separated input then contributes one actual emission. -/
theorem Execution.prepared_learning_train {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s) (i : Fin n) (p : Port)
    (hs : PreparedSection s i)
    (hz : Real.log (3 / 10) - 1 / 100000 ≤ s.x i (.z p) ∧ s.x i (.z p) ≤ Real.log (3 / 10) + 1 / 100000)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (next1 next2 firstStrong : ℝ) (tail : List ℝ)
    (hcalendar : e.cellDeliveries i = (next1 :: next2 :: firstStrong :: tail).map (fun t => ⟨i,p,t⟩))
    (hspace : (s.time :: next1 :: next2 :: firstStrong :: tail).Pairwise (fun t v => t + 15 / 2 ≤ v))
    (hquiet : ∀ t ∈ s.time :: next1 :: next2 :: firstStrong :: tail, t + 15 / 2 ≤ u.time) :
    Nonempty (PreparedLearningTrain e i p (tail.length + 1)) := by
  obtain ⟨warm⟩ := e.prepared_learning_warmup hb hf hv i p hs hz hr ho next1 next2 firstStrong tail hcalendar hspace
  have hgain : 9 / 5 ≤ Real.exp (warm.entry.x i (.z p)) ∧ Real.exp (warm.entry.x i (.z p)) ≤ 12 / 5 := by
    have hlog : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ warm.entry.x i (.z p) ∧
        warm.entry.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
      rw [warm.gain_target]
      norm_num only [List.length_cons,List.length_nil,Nat.cast_ofNat]
      constructor <;> linarith [hz.1,hz.2]
    have h := learned_gain_bounds hlog.1 hlog.2
    exact ⟨h.1,by linarith [h.2]⟩
  have hentrydate : warm.entry.time = firstStrong := by
    simpa only [List.getLastD_cons,List.getLastD_nil] using warm.date
  have hspace' : (warm.entry.time :: tail).Pairwise (fun t v => t + 15 / 2 ≤ v) := by
    rw [hentrydate]
    exact (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hspace).2).2).2
  have hquiet' : ∀ t ∈ warm.entry.time :: tail, t + 15 / 2 ≤ u.time := by
    rw [hentrydate]
    intro t ht
    exact hquiet t (by simp only [List.mem_cons] at ht ⊢; tauto)
  obtain ⟨train⟩ := prepared_cell_train_of_valid hb i p tail warm.rest
    (warm.head.upper_region hb hf.region) (warm.head.raw_valid hv) warm.prepared hgain
    warm.raw_active warm.raw_other warm.calendar hspace' hquiet'
  have hztarget : u.x i (.z p) = s.x i (.z p) + 9 / 5 := by
    rw [train.gain_preserved p,warm.gain_target]
    norm_num
  have hzother : ∀ q, q ≠ p → u.x i (.z q) = s.x i (.z q) := by
    intro q hq
    rw [train.gain_preserved q,warm.gain_other q hq]
  have hrecovery : u.x i .b = s.x i .b := by
    rw [train.recovery_preserved,warm.recovery_preserved]
  refine ⟨⟨?_,?_,?_,?_,hztarget,hzother,hrecovery,train.prepared,train.charge_rest,train.raw_finished⟩⟩
  · have hsplit := congrArg (fun actual => actual.emissionTimes i) warm.reconstruct
    rw [Execution.emissionTimes_append,warm.emissions,List.nil_append] at hsplit
    rw [hsplit]
    exact train.emissions
  · have h := e.gain_balance i p
    linarith
  · intro q hq
    have h := e.gain_balance i q
    rw [hzother q hq] at h
    linarith
  · intro q
    have hsplit := congrArg (fun actual => actual.ledger.mark i q) warm.reconstruct
    rw [Execution.mark_append,warm.mark_zero q,train.mark_zero q,zero_add] at hsplit
    exact hsplit

end KernelR.Hybrid
