import KernelR.HybridBirthInput
import KernelR.HybridBirthPulseGain
import KernelR.HybridNewbornWeakCycle
import KernelR.HybridLowRecoverySlowSpan
import KernelR.HybridProtectedInputShortCycle
import KernelR.HybridLearnedSourcePrefix

/-! Direct preparation of a leaf's nominal fast port from its own READY
birth. The sixteen actual port1 sources are consumed, with all future source
occurrences retained. No teacher, reaching execution, reset or port permutation
is supplied. -/
namespace KernelR.Hybrid

noncomputable def leafPreparationArrived (s : Snapshot 1) (later : List (Delivery 1)) : Snapshot 1 :=
  {setRaw s 0 1 (some s.time) with pending := later}

noncomputable def leafPreparationDates : List ℝ :=
  List.ofFn (fun k : Fin 12 => (32 : ℝ) + 8 * k.val)

private theorem leaf_preparation_future (future : List (Delivery 1))
    (hf : ∀ d ∈ future, (160 : ℝ) ≤ d.due) (start : ℝ) (count : ℕ) (T : ℝ)
    (hs : T ≤ start) (ht : T ≤ 160) :
    ∀ d ∈ sourceTrain (0 : Fin 1) 1 start 8 count ++ future, T ≤ d.due := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change T ≤ start + 8 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  · exact ht.trans (hf d hd)

private theorem leaf_preparation_dates_queue :
    leafPreparationDates.map (fun H => (⟨0,1,H⟩ : Delivery 1)) = sourceTrain 0 1 32 8 12 := by
  simp only [leafPreparationDates,sourceTrain,List.map_ofFn,Function.comp_def]

private theorem leaf_preparation_dates_spacing : LearnedPrefixSpacing 24 leafPreparationDates := by
  norm_num [leafPreparationDates,LearnedPrefixSpacing,List.ofFn_succ]

private theorem leaf_preparation_dates_end : learnedPrefixEnd 24 leafPreparationDates = 120 := by
  norm_num [leafPreparationDates,learnedPrefixEnd,List.ofFn_succ]

structure FiniteChainLeafPreparation (θ : Fin 1 → Parameters) (born : Snapshot 1)
    (future : List (Delivery 1)) where
  firstArrival : Jump (fun _ _ => []) born
    (leafPreparationArrived born (sourceTrain 0 1 8 8 15 ++ future))
  weak : WeakInputCycle θ (fun _ _ => [])
    (leafPreparationArrived born (sourceTrain 0 1 8 8 15 ++ future)) 0 1
  source8 : QuietSourceArrival θ (fun _ _ => []) weak.final ⟨0,1,8⟩
    (sourceTrain 0 1 16 8 14 ++ future)
  fire : FirstLearnedFire θ (fun _ _ => []) source8.final 0 1
  fast : MidLearnedFastEnd fire
  slow16 : LowRecoverySlowSpan fast 16
  arrival16 : Jump (fun _ _ => []) slow16.final
    (leafPreparationArrived slow16.final (sourceTrain 0 1 24 8 13 ++ future))
  protectedCycle : ProtectedInputShortCycle θ (fun _ _ => [])
    (leafPreparationArrived slow16.final (sourceTrain 0 1 24 8 13 ++ future)) 1
  source24 : QuietSourceArrival θ (fun _ _ => []) protectedCycle.final ⟨0,1,24⟩
    (sourceTrain 0 1 32 8 12 ++ future)
  learnedPrefix : LearnedSourcePrefix θ source24.final 1 leafPreparationDates future
  lastCycle : ShortLearnedCycle θ learnedPrefix.final 1
  waitFlow : Flow θ lastCycle.returned.final (quietAt lastCycle.returned.final (1599/10))
  execution : Execution θ (fun _ _ => []) born (quietAt lastCycle.returned.final (1599/10))
  reconstruct : execution =
    ((Execution.cons (.jump firstArrival) weak.execution).append
      (source8.execution.append ((fire.execution.append fast.execution).append
        (slow16.execution.append (Execution.cons (.jump arrival16)
          (protectedCycle.execution.append source24.execution)))))).append
      (learnedPrefix.execution.append
        (lastCycle.execution.append (Execution.cons (.flow waitFlow) (Execution.nil _))))
  source120_date : learnedPrefix.final.time = 120
  returned_date : lastCycle.returned.final.time = 1269/10
  prepared : PreparedSection (quietAt lastCycle.returned.final (1599/10)) 0
  charge : (quietAt lastCycle.returned.final (1599/10)).x 0 .q = 1/10
  raw_none : ∀ j p, (quietAt lastCycle.returned.final (1599/10)).raw j p = none
  pending : (quietAt lastCycle.returned.final (1599/10)).pending = future
  gain_target : (quietAt lastCycle.returned.final (1599/10)).x 0 (.z 1) = born.x 0 (.z 1) + 3/5
  gain_other : ∀ p, p ≠ 1 → (quietAt lastCycle.returned.final (1599/10)).x 0 (.z p) = born.x 0 (.z p)
  recovery : (quietAt lastCycle.returned.final (1599/10)).x 0 .b = born.x 0 .b + 1/10
  calendar : execution.emissionTimes 0 =
    [fire.final.time] ++ learnedPrefix.execution.emissionTimes 0 ++ [lastCycle.fire.final.time]
  emission_count : (execution.emissionTimes 0).length = 14
  deliveries : execution.deliveries = sourceTrain 0 1 0 8 16
  physical : PhysicalInvariant θ (quietAt lastCycle.returned.final (1599/10))
  raw_valid : RawValid (quietAt lastCycle.returned.final (1599/10))
  complete : CompleteThrough execution (1599/10)

/-- The full birth family, physical box, sixteen direct sources and actual
future queue suffice. Every subsequent physical phase is constructed. -/
theorem finite_chain_leaf_preparation_exists {θ ε born}
    (hborn : @BirthState 1 born) (hb : PhysicalBox θ ε)
    (ha : ∀ p, born.aux 0 p = .ready) (future : List (Delivery 1))
    (hqueue : born.pending = sourceTrain 0 1 0 8 16 ++ future)
    (hfuture : ∀ d ∈ future, (160 : ℝ) ≤ d.due) :
    Nonempty (FiniteChainLeafPreparation θ born future) := by
  let seed := leafPreparationArrived born (sourceTrain 0 1 8 8 15 ++ future)
  have hQueue0 : born.pending = ⟨0,1,0⟩ :: (sourceTrain 0 1 8 8 15 ++ future) := by
    rw [hqueue,sourceTrain_succ]
    norm_num
  let firstArrival : Jump (fun _ _ => []) born seed :=
    .arrive born ⟨0,1,0⟩ [] _ hQueue0 hborn.1.symm (hborn.2.1 0 1)
  let firstTrace : Execution θ (fun _ _ => []) born seed := Execution.cons (.jump firstArrival) (Execution.nil _)
  have hfSeed := firstTrace.physical_invariant hb (hborn.physical_invariant hb)
  have hvSeed := firstTrace.raw_valid hborn.raw_valid
  have hsSeed : ∀ j, ReadyCoordinates seed j := by
    intro j
    have h := hborn.ready_coordinates j (by intro p; have hj : j=0 := Subsingleton.elim _ _; subst j; exact ha p)
    exact ⟨h.ready,h.charge,h.auxiliary⟩
  have hNarrow : seed.x 0 .q ≤ 10001/100000 := by
    change born.x 0 .q ≤ _
    linarith [(hborn.2.2 0).2.1.2]
  have hGainSeed : Real.exp (seed.x 0 (.z 1)) ≤ 4/3 := hborn.nominal_pulse_gain_upper 0 1
  have hzBorn := ((hborn.2.2 0).2.2.2.2 (1 : Port)).1
  norm_num [nominalGain] at hzBorn
  have hzSeed : seed.x 0 (.z 1) ≤ Real.log (6/5) + 1/1000 := by
    change born.x 0 (.z 1) ≤ _
    linarith [hzBorn.2]
  have hrSeed : seed.raw 0 1 = some seed.time := by simp [seed,leafPreparationArrived,setRaw]
  have hoSeed : ∀ j p, j ≠ (0 : Fin 1) ∨ p ≠ (1 : Port) → seed.raw j p = none := by
    intro j p hp
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    simp only [ne_eq,not_true_eq_false,false_or] at hp
    simp [seed,leafPreparationArrived,setRaw,hp,hborn.2.1]
  obtain ⟨weak⟩ := narrow_weak_input_cycle_exists (route:=fun _ _=>[]) seed hb hfSeed hvSeed 0 1 hsSeed hNarrow hGainSeed
    hzSeed hrSeed hoSeed (by
      intro d hd
      have h := leaf_preparation_future future hfuture 8 15 8 (by norm_num) (by norm_num) d hd
      change born.time + 31/4 ≤ d.due
      rw [hborn.1]
      linarith)
  have hWeakDate : weak.final.time = 15/2 := by rw [weak.date]; change born.time + 15/2 = _; rw [hborn.1]; norm_num
  have hWeakQueue : weak.final.pending = ⟨0,1,8⟩ :: (sourceTrain 0 1 16 8 14 ++ future) := by
    rw [weak.pending]
    change sourceTrain 0 1 8 8 15 ++ future = _
    rw [sourceTrain_succ]
    norm_num
  obtain ⟨source8⟩ := quiet_source_arrival_exists (route:=fun _ _=>[]) hb weak.final ⟨0,1,8⟩
    (sourceTrain 0 1 16 8 14 ++ future) weak.physical weak.raw_valid
    (by intro j; have hj : j=0 := Subsingleton.elim _ _; subst j; exact weak.pulse.coordinates)
    (by intro j p; have hj : j=0 := Subsingleton.elim _ _; subst j; exact weak.pulse.raw_finished p)
    (by rw [hWeakDate]; norm_num) hWeakQueue
    (leaf_preparation_future future hfuture 16 14 8 (by norm_num) (by norm_num))
  have hGain8 (p : Port) : source8.final.x 0 (.z p) = weak.final.x 0 (.z p) := source8.gain_preserved 0 p
  have hz8 : source8.final.x 0 (.z 1) = born.x 0 (.z 1) + 3/5 := by
    rw [hGain8,weak.pulse.gain_target]
    rfl
  have hG8 : 9/5 ≤ Real.exp (source8.final.x 0 (.z 1)) ∧ Real.exp (source8.final.x 0 (.z 1)) ≤ 11/5 := by
    apply fast_learned_gain_sharp_bounds
    · rw [hz8]; linarith [hzBorn.1]
    · rw [hz8]; linarith [hzBorn.2]
  have hp8 : ∀ d ∈ source8.final.pending, source8.final.time + 31/4 ≤ d.due := by
    intro d hd
    rw [source8.pending] at hd
    have hh := leaf_preparation_future future hfuture 16 14 16 (by norm_num) (by norm_num) d hd
    rw [source8.date]
    change (8 : ℝ)+31/4 ≤ d.due
    linarith
  obtain ⟨fire⟩ := first_mid_learned_fire_exists (route:=fun _ _=>[]) source8.final hb
    source8.physical source8.raw_valid 0 1 source8.ready hG8 source8.raw_active source8.raw_other hp8
  obtain ⟨fast⟩ := fire.mid_learned_fast_end_exists hb (source8.ready 0) hG8.2
    (fun p hp => source8.raw_other 0 p (Or.inr hp)) hp8
  have hB8 : 7999/100000 ≤ source8.final.x 0 .b ∧ source8.final.x 0 .b ≤ 8001/100000 := by
    rw [source8.recovery_preserved,weak.pulse.recovery_preserved]
    change 7999/100000 ≤ born.x 0 .b ∧ born.x 0 .b ≤ 8001/100000
    have h := (hborn.2.2 0).2.2.1
    constructor <;> linarith [h.1,h.2]
  have hFastStart : fast.final.time ≤ (16 : ℝ) := by
    rw [fast.date,fire.date,source8.date]
    change (8 : ℝ)+fire.latency+1 ≤ 16
    linarith [fire.deadline]
  have hFastQueue : fast.final.pending = sourceTrain 0 1 16 8 14 ++ future := by
    rw [fast.pending,fire.pending,source8.pending,List.append_nil]
  obtain ⟨slow⟩ := fire.low_recovery_slow_span_exists hb fast (source8.ready 0) hG8.2 hB8 16 hFastStart
    (by rw [source8.date]; norm_num)
    (by rw [hFastQueue]; exact leaf_preparation_future future hfuture 16 14 16 (by norm_num) (by norm_num))
  have hSlowQueue : slow.final.pending = ⟨0,1,16⟩ :: (sourceTrain 0 1 24 8 13 ++ future) := by
    rw [slow.pending,hFastQueue,sourceTrain_succ]
    norm_num
  let at16 := leafPreparationArrived slow.final (sourceTrain 0 1 24 8 13 ++ future)
  let arrival16 : Jump (fun _ _=>[]) slow.final at16 :=
    .arrive slow.final ⟨0,1,16⟩ [] _ hSlowQueue slow.date.symm (slow.raw_none 0 1)
  let arrive16Trace : Execution θ (fun _ _=>[]) slow.final at16 := Execution.cons (.jump arrival16) (Execution.nil _)
  have hAt16Date : at16.time = 16 := slow.date
  have hAt16B : 7999/100000 ≤ at16.x 0 .b ∧ at16.x 0 .b ≤ 8001/100000 := by
    change 7999/100000 ≤ slow.final.x 0 .b ∧ slow.final.x 0 .b ≤ 8001/100000
    rw [slow.recovery,fast.recovery,fire.recovery_preserved]
    exact hB8
  have hAt16Charge : 7/50 ≤ at16.x 0 .q ∧ at16.x 0 .q ≤ 4/25 := by
    have h := slow.near_charge (by rw [source8.date]; norm_num)
    exact ⟨h.1.le,h.2.le⟩
  have hr16 : at16.raw 0 1 = some at16.time := by simp [at16,leafPreparationArrived,setRaw]
  have ho16 : ∀ p, p ≠ 1 → at16.raw 0 p = none := by
    intro p hp
    simp [at16,leafPreparationArrived,setRaw,hp,slow.raw_none]
  obtain ⟨protect⟩ := protected_input_short_cycle_exists (route:=fun _ _=>[]) hb at16 1
    (arrive16Trace.physical_invariant hb slow.physical) (arrive16Trace.raw_valid slow.raw_valid)
    slow.main_slow hAt16Charge hAt16B (fun p => ⟨slow.auxiliary 0 p,slow.rest p⟩) hr16 ho16
    (by
      intro d hd
      have h := leaf_preparation_future future hfuture 24 13 24 (by norm_num) (by norm_num) d hd
      rw [hAt16Date]
      linarith)
  have hProtectedDate : protect.final.time = 45/2 := by rw [protect.date,hAt16Date]; norm_num
  have hProtectedQueue : protect.final.pending = ⟨0,1,24⟩ :: (sourceTrain 0 1 32 8 12 ++ future) := by
    rw [protect.pending]
    change sourceTrain 0 1 24 8 13 ++ future = _
    rw [sourceTrain_succ]
    norm_num
  obtain ⟨source24⟩ := quiet_source_arrival_exists (route:=fun _ _=>[]) hb protect.final ⟨0,1,24⟩
    (sourceTrain 0 1 32 8 12 ++ future) protect.physical protect.raw_valid protect.ready
    protect.raw_none (by rw [hProtectedDate]; norm_num) hProtectedQueue
    (leaf_preparation_future future hfuture 32 12 24 (by norm_num) (by norm_num))
  have h24Prepared : PreparedSection source24.final 0 := by
    refine ⟨(source24.ready 0).ready,(source24.ready 0).charge,?_,(source24.ready 0).auxiliary⟩
    rw [source24.recovery_preserved]
    exact (protect.prepared 0).recovery
  have h24Charge : source24.final.x 0 .q = 1/10 := by
    rw [congrFun (congrFun source24.values 0) .q]
    change relax (1/2) (1/10) (protect.final.x 0 .q) protect.final.time 24 = 1/10
    rw [protect.charge]
    simp [relax]
  have h24Gains (p : Port) : source24.final.x 0 (.z p) = source8.final.x 0 (.z p) := by
    rw [source24.gain_preserved,protect.gains]
    change slow.final.x 0 (.z p) = _
    rw [slow.gains,fast.gains,fire.gain_preserved]
  have h24Recovery : source24.final.x 0 .b = born.x 0 .b + 1/10 := by
    rw [source24.recovery_preserved,protect.recovery_gain]
    change slow.final.x 0 .b + 1/10 = _
    rw [slow.recovery,fast.recovery,fire.recovery_preserved,source8.recovery_preserved,
      weak.pulse.recovery_preserved]
    rfl
  have h24Gain : 9/5 ≤ Real.exp (source24.final.x 0 (.z 1)) ∧ Real.exp (source24.final.x 0 (.z 1)) ≤ 11/5 := by
    rw [h24Gains]
    exact hG8
  obtain ⟨learned⟩ := learned_source_prefix_exists hb source24.final 1 leafPreparationDates future
    source24.physical source24.raw_valid h24Prepared h24Charge h24Gain source24.raw_active
    (fun p hp => source24.raw_other 0 p (Or.inr hp))
    (by rw [source24.pending,leaf_preparation_dates_queue])
    (by rw [source24.date]; exact leaf_preparation_dates_spacing)
    (by
      intro d hd
      rw [source24.date,leaf_preparation_dates_end]
      linarith [hfuture d hd])
  have hPrefixDate : learned.final.time = 120 := by
    rw [learned.date,source24.date,leaf_preparation_dates_end]
  have hPrefixGain : 9/5 ≤ Real.exp (learned.final.x 0 (.z 1)) ∧ Real.exp (learned.final.x 0 (.z 1)) ≤ 11/5 := by
    rw [learned.gains]
    exact h24Gain
  obtain ⟨last⟩ := short_learned_cycle_exists hb learned.final 1 learned.physical learned.raw_valid learned.prepared
    hPrefixGain learned.raw_active learned.raw_other (by
      intro d hd
      rw [learned.pending] at hd
      rw [hPrefixDate]
      linarith [hfuture d hd])
  have hLastDate : last.returned.final.time = 1269/10 := by rw [last.date,hPrefixDate]; norm_num
  have hWait : last.returned.final.time < (1599/10 : ℝ) := by rw [hLastDate]; norm_num
  have hLastPending : last.returned.final.pending = future := last.pending.trans learned.pending
  have hFinalFuture : ∀ d ∈ last.returned.final.pending, (1599/10 : ℝ) < d.due := by
    intro d hd
    rw [hLastPending] at hd
    linarith [hfuture d hd]
  let waitFlow : Flow θ last.returned.final (quietAt last.returned.final (1599/10)) := quietFlow last.returned.final hWait
    (fun j => (last.ready j).ready) (fun j p => ((last.ready j).auxiliary p).1) last.raw_none
    (fun j => by linarith [(last.ready j).charge.2])
    (fun j p => by linarith [((last.ready j).auxiliary p).2.2]) (fun d hd => (hFinalFuture d hd).le)
  let wait : Execution θ (fun _ _=>[]) last.returned.final (quietAt last.returned.final (1599/10)) := Execution.cons (.flow waitFlow) (Execution.nil _)
  let early : Execution θ (fun _ _=>[]) born source24.final :=
    (Execution.cons (.jump firstArrival) weak.execution).append
      (source8.execution.append ((fire.execution.append fast.execution).append
        (slow.execution.append (Execution.cons (.jump arrival16) (protect.execution.append source24.execution)))))
  let execution : Execution θ (fun _ _=>[]) born (quietAt last.returned.final (1599/10)) :=
    early.append (learned.execution.append (last.execution.append wait))
  have he0 : firstArrival.ledger.emissions = [] := rfl
  have hd0 : firstArrival.deliveries = [⟨0,1,0⟩] := rfl
  have he16 : arrival16.ledger.emissions = [] := rfl
  have hd16 : arrival16.deliveries = [⟨0,1,16⟩] := rfl
  have hCalendar : execution.emissionTimes 0 =
      [fire.final.time] ++ learned.execution.emissionTimes 0 ++ [last.fire.final.time] := by
    simp only [execution,early,wait,Execution.emissionTimes,
      Execution.emissions_append,Execution.ledger,Move.ledger,he0,he16,Ledger.zero,Ledger.add,
      List.filter_append,List.map_append,weak.emissions,source8.emissions,fire.emissions,
      fast.emissions,slow.emissions,protect.emissions,source24.emissions,last.emissions,
      Flow.ledger,List.nil_append,List.append_nil]
    simp [fire.date]
  have hCount : (execution.emissionTimes 0).length = 14 := by
    rw [hCalendar,List.length_append,List.length_append,learned.emission_count]
    norm_num [leafPreparationDates]
  have hDeliveries : execution.deliveries = sourceTrain 0 1 0 8 16 := by
    simp only [execution,early,wait,Execution.deliveries_append,Execution.deliveries,Move.deliveries,
      hd0,hd16,weak.deliveries,source8.deliveries,fire.deliveries,fast.deliveries,
      slow.deliveries,protect.deliveries,source24.deliveries,learned.deliveries,last.deliveries,
      List.nil_append,List.append_nil,leaf_preparation_dates_queue]
    norm_num [sourceTrain,List.ofFn_succ]
  have hFinalGains (p : Port) : (quietAt last.returned.final (1599/10)).x 0 (.z p) = weak.final.x 0 (.z p) := by
    change last.returned.final.x 0 (.z p) = _
    rw [last.gains,learned.gains,h24Gains,hGain8]
  have hFinalRecovery : (quietAt last.returned.final (1599/10)).x 0 .b = born.x 0 .b + 1/10 := by
    change last.returned.final.x 0 .b = _
    rw [last.recovery,learned.recovery,h24Recovery]
  have hFinalPrepared : PreparedSection (quietAt last.returned.final (1599/10)) 0 := by
    have hReady := quietAt_ready_coordinates last.returned.final 0 (last.ready 0) hWait.le
    exact ⟨hReady.ready,hReady.charge,(last.prepared 0).recovery,hReady.auxiliary⟩
  obtain ⟨_,hc⟩ := quiet_complete_exists (θ:=θ) (route:=fun _ _=>[]) last.returned.final hWait
    (fun j => (last.ready j).ready) (fun j p => ((last.ready j).auxiliary p).1) last.raw_none
    (fun j => by linarith [(last.ready j).charge.2])
    (fun j p => by linarith [((last.ready j).auxiliary p).2.2]) hFinalFuture
  refine ⟨{
    firstArrival:=firstArrival,weak:=weak,source8:=source8,fire:=fire,fast:=fast,slow16:=slow
    arrival16:=arrival16,protectedCycle:=protect,source24:=source24,learnedPrefix:=learned,lastCycle:=last
    waitFlow:=waitFlow,execution:=execution,reconstruct:=rfl,source120_date:=hPrefixDate,returned_date:=hLastDate
    prepared:=hFinalPrepared,charge:=?_,raw_none:=last.raw_none,pending:=hLastPending
    gain_target:=?_,gain_other:=?_,recovery:=hFinalRecovery,calendar:=hCalendar,emission_count:=hCount
    deliveries:=hDeliveries,physical:=execution.physical_invariant hb (hborn.physical_invariant hb)
    raw_valid:=execution.raw_valid hborn.raw_valid,complete:=?_
  }⟩
  · change relax (1/2) (1/10) (last.returned.final.x 0 .q) last.returned.final.time (1599/10) = 1/10
    rw [last.charge]
    simp [relax]
  · rw [hFinalGains,weak.pulse.gain_target]
    rfl
  · intro p hp
    rw [hFinalGains,weak.pulse.gain_other p hp]
    rfl
  · simpa only [CompleteThrough] using hc

namespace FiniteChainLeafPreparation
variable {θ born future} (c : FiniteChainLeafPreparation θ born future)

noncomputable abbrev final : Snapshot 1 := quietAt c.lastCycle.returned.final (1599/10)

theorem date : c.final.time = 1599/10 := rfl

theorem gain_port0 : c.final.x 0 (.z 0) = born.x 0 (.z 0) := c.gain_other 0 (by decide)

end FiniteChainLeafPreparation
end KernelR.Hybrid
