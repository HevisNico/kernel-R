import KernelR.HybridLocalCadenceHighTrain
import KernelR.HybridCadenceSecondStrongResponse
import KernelR.HybridCadenceMixedNextSource

/-! An autonomous isolated C tail from the actual source660 section. It
constructs sources664/668, eighteen high responses through736, and the quiet
endpoint789.9. It makes no assertion about the surrounding network. -/
namespace KernelR.Hybrid

structure LocalCadenceTail (θ : Fin 1 → Parameters) (source : Snapshot 1) where
  source_date : source.time = 660
  second : CadenceSecondStrongResponse θ source 0 (sourceTrain 0 0 668 4 18)
  mixed : CadenceMixedResponse θ second.final 0
  source668 : CadenceMixedNextSource mixed (sourceTrain 0 0 672 4 17)
  high : LocalCadenceHighTrain θ source668.final 17 []
  high_date : high.final.time = 740
  final : Snapshot 1
  wait : Execution θ (fun _ _ => []) high.final final
  execution : Execution θ (fun _ _ => []) source final
  reconstruct : execution = second.execution.append
    (source668.execution.append (high.execution.append wait))
  date : final.time = 7899 / 10
  ready : ∀ j, ReadyCoordinates final j
  charge : final.x 0 .q = 1 / 10
  raw_none : ∀ j q, final.raw j q = none
  pending : final.pending = []
  gain_target : final.x 0 (.z 0) = source.x 0 (.z 0) + 3 / 5
  gain_other : ∀ q, q ≠ 0 → final.x 0 (.z q) = source.x 0 (.z q)
  recovery_gain : final.x 0 .b = source.x 0 .b + 1 / 10
  emission_count : (execution.emissionTimes 0).length = 19
  calendar : execution.emissionTimes 0 = second.fire.final.time :: high.execution.emissionTimes 0
  deliveries : execution.deliveries = sourceTrain 0 0 664 4 19
  wait_emissions : wait.ledger.emissions = []
  wait_deliveries : wait.deliveries = []
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  complete : CompleteThrough execution (7899 / 10)

theorem local_cadence_tail_exists {θ ε} (hb : PhysicalBox θ ε) (source : Snapshot 1)
    (hf : PhysicalInvariant θ source) (hv : RawValid source) (ht : source.time = 660)
    (hs : CadenceReadyCoordinates source 0 (3 / 10)) (hq : source.x 0 .q = 1 / 10)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ source.x 0 (.z 0) ∧
      source.x 0 (.z 0) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hB : 27999 / 100000 ≤ source.x 0 .b ∧ source.x 0 .b ≤ 28001 / 100000)
    (hr : source.raw 0 0 = some source.time) (ho : ∀ q, q ≠ 0 → source.raw 0 q = none)
    (hqueue : source.pending = sourceTrain 0 0 664 4 19) :
    Nonempty (LocalCadenceTail θ source) := by
  have hHead : source.pending = ⟨0,0,source.time + 4⟩ :: sourceTrain 0 0 668 4 18 := by
    rw [hqueue,ht,sourceTrain_succ]
    norm_num
  obtain ⟨second⟩ := cadence_second_strong_response_exists hb source 0 hf hv hs hq hz hB hr ho
    (sourceTrain 0 0 668 4 18) hHead
    (by intro d hd; obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd; rw [ht]
        change (660 : ℝ) + 4 < 668 + 4 * (k.val : ℝ)
        nlinarith [Nat.cast_nonneg (α := ℝ) k.val])
  have hSecondDate : second.final.time = 664 := by rw [second.date,ht]; norm_num
  have hSecondB : 27999 / 100000 ≤ second.final.x 0 .b ∧ second.final.x 0 .b ≤ 28001 / 100000 := by
    rw [second.recovery]
    exact hB
  have hSecondZ : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ second.final.x 0 (.z 0) ∧
      second.final.x 0 (.z 0) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [second.gains]
    exact hz
  have hFuture : ∀ d ∈ second.final.pending, second.final.time + 4 ≤ d.due := by
    intro d hd
    rw [second.pending] at hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    rw [hSecondDate]
    change (664 : ℝ) + 4 ≤ 668 + 4 * (k.val : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) k.val]
  obtain ⟨mixed⟩ := cadence_mixed_response_exists hb second.final 0 second.physical second.raw_valid
    second.main_slow second.charge hSecondB (fun q => ⟨second.auxiliary 0 q,second.rest q⟩)
    hSecondZ second.raw_active second.raw_other hFuture
  have hMixedHead : second.final.pending = ⟨0,0,second.final.time + 4⟩ :: sourceTrain 0 0 672 4 17 := by
    rw [second.pending,hSecondDate,sourceTrain_succ]
    norm_num
  obtain ⟨input⟩ := cadence_mixed_next_source_exists mixed hb second.physical second.raw_valid
    (sourceTrain 0 0 672 4 17) hMixedHead
    (by intro d hd; obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd; rw [hSecondDate]
        change (664 : ℝ) + 4 < 672 + 4 * (k.val : ℝ)
        nlinarith [Nat.cast_nonneg (α := ℝ) k.val])
  have hInputDate : input.final.time = 668 := by rw [input.date,hSecondDate]; norm_num
  have hHighQueue : input.final.pending = sourceTrain 0 0 (input.final.time + 4) 4 17 ++ [] := by
    rw [input.pending,hInputDate]
    norm_num
  obtain ⟨high⟩ := local_cadence_high_train_exists hb input.final 17 [] input.physical input.raw_valid
    input.coordinates input.charge_lower (input.high_gain_bounds hSecondZ) input.recovery_band
    input.raw_active input.raw_other hHighQueue (by simp)
  have hHighDate : high.final.time = 740 := by rw [high.date,hInputDate]; norm_num
  have hWait : high.final.time < (7899 / 10 : ℝ) := by rw [hHighDate]; norm_num
  have hMain : ∀ j, high.final.main j = .ready := fun j => (high.ready j).ready
  have hAux : ∀ j q, high.final.aux j q = .ready := fun j q => ((high.ready j).auxiliary q).1
  have hCharge : ∀ j, high.final.x j .q < 1 := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rw [high.charge]
    norm_num
  have hSensor : ∀ j q, high.final.x j (.m q) < 1 := by
    intro j q
    linarith [((high.ready j).auxiliary q).2.2]
  have hNoPending : ∀ d ∈ high.final.pending, (7899 / 10 : ℝ) < d.due := by
    rw [high.pending]
    simp
  let flow := quietFlow (θ := θ) high.final hWait hMain hAux high.raw_none hCharge hSensor
    (fun d hd => (hNoPending d hd).le)
  let wait : Execution θ (fun _ _ => []) high.final (quietAt high.final (7899 / 10)) :=
    .cons (.flow flow) (.nil _)
  let execution := second.execution.append (input.execution.append (high.execution.append wait))
  have hWaitEm : wait.ledger.emissions = [] := rfl
  have hWaitDel : wait.deliveries = [] := rfl
  have hCalendar : execution.emissionTimes 0 = second.fire.final.time :: high.execution.emissionTimes 0 := by
    change (second.execution.append (input.execution.append (high.execution.append wait))).emissionTimes 0 = _
    rw [Execution.emissionTimes_append,Execution.emissionTimes_append,Execution.emissionTimes_append]
    have hSecond : second.execution.emissionTimes 0 = [second.fire.final.time] := by
      simp [Execution.emissionTimes,second.emissions]
    have hInput : input.execution.emissionTimes 0 = [] := by simp [Execution.emissionTimes,input.emissions]
    have hQuiet : wait.emissionTimes 0 = [] := by simp [Execution.emissionTimes,hWaitEm]
    rw [hSecond,hInput,hQuiet,List.append_nil,List.nil_append]
    rfl
  have hPartition : sourceTrain (0 : Fin 1) 0 664 4 19 =
      [⟨0,0,664⟩,⟨0,0,668⟩] ++ sourceTrain 0 0 672 4 17 := by
    rw [sourceTrain_succ,show (664 : ℝ) + 4 = 668 by norm_num,
      sourceTrain_succ,show (668 : ℝ) + 4 = 672 by norm_num]
    rfl
  obtain ⟨_,hc⟩ := quiet_complete_exists (θ := θ) (route := fun _ _ => []) high.final hWait
    hMain hAux high.raw_none hCharge hSensor hNoPending
  refine ⟨{
    source_date := ht, second := second, mixed := mixed, source668 := input, high := high, high_date := hHighDate
    final := quietAt high.final (7899 / 10), wait := wait, execution := execution, reconstruct := rfl
    date := rfl, ready := fun j => quietAt_ready_coordinates high.final j (high.ready j) hWait.le
    charge := ?_, raw_none := high.raw_none, pending := high.pending
    gain_target := ?_, gain_other := ?_, recovery_gain := ?_
    emission_count := by rw [hCalendar,List.length_cons,high.emission_count]
    calendar := hCalendar, deliveries := ?_, wait_emissions := hWaitEm, wait_deliveries := hWaitDel
    physical := wait.physical_invariant hb high.physical, raw_valid := wait.raw_valid high.raw_valid
    complete := by simpa only [CompleteThrough] using hc
  }⟩
  · change relax (1 / 2) (1 / 10) (high.final.x 0 .q) high.final.time (7899 / 10) = 1 / 10
    rw [high.charge]
    simp [relax]
  · change high.final.x 0 (.z 0) = _
    rw [high.gains,input.gain_target,second.gains]
  · intro q hq
    change high.final.x 0 (.z q) = _
    rw [high.gains,input.gain_other q hq,second.gains]
  · change high.final.x 0 .b = _
    rw [high.recovery,input.recovery_gain,second.recovery]
  · simp only [execution,Execution.deliveries_append,second.deliveries,input.deliveries,high.deliveries,
      hWaitDel,List.append_nil,ht,hSecondDate,hInputDate,
      show (660 : ℝ) + 4 = 664 by norm_num,show (664 : ℝ) + 4 = 668 by norm_num,
      show (668 : ℝ) + 4 = 672 by norm_num]
    exact hPartition.symm

end KernelR.Hybrid
