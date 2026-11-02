import KernelR.HybridCadenceBudgetReceiverSchedule
import KernelR.HybridCadenceFirstStrongBudgetNextSource
import KernelR.HybridCadenceMarkOnlyBudgetNextSource
import KernelR.HybridCadenceSecondStrongBudgetNextSource
import KernelR.HybridCadenceMixedFullJitterNextSource

/-! Construct an autonomous physical receiver from its prepared source state
and a packet of actual incoming tokens. Every response phase and physical path
is retained. No output calendar or reaching execution is a premise. -/
namespace KernelR.Hybrid

structure LocalCadenceBudgetReceiver (θ : Fin 1 → Parameters) (s : Snapshot 1) (p : Port)
    {m L J} (packet : KernelR.Chain.Packet m L J) (terminal : ℝ) where
  jitter_bound : J ≤ 3 / 20
  tail_size : 5 ≤ L
  initial_prepared : PreparedSection s 0
  initial_charge : s.x 0 .q = 1 / 10
  initial_log_gain : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 0 (.z p) ∧
    s.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000
  firstSource : PreparedFirstSource θ s p (packet.actual 0)
    (cadenceSources packet.actual p 1 (m - 1) ++ cadenceSources packet.actual p m L)
  learnedPrefix : LearnedSourcePrefix θ firstSource.final p
    (cadenceDates packet.actual 1 (m - 1)) (cadenceSources packet.actual p m L)
  firstStrong : CadenceFirstStrongJitterNextSource θ learnedPrefix.final p (packet.actual m)
    (cadenceSources packet.actual p (m + 1) (L - 1))
  markOnly : CadenceMarkOnlyJitterNextSource θ firstStrong.final p (packet.actual (m + 1))
    (cadenceSources packet.actual p (m + 2) (L - 2))
  secondStrong : CadenceSecondStrongBudgetNextSource θ markOnly.final p (packet.actual (m + 2))
    (cadenceSources packet.actual p (m + 3) (L - 3))
  mixed : CadenceMixedFullJitterNextSource θ secondStrong.final p (packet.actual (m + 3))
    (cadenceSources packet.actual p (m + 4) (L - 4))
  high : LocalCadenceHighJitterTrain θ mixed.final p
    (cadenceDates packet.actual (m + 4) (L - 4)) terminal
  execution : Execution θ (fun _ _ => []) s high.final
  reconstruct : execution = firstSource.execution.append (learnedPrefix.execution.append
    (firstStrong.execution.append (markOnly.execution.append
      (secondStrong.execution.append (mixed.execution.append high.execution)))))

theorem local_cadence_budget_receiver_exists {θ ε m L J} (hb : PhysicalBox θ ε)
    (s : Snapshot 1) (p : Port) (packet : KernelR.Chain.Packet m L J) (terminal : ℝ)
    (hJ : J ≤ 3 / 20) (hL : 5 ≤ L)
    (hf : PhysicalInvariant θ s) (hv : RawValid s) (hs : PreparedSection s 0)
    (hq : s.x 0 .q = 1 / 10) (hr : ∀ q, s.raw 0 q = none)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x 0 (.z p) ∧
      s.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hqueue : s.pending = List.ofFn (fun i : Fin (m + L) => (⟨0,p,packet.actual i.val⟩ : Delivery 1)))
    (hfirst : s.time < packet.actual 0)
    (hterminal : packet.actual (m + L - 1) + 37 / 10 ≤ terminal) :
    Nonempty (LocalCadenceBudgetReceiver θ s p packet terminal) := by
  have hm : 1 ≤ m := packet.prefix_pos
  have hmono := packet.full_budget_strict_mono hJ
  have hQueue : s.pending = ⟨0,p,packet.actual 0⟩ ::
      (cadenceSources packet.actual p 1 (m - 1) ++ cadenceSources packet.actual p m L) := by
    have hqSources : s.pending = cadenceSources packet.actual p 0 (m + L) := by
      simpa only [cadenceSources_ofFn,zero_add] using hqueue
    exact hqSources.trans (cadenceSources_head_prefix packet.actual p m L hm)
  have hLater0 : ∀ d ∈ cadenceSources packet.actual p 1 (m - 1) ++
      cadenceSources packet.actual p m L, packet.actual 0 < d.due := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact cadenceSources_later hmono p 0 1 (m - 1) (by omega) d hd
    · exact cadenceSources_later hmono p 0 m L (by omega) d hd
  obtain ⟨first⟩ := prepared_first_source_exists hb s p (packet.actual 0)
    (cadenceSources packet.actual p 1 (m - 1) ++ cadenceSources packet.actual p m L)
    hf hv hs hq hr hQueue hfirst hLater0
  have hGain0 := cadence_three_dose_gain_bounds hz
  have hGainFirst : 9 / 5 ≤ Real.exp (first.final.x 0 (.z p)) ∧
      Real.exp (first.final.x 0 (.z p)) ≤ 11 / 5 := by
    rw [first.gains]
    exact ⟨hGain0.1,by linarith [hGain0.2]⟩
  have hPrefixSpace : LearnedPrefixSpacing first.final.time (cadenceDates packet.actual 1 (m - 1)) := by
    rw [first.date]
    exact packet_full_budget_learned_prefix_spacing packet hJ 0 (m - 1) (by omega)
  have hPrefixEnd : learnedPrefixEnd first.final.time (cadenceDates packet.actual 1 (m - 1)) =
      packet.actual (m - 1) := by
    rw [first.date]
    simpa only [zero_add] using learnedPrefixEnd_cadenceDates packet.actual 0 (m - 1)
  obtain ⟨prefixResponse⟩ := learned_source_prefix_exists hb first.final p
    (cadenceDates packet.actual 1 (m - 1)) (cadenceSources packet.actual p m L)
    first.physical first.raw_valid first.prepared first.charge hGainFirst
    (by rw [first.date]; exact first.raw_active) first.raw_other first.pending hPrefixSpace
    (by rw [hPrefixEnd]; exact cadenceSources_later hmono p (m - 1) m L (by omega))
  have hPrefixDate : prefixResponse.final.time = packet.actual (m - 1) := prefixResponse.date.trans hPrefixEnd
  have hPrefixGain (q : Port) : prefixResponse.final.x 0 (.z q) = s.x 0 (.z q) :=
    (prefixResponse.gains q).trans (first.gains q)
  have hPrefixRec : prefixResponse.final.x 0 .b = s.x 0 .b := prefixResponse.recovery.trans first.recovery
  have hPrefixCoordinates : CadenceReadyCoordinates prefixResponse.final 0 (3 / 10) :=
    ⟨prefixResponse.prepared.ready,⟨prefixResponse.prepared.charge.1,
      by rw [prefixResponse.charge]; norm_num⟩,prefixResponse.prepared.auxiliary⟩
  have hPrefixLog : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ prefixResponse.final.x 0 (.z p) ∧
      prefixResponse.final.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [hPrefixGain]
    exact hz
  have hHead0 : prefixResponse.final.pending = ⟨0,p,packet.actual m⟩ ::
      cadenceSources packet.actual p (m + 1) (L - 1) := by
    rw [prefixResponse.pending,cadenceSources_head_of_pos packet.actual p m L (by omega)]
  have hGap0 : prefixResponse.final.time + 37 / 10 ≤ packet.actual m ∧
      packet.actual m ≤ prefixResponse.final.time + 22 / 5 := by
    rw [hPrefixDate]
    constructor <;> linarith [packet.full_budget_transition_gap hJ]
  obtain ⟨strong⟩ := cadence_first_strong_full_budget_next_source_exists hb prefixResponse.final p
    (packet.actual m) (cadenceSources packet.actual p (m + 1) (L - 1))
    prefixResponse.physical prefixResponse.raw_valid hPrefixCoordinates prefixResponse.charge hPrefixLog
    (by rw [hPrefixRec]; exact hs.recovery) prefixResponse.raw_active prefixResponse.raw_other
    hHead0 hGap0 (cadenceSources_later hmono p m (m + 1) (L - 1) (by omega))
  have hHead1 : strong.final.pending = ⟨0,p,packet.actual (m + 1)⟩ ::
      cadenceSources packet.actual p (m + 2) (L - 2) := by
    rw [strong.pending,cadenceSources_head_of_pos packet.actual p (m + 1) (L - 1) (by omega)]
    congr 2
  obtain ⟨mark⟩ := cadence_mark_only_full_budget_next_source_exists hb strong.final p
    (packet.actual (m + 1)) (cadenceSources packet.actual p (m + 2) (L - 2))
    strong.physical strong.raw_valid strong.main_slow strong.charge
    (by rw [strong.recovery,hPrefixRec]; exact hs.recovery)
    (fun q => ⟨strong.auxiliary 0 q,strong.rest q⟩)
    (by rw [strong.date]; exact strong.raw_active) strong.raw_other hHead1
    (by rw [strong.date]; linarith [packet.full_budget_tail_gap hJ m (by omega)])
    (cadenceSources_later hmono p (m + 1) (m + 2) (L - 2) (by omega))
  have hMarkLog : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ mark.final.x 0 (.z p) ∧
      mark.final.x 0 (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [mark.gains,strong.gains]
    exact hPrefixLog
  have hMarkCoordinates : CadenceReadyCoordinates mark.final 0 (3 / 10) :=
    ⟨(mark.ready 0).ready,⟨(mark.ready 0).charge.1,by rw [mark.charge]; norm_num⟩,(mark.ready 0).auxiliary⟩
  have hHead2 : mark.final.pending = ⟨0,p,packet.actual (m + 2)⟩ ::
      cadenceSources packet.actual p (m + 3) (L - 3) := by
    rw [mark.pending,cadenceSources_head_of_pos packet.actual p (m + 2) (L - 2) (by omega)]
    congr 2
  obtain ⟨second⟩ := cadence_second_strong_full_budget_next_source_exists hb mark.final p
    (packet.actual (m + 2)) (cadenceSources packet.actual p (m + 3) (L - 3))
    mark.physical mark.raw_valid hMarkCoordinates mark.charge hMarkLog mark.recovery_band
    (by rw [mark.date]; exact mark.raw_active) mark.raw_other hHead2
    (by rw [mark.date]; constructor <;> linarith [packet.full_budget_tail_gap hJ (m + 1) (by omega)])
    (cadenceSources_later hmono p (m + 2) (m + 3) (L - 3) (by omega))
  have hHead3 : second.final.pending = ⟨0,p,packet.actual (m + 3)⟩ ::
      cadenceSources packet.actual p (m + 4) (L - 4) := by
    rw [second.pending,cadenceSources_head_of_pos packet.actual p (m + 3) (L - 3) (by omega)]
    congr 2
  obtain ⟨mixed⟩ := cadence_mixed_full_jitter_next_source_exists hb second.final p
    (packet.actual (m + 3)) (cadenceSources packet.actual p (m + 4) (L - 4))
    second.physical second.raw_valid second.main_slow second.charge
    (by rw [second.recovery]; exact mark.recovery_band)
    (fun q => ⟨second.auxiliary 0 q,second.rest q⟩)
    (by rw [second.gains]; exact hMarkLog)
    (by rw [second.date]; exact second.raw_active) second.raw_other hHead3
    (by rw [second.date]; linarith [packet.full_budget_tail_gap hJ (m + 2) (by omega)])
    (cadenceSources_later hmono p (m + 3) (m + 4) (L - 4) (by omega))
  have hSchedule : CadenceHighBudgetSchedule mixed.final.time
      (cadenceDates packet.actual (m + 4) (L - 4)) terminal := by
    rw [mixed.date]
    have h := packet_high_full_budget_schedule packet hJ (m + 3) (L - 4) terminal
      (by
        have hidx : m + 3 + (L - 4) = m + L - 1 := by omega
        simpa only [hidx] using hterminal)
    simpa only [show m + 3 + 1 = m + 4 by omega] using h
  obtain ⟨high⟩ := local_cadence_high_full_budget_train_exists hb mixed.final p
    (cadenceDates packet.actual (m + 4) (L - 4)) terminal mixed.physical mixed.raw_valid
    mixed.coordinates mixed.charge_lower mixed.high_gain mixed.recovery_band
    (by rw [mixed.date]; exact mixed.raw_active) mixed.raw_other mixed.pending hSchedule
  exact ⟨{
    jitter_bound := hJ, tail_size := hL, initial_prepared := hs, initial_charge := hq, initial_log_gain := hz
    firstSource := first, learnedPrefix := prefixResponse, firstStrong := strong, markOnly := mark
    secondStrong := second, mixed := mixed, high := high
    execution := first.execution.append (prefixResponse.execution.append
      (strong.execution.append (mark.execution.append (second.execution.append (mixed.execution.append high.execution)))))
    reconstruct := rfl
  }⟩

namespace LocalCadenceBudgetReceiver
variable {θ s p m L J} {packet : KernelR.Chain.Packet m L J} {terminal}
  (r : LocalCadenceBudgetReceiver θ s p packet terminal)

noncomputable abbrev final : Snapshot 1 := r.high.final

theorem date : r.final.time = terminal := r.high.date

theorem ready (j : Fin 1) : ReadyCoordinates r.final j := r.high.ready j

theorem charge : r.final.x 0 .q = 1 / 10 := r.high.charge

theorem raw_none (j : Fin 1) (q : Port) : r.final.raw j q = none := r.high.raw_none j q

theorem pending : r.final.pending = [] := r.high.pending

theorem physical : PhysicalInvariant θ r.final := r.high.physical

theorem raw_valid : RawValid r.final := r.high.raw_valid

theorem complete : CompleteThrough r.execution terminal := by
  simpa only [CompleteThrough] using r.high.complete

theorem prefix_date : r.learnedPrefix.final.time = packet.actual (m - 1) := by
  rw [r.learnedPrefix.date,r.firstSource.date]
  simpa only [zero_add] using learnedPrefixEnd_cadenceDates packet.actual 0 (m - 1)

theorem prefix_gain (q : Port) : r.learnedPrefix.final.x 0 (.z q) = s.x 0 (.z q) :=
  (r.learnedPrefix.gains q).trans (r.firstSource.gains q)

theorem high_gain_source : r.mixed.final.x 0 (.z p) = s.x 0 (.z p) + 3 / 5 := by
  rw [r.mixed.gain_target,r.secondStrong.gains,r.markOnly.gains,r.firstStrong.gains,r.prefix_gain]

theorem gain_target : r.final.x 0 (.z p) = s.x 0 (.z p) + 3 / 5 := by
  rw [r.high.gains,r.high_gain_source]

theorem gain_other (q : Port) (hq : q ≠ p) : r.final.x 0 (.z q) = s.x 0 (.z q) := by
  rw [r.high.gains,r.mixed.gain_other q hq,r.secondStrong.gains,r.markOnly.gains,
    r.firstStrong.gains,r.prefix_gain]

theorem recovery_gain : r.final.x 0 .b = s.x 0 .b + 1 / 5 := by
  rw [r.high.recovery,r.mixed.recovery_gain,r.secondStrong.recovery,r.markOnly.recovery_gain,
    r.firstStrong.recovery,r.learnedPrefix.recovery,r.firstSource.recovery]
  ring

theorem emission_count : (r.execution.emissionTimes 0).length = m + L - 2 := by
  rw [r.reconstruct]
  simp only [Execution.emissionTimes_append,List.length_append]
  have hFirst : r.firstSource.execution.emissionTimes 0 = [] := by
    simp [Execution.emissionTimes,r.firstSource.emissions]
  have hStrong : r.firstStrong.execution.emissionTimes 0 = [r.firstStrong.fire.final.time] := by
    simp [Execution.emissionTimes,r.firstStrong.emissions]
  have hMark : r.markOnly.execution.emissionTimes 0 = [] := by
    simp [Execution.emissionTimes,r.markOnly.emissions]
  have hSecond : r.secondStrong.execution.emissionTimes 0 = [r.secondStrong.fire.final.time] := by
    simp [Execution.emissionTimes,r.secondStrong.emissions]
  have hMixed : r.mixed.execution.emissionTimes 0 = [] := by
    simp [Execution.emissionTimes,r.mixed.emissions]
  rw [hFirst,hStrong,hMark,hSecond,hMixed,r.learnedPrefix.emission_count,r.high.emission_count]
  simp only [List.length_nil,List.length_cons,cadenceDates_length]
  have hm := packet.prefix_pos
  have hL := r.tail_size
  omega

theorem deliveries : r.execution.deliveries =
    List.ofFn (fun i : Fin (m + L) => (⟨0,p,packet.actual i.val⟩ : Delivery 1)) := by
  rw [r.reconstruct]
  simp only [Execution.deliveries_append,r.firstSource.deliveries,r.learnedPrefix.deliveries,
    r.firstStrong.deliveries,r.markOnly.deliveries,r.secondStrong.deliveries,r.mixed.deliveries,r.high.deliveries]
  have hSources : List.ofFn (fun i : Fin (m + L) => (⟨0,p,packet.actual i.val⟩ : Delivery 1)) =
      cadenceSources packet.actual p 0 (m + L) := by
    simp only [cadenceSources_ofFn,zero_add]
  rw [hSources,cadenceSources_head_prefix packet.actual p m L packet.prefix_pos,
    cadenceSources_four packet.actual p m L (by have hL := r.tail_size; omega : 4 ≤ L)]
  rfl

theorem first_strong_date : r.firstStrong.fire.final.time =
    packet.actual (m - 1) + restLatency (Real.exp (s.x 0 (.z p))) := by
  rw [r.firstStrong.fire.date,r.firstStrong.rest_latency]
  change r.learnedPrefix.final.time + restLatency (Real.exp (r.learnedPrefix.final.x 0 (.z p))) = _
  rw [r.prefix_date,r.prefix_gain]

theorem second_strong_date : r.secondStrong.fire.final.time =
    packet.actual (m + 1) + restLatency (Real.exp (s.x 0 (.z p))) := by
  rw [r.secondStrong.fire.date,r.secondStrong.rest_latency]
  change r.markOnly.final.time + restLatency (Real.exp (r.markOnly.final.x 0 (.z p))) = _
  rw [r.markOnly.date,r.markOnly.gains,r.firstStrong.gains,r.prefix_gain]

theorem high_first_date : r.high.first.final.time = packet.actual (m + 3) + r.high.first.latency := by
  rw [r.high.first.date]
  exact congrArg (fun t => t + r.high.first.latency) r.mixed.date

/-- Every output date is obtained from the constructed physical phases. -/
theorem calendar : r.execution.emissionTimes 0 =
    ((cadenceDates packet.actual 0 m).map (fun H => H + restLatency (Real.exp (s.x 0 (.z p))))) ++
    [packet.actual (m + 1) + restLatency (Real.exp (s.x 0 (.z p))),r.high.first.final.time] ++
    ((cadenceDates packet.actual (m + 4) (L - 4)).map
      (fun H => H + highRestLatency (Real.exp (s.x 0 (.z p) + 3 / 5)))) := by
  rw [r.reconstruct]
  simp only [Execution.emissionTimes_append]
  have hFirst : r.firstSource.execution.emissionTimes 0 = [] := by
    simp [Execution.emissionTimes,r.firstSource.emissions]
  have hStrong : r.firstStrong.execution.emissionTimes 0 = [r.firstStrong.fire.final.time] := by
    simp [Execution.emissionTimes,r.firstStrong.emissions]
  have hMark : r.markOnly.execution.emissionTimes 0 = [] := by
    simp [Execution.emissionTimes,r.markOnly.emissions]
  have hSecond : r.secondStrong.execution.emissionTimes 0 = [r.secondStrong.fire.final.time] := by
    simp [Execution.emissionTimes,r.secondStrong.emissions]
  have hMixed : r.mixed.execution.emissionTimes 0 = [] := by
    simp [Execution.emissionTimes,r.mixed.emissions]
  have hPrefix : r.learnedPrefix.execution.emissionTimes 0 =
      (cadenceDates packet.actual 0 (m - 1)).map (fun H => H + restLatency (Real.exp (s.x 0 (.z p)))) := by
    rw [r.learnedPrefix.calendar,r.firstSource.date,r.firstSource.gains]
    exact congrArg (List.map (fun H => H + restLatency (Real.exp (s.x 0 (.z p)))))
      (learnedPrefixResponses_cadenceDates packet.actual 0 (m - 1))
  rw [hFirst,hStrong,hMark,hSecond,hMixed,hPrefix,r.high.calendar,r.high_gain_source,
    r.first_strong_date,r.second_strong_date]
  rw [cadenceDates_snoc packet.actual 0 m packet.prefix_pos]
  simp only [zero_add,List.map_append,List.map_singleton,List.nil_append,List.append_assoc]
  rfl

end LocalCadenceBudgetReceiver
end KernelR.Hybrid
