import KernelR.HybridLocalCadenceBudgetReceiver
import KernelR.HybridCadencePacketRelay

/-! The actual receiver calendar closes under the packet transform. All
latencies below are extracted from the constructed response paths. -/
namespace KernelR.Hybrid
namespace LocalCadenceBudgetReceiver
variable {θ s p m L J} {packet : KernelR.Chain.Packet m L J} {terminal}
  (r : LocalCadenceBudgetReceiver θ s p packet terminal)

noncomputable def lowLatency (_r : LocalCadenceBudgetReceiver θ s p packet terminal) : ℝ := restLatency (Real.exp (s.x 0 (.z p)))
noncomputable def firstHighLatency : ℝ := r.high.first.latency
noncomputable def restHighLatency (_r : LocalCadenceBudgetReceiver θ s p packet terminal) : ℝ := highRestLatency (Real.exp (s.x 0 (.z p) + 3 / 5))

theorem low_latency_bounds : 65 / 100 ≤ r.lowLatency ∧ r.lowLatency ≤ 66 / 100 := by
  have h := restLatency_three_doses_bounds r.initial_log_gain.1 r.initial_log_gain.2
  dsimp [lowLatency]
  constructor <;> linarith [h.1,h.2]

theorem first_high_latency_bounds : 4 / 25 ≤ r.firstHighLatency ∧ r.firstHighLatency ≤ 13 / 50 :=
  ⟨r.high.first.early.le,r.high.first.deadline.le⟩

theorem high_latency_order : r.firstHighLatency ≤ r.restHighLatency := by
  have h := r.high.first_latency_le_rest
  rw [r.high_gain_source] at h
  exact h

theorem rest_high_latency_bounds : 4 / 25 ≤ r.restHighLatency ∧ r.restHighLatency ≤ 13 / 50 := by
  have hupper := highRestLatency_lt_twenty_six r.mixed.high_gain
  rw [r.high_gain_source] at hupper
  exact ⟨r.first_high_latency_bounds.1.trans r.high_latency_order,hupper.le⟩

noncomputable def outputPacket : KernelR.Chain.Packet (m + 2) (L - 4) J :=
  packet.relayCadence r.tail_size r.lowLatency r.firstHighLatency r.restHighLatency
    r.low_latency_bounds r.first_high_latency_bounds r.rest_high_latency_bounds r.high_latency_order

theorem output_packet_prefix : cadenceDates r.outputPacket.actual 0 m =
    (cadenceDates packet.actual 0 m).map (fun H => H + r.lowLatency) := by
  simp only [cadenceDates,List.map_ofFn,Function.comp_def,zero_add]
  apply congrArg List.ofFn
  funext k
  exact KernelR.Chain.relay_cadence_actual_prefix packet r.tail_size r.lowLatency r.firstHighLatency
    r.restHighLatency r.low_latency_bounds r.first_high_latency_bounds r.rest_high_latency_bounds
    r.high_latency_order k.isLt

theorem output_packet_special : cadenceDates r.outputPacket.actual m 2 =
    [packet.actual (m + 1) + r.lowLatency,r.high.first.final.time] := by
  have hsecond := KernelR.Chain.relay_cadence_actual_second packet r.tail_size r.lowLatency r.firstHighLatency
    r.restHighLatency r.low_latency_bounds r.first_high_latency_bounds r.rest_high_latency_bounds
    r.high_latency_order
  have hhigh := KernelR.Chain.relay_cadence_actual_first_high packet r.tail_size r.lowLatency r.firstHighLatency
    r.restHighLatency r.low_latency_bounds r.first_high_latency_bounds r.rest_high_latency_bounds
    r.high_latency_order
  change r.outputPacket.actual m = packet.actual (m + 1) + r.lowLatency at hsecond
  change r.outputPacket.actual (m + 1) = packet.actual (m + 3) + r.high.first.latency at hhigh
  norm_num only [cadenceDates,List.ofFn_succ,Fin.val_zero,Fin.val_succ,List.ofFn_zero,add_zero,Nat.zero_add]
  rw [hsecond,hhigh,r.high_first_date]

theorem output_packet_tail : cadenceDates r.outputPacket.actual (m + 2) (L - 4) =
    (cadenceDates packet.actual (m + 4) (L - 4)).map (fun H => H + r.restHighLatency) := by
  simp only [cadenceDates,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext k
  have h := KernelR.Chain.relay_cadence_actual_tail packet r.tail_size r.lowLatency r.firstHighLatency
    r.restHighLatency r.low_latency_bounds r.first_high_latency_bounds r.rest_high_latency_bounds
    r.high_latency_order (i := m + 2 + k.val) (by omega)
  change r.outputPacket.actual (m + 2 + k.val) = packet.actual (m + 2 + k.val + 2) + r.restHighLatency at h
  simpa only [show m + 2 + k.val + 2 = m + 4 + k.val by omega] using h

/-- The complete physical output list, with its unchanged phase errors. -/
theorem output_packet_calendar : r.execution.emissionTimes 0 =
    List.ofFn (fun i : Fin ((m + 2) + (L - 4)) => r.outputPacket.actual i.val) := by
  have h : cadenceDates r.outputPacket.actual 0 ((m + 2) + (L - 4)) =
      ((cadenceDates packet.actual 0 m).map (fun H => H + r.lowLatency)) ++
      [packet.actual (m + 1) + r.lowLatency,r.high.first.final.time] ++
      ((cadenceDates packet.actual (m + 4) (L - 4)).map (fun H => H + r.restHighLatency)) := by
    rw [cadenceDates_add,cadenceDates_add]
    simp only [zero_add]
    rw [r.output_packet_prefix,r.output_packet_special,r.output_packet_tail]
  rw [r.calendar]
  simpa only [cadenceDates,zero_add,lowLatency,restHighLatency] using h.symm

end LocalCadenceBudgetReceiver
end KernelR.Hybrid
