import KernelR.HybridConstructedCadenceLeafK
import KernelR.HybridFiniteCausalChain
import KernelR.HybridQuietLeftWireArrival
import KernelR.HybridCadenceChainEnvelope

/-! Time bounds of the actual finite leaf packet, independent of its chosen
terminal quiet date. Every output is attached to an original source index
and its genuine response latency. The physical leaf also supplies the base
one-cell witness required by finite causal weaving. -/
namespace KernelR.Hybrid
namespace ConstructedCadenceLeafK
variable {θ s p start K terminal} (full : ConstructedCadenceLeafK θ s p start K terminal)

theorem rest_latency_lower : (4 / 25 : ℝ) < full.restLatency := by
  have h := full.tail.high_first_latency_le_rest
  change full.tail.high.first.latency ≤ full.restLatency at h
  exact full.tail.high.first.early.trans_le h

/-- Prefix source indices are 3,5,7. Later outputs use the original indices
8,9,...,K-1, all with this cell's own proved exact-rest latency. -/
theorem packet_emission_origin (i : Fin (3 + (K - 8))) :
    ∃ (source : Fin K) (latency : ℝ),
      full.packet.actual i.val = start + 4 * (source.val : ℝ) + latency ∧
      4 / 25 < latency ∧ latency < 9 / 10 := by
  have hK := full.budget
  by_cases h0 : i.val = 0
  · rw [h0]
    refine ⟨⟨3,by omega⟩,full.firstMark.fire.latency,?_,?_,?_⟩
    · rw [full.packet_actual_zero]
      change full.firstMark.fire.final.time = start + 4 * (3 : ℝ) + full.firstMark.fire.latency
      linarith [full.firstMark.fire.date,full.warmup_date]
    · linarith [full.first_window.1,full.firstMark.fire.date,full.warmup_date]
    · linarith [full.first_window.2,full.firstMark.fire.date,full.warmup_date]
  by_cases h1 : i.val = 1
  · rw [h1]
    refine ⟨⟨5,by omega⟩,full.tail.second.fire.latency,?_,?_,?_⟩
    · rw [full.packet_actual_one]
      change full.tail.second.fire.final.time = start + 4 * (5 : ℝ) + full.tail.second.fire.latency
      linarith [full.tail.second.fire.date,full.mark_date]
    · linarith [full.second_window.1,full.tail.second.fire.date,full.mark_date]
    · linarith [full.second_window.2,full.tail.second.fire.date,full.mark_date]
  by_cases h2 : i.val = 2
  · rw [h2]
    refine ⟨⟨7,by omega⟩,full.tail.high.first.latency,?_,full.tail.high.first.early,
      full.tail.high.first.deadline.trans (by norm_num)⟩
    · rw [full.packet_actual_two]
      change full.tail.high.first.final.time = start + 4 * (7 : ℝ) + full.tail.high.first.latency
      linarith [full.tail.high_first_date,full.mark_date]
  have hIndex : i.val - 3 + 3 = i.val := by omega
  have hSource : i.val - 3 + 8 < K := by omega
  refine ⟨⟨i.val - 3 + 8,hSource⟩,full.restLatency,?_,full.rest_latency_lower,
    full.rest_latency_upper.trans (by norm_num)⟩
  conv_lhs => rw [← hIndex,full.packet_actual_tail]
  change start + 32 + 4 * ((i.val - 3 : ℕ) : ℝ) + full.restLatency =
    start + 4 * ((i.val - 3 + 8 : ℕ) : ℝ) + full.restLatency
  push_cast
  ring

/-- Neither bound uses the final quiet horizon. -/
theorem packet_actual_strict_bounds (i : Fin (3 + (K - 8))) :
    start < full.packet.actual i.val ∧
      full.packet.actual i.val < start + 4 * ((K - 1 : ℕ) : ℝ) + 9 / 10 := by
  obtain ⟨source,latency,hDate,hLower,hUpper⟩ := full.packet_emission_origin i
  have hIndex : (source.val : ℝ) ≤ ((K - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show source.val ≤ K - 1 by omega)
  have hNonneg : (0 : ℝ) ≤ source.val := Nat.cast_nonneg _
  rw [hDate]
  constructor <;> nlinarith

theorem packet_actual_bounds (i : Fin (3 + (K - 8))) :
    start ≤ full.packet.actual i.val ∧
      full.packet.actual i.val ≤ start + 4 * ((K - 1 : ℕ) : ℝ) + 9 / 10 :=
  ⟨(full.packet_actual_strict_bounds i).1.le,(full.packet_actual_strict_bounds i).2.le⟩

theorem first_after_start : start < full.packet.actual 0 := by
  rw [full.packet_actual_zero]
  linarith [full.first_window.1]

theorem packet_last_deadline : full.packet.actual (3 + (K - 8) - 1) ≤
    start + 4 * ((K - 1 : ℕ) : ℝ) + 9 / 10 := by
  have hIndex : 3 + (K - 8) - 1 < 3 + (K - 8) := by omega
  exact (full.packet_actual_bounds ⟨3 + (K - 8) - 1,hIndex⟩).2

theorem chain_envelope : CadencePacketEnvelope full.packet start K 0 := by
  constructor
  · intro i
    exact (full.packet_actual_bounds i).1
  · intro i
    simpa only [Nat.cast_zero,mul_zero,add_zero] using (full.packet_actual_bounds i).2

private theorem leaf_single_parameters (θ : Fin 1 → Parameters) : θ = fun _ : Fin 1 => θ 0 := by
  funext i
  exact congrArg θ (Subsingleton.elim i 0)

/-- Use this exact leaf execution as the physical base cell of the causal
network induction. The parameter cast only names the unique Fin1 cell. -/
noncomputable def finiteCell : FiniteCausalCell (θ 0) s terminal where
  final := full.final
  execution := full.execution.cast_parameters (leaf_single_parameters θ)
  complete := by simpa only [CompleteThrough] using full.complete
  ready := full.ready 0
  charge := full.charge
  raw_none := full.raw_none 0
  pending := full.pending

theorem finite_cell_calendar : full.finiteCell.execution.emissionTimes 0 =
    full.execution.emissionTimes 0 := by
  simp only [finiteCell,Execution.emissionTimes,Execution.cast_parameters_ledger]

theorem finite_cell_packet_calendar : full.finiteCell.execution.emissionTimes 0 =
    List.ofFn (fun i : Fin (3 + (K - 8)) => full.packet.actual i.val) :=
  full.finite_cell_calendar.trans full.packet_calendar

theorem finite_cell_deliveries : full.finiteCell.execution.deliveries =
    sourceTrain 0 p start 4 K :=
  (full.execution.cast_parameters_deliveries (leaf_single_parameters θ)).trans full.deliveries

end ConstructedCadenceLeafK
end KernelR.Hybrid
