import KernelR.HybridCadenceReceiverSchedule
import KernelR.HybridFiniteCadencePacketGaps
import KernelR.HybridLocalCadenceHighBudgetTrain

/-! Full-budget input schedules retain the actual phase errors and derive
all spacing from the incoming packet. No output date is prescribed. -/
namespace KernelR.Hybrid

theorem packet_full_budget_learned_prefix_spacing {m L J} (packet : KernelR.Chain.Packet m L J)
    (hJ : J ≤ 3 / 20) (offset count : ℕ) (hend : offset + count < m) :
    LearnedPrefixSpacing (packet.actual offset) (cadenceDates packet.actual (offset + 1) count) := by
  induction count generalizing offset with
  | zero => trivial
  | succ count ih =>
    rw [cadenceDates_succ]
    constructor
    · have h := packet.full_budget_prefix_gap hJ offset (by omega)
      linarith [h.1]
    · apply ih
      omega

theorem packet_high_full_budget_schedule {m L J} (packet : KernelR.Chain.Packet m L J)
    (hJ : J ≤ 3 / 20) (offset count : ℕ) (terminal : ℝ)
    (hend : packet.actual (offset + count) + 37 / 10 ≤ terminal) :
    CadenceHighBudgetSchedule (packet.actual offset)
      (cadenceDates packet.actual (offset + 1) count) terminal := by
  induction count generalizing offset with
  | zero => simpa [CadenceHighBudgetSchedule] using hend
  | succ count ih =>
    rw [cadenceDates_succ]
    constructor
    · linarith [packet.full_budget_actual_gap hJ offset]
    · apply ih
      have hidx : offset + 1 + count = offset + (count + 1) := by omega
      simpa only [hidx] using hend

end KernelR.Hybrid
