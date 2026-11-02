import KernelR.HybridCadenceMarkOnlyExistence
import KernelR.HybridCadenceHighCompletion

/-! Real logarithmic return margins for received gaps as short as3.7.
These are separate strengthened consequences; the established three-cell
constructors and their original return interfaces remain unchanged. -/
namespace KernelR.Hybrid

/-- The high response's actual FAST/SLOW root is before3.68, uniformly over
its own recovery band and the existing carried-charge firing window. -/
theorem full_budget_high_reopen_bound {B S latency R : ℝ}
    (hB : 37999 / 100000 ≤ B) (hlat : latency < 13 / 50)
    (hclock : R = S + latency + 1 + Real.log (5 / 2 : ℝ) / B) :
    R < S + 92 / 25 := by
  have hbpos : 0 < B := by linarith
  have hquot : Real.log (5 / 2 : ℝ) / B < 121 / 50 :=
    (div_lt_iff₀ hbpos).mpr (by linarith [KernelR.log_recovery_bounds.2])
  rw [hclock]
  linarith

/-- A completed protected MARK starts its constant-recovery clock before.05.
Even the largest admitted charge returns before3.35, hence before gap3.7. -/
theorem full_budget_mark_reopen_bound {B S M q R : ℝ}
    (hB : 27999 / 100000 ≤ B) (hM : M < S + 1 / 20)
    (hq : 0 < q ∧ q ≤ 1 / 4)
    (hclock : R = M + Real.log (q / (1 / 10 : ℝ)) / B) :
    R < S + 67 / 20 := by
  have hbpos : 0 < B := by linarith
  have hlog : Real.log (q / (1 / 10 : ℝ)) ≤ Real.log (5 / 2 : ℝ) := by
    apply Real.log_le_log (div_pos hq.1 (by norm_num)) ?_
    linarith [hq.2]
  have hquot : Real.log (q / (1 / 10 : ℝ)) / B < 33 / 10 := by
    apply (div_lt_iff₀ hbpos).mpr
    linarith [KernelR.log_recovery_bounds.2]
  rw [hclock]
  linarith

/-- A genuine existing protected-MARK witness already retains enough clock
metadata to recover its stronger return deadline, without a new execution. -/
theorem CadenceMarkOnlyResponse.return_before_full_budget_gap {θ route s p}
    (m : CadenceMarkOnlyResponse θ route s p)
    (hbown : 17999 / 100000 ≤ s.x 0 .b) :
    m.returnState.time < s.time + 67 / 20 := by
  let B := s.x 0 .b + 1 / 10
  have hB : 27999 / 100000 ≤ B := by dsimp [B]; linarith
  have hbpos : 0 < B := by linarith
  have hbM : m.markPrefix.final.x 0 .b = B := m.markPrefix.recovery_gain
  have hbA : m.auxiliary.final.x 0 .b = B := (m.auxiliary.recovery 0).trans hbM
  have hqMpos : 0 < m.markPrefix.final.x 0 .q := by linarith [m.markPrefix.charge.1]
  have hlog : Real.log (m.auxiliary.final.x 0 .q / (1 / 10)) =
      Real.log (m.markPrefix.final.x 0 .q / (1 / 10)) -
        B * (m.auxiliary.final.time - m.markPrefix.final.time) := by
    rw [m.auxiliary.charge_clock,hbM]
    rw [Real.log_div (mul_ne_zero (ne_of_gt hqMpos) (Real.exp_ne_zero _)) (by norm_num),
      Real.log_mul (ne_of_gt hqMpos) (Real.exp_ne_zero _),Real.log_exp,
      Real.log_div (ne_of_gt hqMpos) (by norm_num)]
    ring
  have hclock : m.returnState.time = m.markPrefix.final.time +
      Real.log (m.markPrefix.final.x 0 .q / (1 / 10)) / B := by
    rw [m.returnDate]
    dsimp [slowReopenDuration]
    rw [hbA,hlog]
    field_simp [ne_of_gt hbpos]
    ring
  exact full_budget_mark_reopen_bound hB m.markPrefix.deadline
    ⟨hqMpos,m.markPrefix.charge.2⟩ hclock

end KernelR.Hybrid
