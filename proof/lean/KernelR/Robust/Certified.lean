import KernelR.Robust.Response
import KernelR.Robust.Induction
import KernelR.Robust.Evidence.Latency5

/-! An explicit link from the checked epsilon=.1, nu=.002, alpha=0 endpoints
to the abstract analytic and chain results. Enclosure membership is exposed. -/
namespace KernelR.Robust
open Evidence.Latency5

theorem checked_radius_value : (latency_radius.hi : ℝ) = 187 / 25000 := by
  norm_num [latency_radius]

theorem checked_radius_period_32 :
    15/2 + 2 * KernelR.Chain.pathJitter (fun _ => (latency_radius.hi : ℝ)) 31 ≤ 8 := by
  rw [KernelR.Chain.constant_jitter, checked_radius_value]
  norm_num

/-- The numerical margin is transferred to actual real increments only after
the caller supplies sound enclosures for those real quantities. -/
theorem checked_latency_margins {earlyError earlyIncrement lateError lateIncrement : ℝ}
    (he : early_reference_separation_dominates_perturbation_left.Contains earlyError)
    (hi : early_reference_separation_dominates_perturbation_right.Contains earlyIncrement)
    (hle : late_reference_separation_dominates_perturbation_left.Contains lateError)
    (hli : late_reference_separation_dominates_perturbation_right.Contains lateIncrement) :
    earlyError < earlyIncrement ∧ lateError < lateIncrement := by
  exact ⟨RationalBox.strict_of_enclosures he hi
    early_reference_separation_dominates_perturbation_verified,
    RationalBox.strict_of_enclosures hle hli
    late_reference_separation_dominates_perturbation_verified⟩

end KernelR.Robust
