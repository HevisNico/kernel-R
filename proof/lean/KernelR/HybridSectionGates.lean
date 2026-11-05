import KernelR.HybridDoseCounting
import KernelR.HybridMarkBudget

/-! Derive strict learning gates along a physical execution from its final
headroom. Monotonicity bounds the whole path; reserve invariance supplies
positive energy. No gate certificate is assumed for an intermediate state. -/
namespace KernelR.Hybrid
open Set MeasureTheory

theorem Flow.gain_le_final {n θ ε s u} (f : @Flow n θ s u)
    (box : PhysicalBox θ ε) (i : Fin n) (p : Port) :
    ∀ t ∈ Icc s.time u.time, f.path t i (.z p) ≤ u.x i (.z p) := by
  intro t ht
  have nonnegative : ∀ᵐ v ∂volume.restrict (Ioc s.time u.time),
      0 ≤ field θ s (f.path v) v i (.z p) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact f.error_act_nonnegative box i p ⟨hv.1.le, hv.2⟩
  have integral := intervalIntegral.integral_mono_interval (μ := volume)
    (f := fun v => field θ s (f.path v) v i (.z p)) le_rfl ht.1 ht.2
    nonnegative (f.integrable i (.z p))
  have here := f.integral_eq t ht i (.z p)
  have terminal := f.integral_eq u.time ⟨f.positive.le, le_rfl⟩ i (.z p)
  rw [f.final] at terminal
  linarith

theorem Execution.learningGatesOpen_of_final_headroom {n θ ε route s u}
    (execution : @Execution n θ route s u)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s)
    (gain : ∀ i p, u.x i (.z p) < Real.log ((θ i).cap p))
    (recovery : ∀ i, u.x i .b < 11 / 10) : LearningGatesOpen execution := by
  induction execution with
  | nil => trivial
  | @cons s middle u move rest ih =>
    have next := (Execution.cons move (.nil _) : Execution θ route s middle).physical_invariant box physical
    have tail := ih next gain recovery
    cases move with
    | jump jump => exact tail
    | flow flow =>
      refine ⟨?_, tail⟩
      intro t ht i
      refine ⟨flow.power_gate_open_of_invariant box physical i t ht, ?_, ?_⟩
      · exact lt_of_le_of_lt ((flow.recovery_le_final box i t ht).trans
          (rest.recovery_nondecreasing box i)) (recovery i)
      · intro p
        exact lt_of_le_of_lt ((flow.gain_le_final box i p t ht).trans
          (rest.gain_nondecreasing box i p)) (gain i p)

#print axioms Execution.learningGatesOpen_of_final_headroom

end KernelR.Hybrid
