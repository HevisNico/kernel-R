import KernelR.HybridWeakExecution
import KernelR.HybridFlowCuts

/-! Cuts of relaxed READY flows retain their integral paths and weak guards. -/
namespace KernelR.Hybrid
open Set MeasureTheory

noncomputable def WeakFlow.at {n θ s u} (flow : @WeakFlow n θ s u)
    (t : ℝ) : Snapshot n := {s with time := t, x := flow.path t}

/-- The remaining part of an existing positive flow, using the same path. -/
noncomputable def WeakFlow.suffix {n θ s u} (f : @WeakFlow n θ s u) {t : ℝ}
    (hstart : s.time ≤ t) (hend : t < u.time) : WeakFlow θ (f.at t) u where
  positive := hend
  path := f.path
  initial := rfl
  final := f.final
  main_fixed := f.main_fixed
  aux_fixed := f.aux_fixed
  raw_fixed := f.raw_fixed
  queue_fixed := f.queue_fixed
  continuous := fun i c => (f.continuous i c).mono (Icc_subset_Icc hstart le_rfl)
  integrable := fun i c => (f.integrable i c).mono_set (by
    change uIcc t u.time ⊆ uIcc s.time u.time
    rw [uIcc_of_le hend.le,uIcc_of_le f.positive.le]
    exact Icc_subset_Icc hstart le_rfl)
  mark_integrable := fun i p => (f.mark_integrable i p).mono_set (by
    change uIcc t u.time ⊆ uIcc s.time u.time
    rw [uIcc_of_le hend.le,uIcc_of_le f.positive.le]
    exact Icc_subset_Icc hstart le_rfl)
  integral_eq := by
    intro v hv i c
    have hv₀ : v ∈ Icc s.time u.time := ⟨hstart.trans hv.1,hv.2⟩
    have ht₀ : t ∈ Icc s.time u.time := ⟨hstart,hend.le⟩
    have hi₁ : IntervalIntegrable (fun v => field θ s (f.path v) v i c) volume s.time t :=
      (f.integrable i c).mono_set (by
        rw [uIcc_of_le hstart,uIcc_of_le f.positive.le]
        exact Icc_subset_Icc le_rfl hend.le)
    have hi₂ : IntervalIntegrable (fun v => field θ s (f.path v) v i c) volume t v :=
      (f.integrable i c).mono_set (by
        rw [uIcc_of_le (show t ≤ v from hv.1),uIcc_of_le f.positive.le]
        exact Icc_subset_Icc hstart hv.2)
    have ha := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
    have ht := f.integral_eq t ht₀ i c
    have he := f.integral_eq v hv₀ i c
    change f.path v i c = f.path t i c + ∫ w in t..v, field θ s (f.path w) w i c
    linarith
  guards := fun v hv => f.guards v ⟨hstart.trans hv.1,hv.2⟩
  raw_support := fun i p origin hr =>
    ⟨(f.raw_support i p origin hr).1.trans hstart,(f.raw_support i p origin hr).2⟩
  pending_urgent := f.pending_urgent

theorem WeakFlow.at_final {n θ s u} (f : @WeakFlow n θ s u) : f.at u.time = u := by
  cases s with
  | mk st sx sm sa sr sq =>
    cases u with
    | mk ut ux um ua ur uq =>
      dsimp only [WeakFlow.at]
      congr 1
      · exact f.final
      · exact f.main_fixed.symm
      · exact f.aux_fixed.symm
      · exact f.raw_fixed.symm
      · exact f.queue_fixed.symm

end KernelR.Hybrid
