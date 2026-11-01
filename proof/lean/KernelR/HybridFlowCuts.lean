import KernelR.HybridSingleOutput
import KernelR.HybridInputBalance
namespace KernelR.Hybrid
open Set MeasureTheory

/-- The remaining part of an existing positive flow, using the same path. -/
noncomputable def Flow.suffix {n θ s u} (f : @Flow n θ s u) {t : ℝ}
    (hstart : s.time ≤ t) (hend : t < u.time) : Flow θ (f.at t) u where
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

theorem Flow.at_final {n θ s u} (f : @Flow n θ s u) : f.at u.time = u := by
  cases s with
  | mk st sx sm sa sr sq =>
    cases u with
    | mk ut ux um ua ur uq =>
      dsimp only [Flow.at]
      congr 1
      · exact f.final
      · exact f.main_fixed.symm
      · exact f.aux_fixed.symm
      · exact f.raw_fixed.symm
      · exact f.queue_fixed.symm

def Execution.cast_source {n θ route s v u} (e : @Execution n θ route s u) (h : v = s) :
    Execution θ route v u := h.symm ▸ e

theorem Execution.cast_source_deliveries {n θ route s v u} (e : @Execution n θ route s u) (h : v = s) :
    (e.cast_source h).deliveries = e.deliveries := by cases h; rfl

theorem Execution.cast_source_ledger {n θ route s v u} (e : @Execution n θ route s u) (h : v = s) :
    (e.cast_source h).ledger = e.ledger := by cases h; rfl

/-- A cut has a genuine remaining execution; splitting a flow retains all events. -/
structure Execution.Continuation {n θ route s u v} (e : @Execution n θ route s u)
    (cut : Execution θ route s v) where
  tail : Execution θ route v u
  deliveries : e.deliveries = cut.deliveries ++ tail.deliveries
  emissions : e.ledger.emissions = cut.ledger.emissions ++ tail.ledger.emissions

theorem Execution.IsPrefix.continuation {n θ route s u v} {e : @Execution n θ route s u}
    {cut : Execution θ route s v} (hcut : e.IsPrefix cut) : Nonempty (e.Continuation cut) := by
  induction hcut with
  | nil e => exact ⟨⟨e,rfl,rfl⟩⟩
  | @flowCut s w u f rest t ht hend =>
    by_cases hlt : t < w.time
    · let tail : Execution θ route (f.at t) u := .cons (.flow (f.suffix ht.le hlt)) rest
      exact ⟨⟨tail,rfl,rfl⟩⟩
    · have heq : t = w.time := le_antisymm hend (le_of_not_gt hlt)
      have hsnap : f.at t = w := by rw [heq]; exact f.at_final
      let tail := rest.cast_source hsnap
      refine ⟨⟨tail,?_,?_⟩⟩
      · change rest.deliveries = tail.deliveries
        exact (rest.cast_source_deliveries hsnap).symm
      · change rest.ledger.emissions = tail.ledger.emissions
        exact congrArg (fun L : Ledger n => L.emissions) (rest.cast_source_ledger hsnap).symm
  | step move rest cut hcut ih =>
    obtain ⟨next⟩ := ih
    refine ⟨⟨next.tail,?_,?_⟩⟩
    · simp only [Execution.deliveries,next.deliveries,List.append_assoc]
    · simp only [Execution.ledger,Ledger.add,next.emissions,List.append_assoc]

theorem Execution.Continuation.emissionTimes {n θ route s u v} {e : @Execution n θ route s u}
    {cut : Execution θ route s v} (c : e.Continuation cut) (i : Fin n) :
    e.emissionTimes i = cut.emissionTimes i ++ c.tail.emissionTimes i := by
  simp only [Execution.emissionTimes,c.emissions,List.filter_append,List.map_append]

theorem Execution.Continuation.error_balance {n θ route s u v} {e : @Execution n θ route s u}
    {cut : Execution θ route s v} (c : e.Continuation cut) (i : Fin n) (p : Port) :
    e.ledger.error i p = cut.ledger.error i p + c.tail.ledger.error i p := by
  have h := e.gain_balance i p
  have hcut := cut.gain_balance i p
  have htail := c.tail.gain_balance i p
  linarith

theorem Execution.Continuation.recovery_balance {n θ route s u v} {e : @Execution n θ route s u}
    {cut : Execution θ route s v} (c : e.Continuation cut) (i : Fin n) :
    e.ledger.recovery i = cut.ledger.recovery i + c.tail.ledger.recovery i := by
  have h := e.recovery_balance i
  have hcut := cut.recovery_balance i
  have htail := c.tail.recovery_balance i
  linarith

end KernelR.Hybrid
