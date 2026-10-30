import KernelR.HybridInvariants
import KernelR.HybridBounds

namespace KernelR.Hybrid
open MeasureTheory Set

/-- Closed sublevels on the compact flow interval, even when the path is only
specified on that interval. -/
theorem compact_sublevel_on_Icc {y : ℝ → ℝ} {s u cap : ℝ}
    (hc : ContinuousOn y (Icc s u)) : IsCompact {t | t ∈ Icc s u ∧ y t ≤ cap} := by
  have hclosed : IsClosed {t : Icc s u | y t ≤ cap} := isClosed_le hc.domRestrict continuous_const
  convert hclosed.isCompact.image continuous_subtype_val using 1
  ext x
  constructor
  · intro hx; exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  · rintro ⟨v, hv, rfl⟩; exact ⟨v.property, hv⟩

theorem continuous_bound_from_Ico {y : ℝ → ℝ} {s u cap : ℝ} (hsu : s < u)
    (hc : ContinuousOn y (Icc s u)) (hpre : ∀ t ∈ Ico s u, y t ≤ cap) :
    ∀ t ∈ Icc s u, y t ≤ cap := by
  have hsub : closure (Ico s u) ⊆ {t | t ∈ Icc s u ∧ y t ≤ cap} :=
    closure_minimal (fun t ht => ⟨⟨ht.1, ht.2.le⟩, hpre t ht⟩) (compact_sublevel_on_Icc hc).isClosed
  rw [closure_Ico hsu.ne] at hsub
  exact fun t ht => (hsub ht).2

theorem decay_upper {initial bound rate duration : ℝ} (hi : initial ≤ bound) (hb : 0 ≤ bound)
    (hr : 0 ≤ rate) (ht : 0 ≤ duration) : initial * Real.exp (-rate * duration) ≤ bound := by
  have he : Real.exp (-rate * duration) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  calc
    initial * Real.exp (-rate * duration) ≤ bound * Real.exp (-rate * duration) :=
      mul_le_mul_of_nonneg_right hi (Real.exp_pos _).le
    _ ≤ bound * 1 := mul_le_mul_of_nonneg_left he hb
    _ = bound := mul_one _

noncomputable def auxUpper : AuxMode → ℝ
  | .error => 1 / 10
  | _ => 1

def UpperRegion {n} (s : Snapshot n) : Prop :=
  ∀ i, 0 ≤ s.x i .b ∧ s.x i .q ≤ 1 ∧ ∀ p, s.x i (.m p) ≤ auxUpper (s.aux i p)

theorem Flow.main_upper {n θ ε s u} (f : @Flow n θ s u) (hb : PhysicalBox θ ε)
    (i : Fin n) (hq : s.x i .q ≤ 1) (hb₀ : 0 ≤ s.x i .b) :
    ∀ t ∈ Icc s.time u.time, f.path t i .q ≤ 1 := by
  cases hm : s.main i with
  | ready =>
    apply continuous_bound_from_Ico f.positive (f.continuous i .q)
    intro t ht
    have h := (f.guards t ht).1 i
    rw [hm] at h
    exact h.le
  | fast =>
    intro t ht
    rw [f.fast_solution i hm t ht]
    exact decay_upper hq (by norm_num) (by linarith [a_coarse_bounds.1]) (by linarith [ht.1])
  | slow =>
    intro t ht
    rw [f.slow_solution i hm t ht]
    have hn : 0 ≤ ∫ v in s.time..t, f.path v i .b :=
      intervalIntegral.integral_nonneg ht.1 (fun v hv => hb₀.trans
        (f.recovery_nondecreasing hb i v ⟨hv.1, hv.2.trans ht.2⟩))
    have he : Real.exp (-(∫ v in s.time..t, f.path v i .b)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hn)
    exact (mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le).trans (by simpa using he)

theorem Flow.aux_upper {n θ ε s u} (f : @Flow n θ s u) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hi : s.x i (.m p) ≤ auxUpper (s.aux i p)) :
    ∀ t ∈ Icc s.time u.time, f.path t i (.m p) ≤ auxUpper (s.aux i p) := by
  cases hm : s.aux i p with
  | ready =>
    change ∀ t ∈ Icc s.time u.time, f.path t i (.m p) ≤ 1
    apply continuous_bound_from_Ico f.positive (f.continuous i (.m p))
    intro t ht
    have h := (f.guards t ht).2 i p
    rw [hm] at h
    exact h.le
  | mark | silent | error =>
    intro t ht
    rw [f.aux_decay_solution i p (by simp [hm]) t ht]
    simp only [hm, auxUpper] at hi ⊢
    apply decay_upper hi (by norm_num) _ (by linarith [ht.1])
    all_goals first | exact (hb.rates_positive i p).1.le | exact (hb.rates_positive i p).2.1.le | exact (hb.rates_positive i p).2.2.le

theorem Flow.upper_region {n θ ε s u} (f : @Flow n θ s u) (hb : PhysicalBox θ ε)
    (hi : UpperRegion s) : UpperRegion u := by
  intro i
  have ht : u.time ∈ Icc s.time u.time := ⟨f.positive.le, le_rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · have h := f.recovery_nondecreasing hb i u.time ht
    rw [f.final] at h
    exact (hi i).1.trans h
  · simpa only [f.final] using f.main_upper hb i (hi i).2.1 (hi i).1 u.time ht
  · intro p
    simpa only [f.final, f.aux_fixed] using f.aux_upper hb i p ((hi i).2.2 p) u.time ht

theorem Jump.upper_region {n route s u} (j : @Jump n route s u)
    (hi : UpperRegion s) : UpperRegion u := by
  intro i
  refine ⟨?_, ?_, ?_⟩
  · simpa only [j.physical_continuous] using (hi i).1
  · simpa only [j.physical_continuous] using (hi i).2.1
  · intro p
    have h := (hi i).2.2 p
    cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
    all_goals split_ifs at * <;> simp_all [Function.update_apply]
    all_goals split_ifs at * <;> simp_all [Function.update_apply, auxUpper]
    all_goals norm_num [auxUpper] at *

theorem BirthState.upper_region {n s} (hs : @BirthState n s) : UpperRegion s := by
  intro i
  have hc := hs.2.2 i
  refine ⟨by linarith [hc.2.2.1.1], by linarith [hc.2.1.2], ?_⟩
  intro p
  rcases (hc.2.2.2.2 p).2 with h | h
  · rw [h.1]; dsimp [auxUpper]; linarith [h.2.2]
  · rw [h.1]; dsimp [auxUpper]; linarith [h.2.2]

theorem Execution.upper_region {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) : UpperRegion u := by
  induction e with
  | nil => exact hi
  | cons step rest ih =>
    apply ih
    cases step with
    | flow f => exact f.upper_region hb hi
    | jump j => exact j.upper_region hi

end KernelR.Hybrid
