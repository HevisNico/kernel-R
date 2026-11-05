import KernelR.Family.FlowUniqueness

/-! Reserve barriers with symbolic work bounds. These hypotheses are separate
from the numerical estimates needed to verify them for a concrete protocol. -/
namespace KernelR.Family
open KernelR.Hybrid MeasureTheory Set

/-- A work ceiling keeps reserve above a chosen lower level, at every time of
an actual flow. No protocol calendar or nominal work estimate is used. -/
theorem Flow.energy_lower {n C θ s u} (f : @Flow n C θ s u)
    (rate : 0 ≤ C.energyRate) (i : Fin n) (lower : ℝ)
    (initial : lower ≤ s.x i .energy)
    (ceiling : ∀ v ∈ Icc s.time u.time,
      work C θ s (f.path v) i v ≤ C.energyRate * (C.energyTarget - lower))
    {t : ℝ} (ht : t ∈ Icc s.time u.time) : lower ≤ f.path t i .energy := by
  have sub : Icc s.time t ⊆ Icc s.time u.time := Icc_subset_Icc le_rfl ht.2
  have hi := (f.integrable i .energy).mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le f.positive.le]
    exact sub)
  have hc : ContinuousOn (fun v => -(f.path v i .energy)) (Icc s.time t) :=
    ((f.continuous i .energy).mono sub).neg
  have result := KernelR.Hybrid.integral_upper_barrier (cap := -lower) ht.1 hc hi.neg
    (by
      intro v hv
      change -f.path v i .energy = -f.path s.time i .energy +
        ∫ w in s.time..v, -(field C θ s (f.path w) w i .energy)
      rw [intervalIntegral.integral_neg, f.initial]
      have balance := f.integral_eq v (sub hv) i .energy
      linarith)
    (by rw [f.initial]; linarith)
    (by
      intro v hv gate
      change -(C.energyRate * (C.energyTarget - f.path v i .energy) -
        work C θ s (f.path v) i v) ≤ 0
      have bound := ceiling v (sub hv)
      have sign : 0 ≤ C.energyRate * (lower - f.path v i .energy) :=
        mul_nonneg rate (by linarith)
      nlinarith)
  linarith

/-- A work floor keeps reserve below a chosen upper level. Negative work is
allowed when it still satisfies the stated floor. -/
theorem Flow.energy_upper {n C θ s u} (f : @Flow n C θ s u)
    (rate : 0 ≤ C.energyRate) (i : Fin n) (upper : ℝ)
    (initial : s.x i .energy ≤ upper)
    (floor : ∀ v ∈ Icc s.time u.time,
      C.energyRate * (C.energyTarget - upper) ≤ work C θ s (f.path v) i v)
    {t : ℝ} (ht : t ∈ Icc s.time u.time) : f.path t i .energy ≤ upper := by
  have sub : Icc s.time t ⊆ Icc s.time u.time := Icc_subset_Icc le_rfl ht.2
  have hi := (f.integrable i .energy).mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le f.positive.le]
    exact sub)
  apply KernelR.Hybrid.integral_upper_barrier ht.1 ((f.continuous i .energy).mono sub) hi
  · intro v hv
    rw [f.initial]
    exact f.integral_eq v (sub hv) i .energy
  · simpa only [f.initial] using initial
  · intro v hv gate
    change C.energyRate * (C.energyTarget - f.path v i .energy) -
      work C θ s (f.path v) i v ≤ 0
    have bound := floor v (sub hv)
    have sign := mul_nonneg rate (sub_nonneg.mpr gate)
    nlinarith

/-- Positive reserve follows from a positive lower barrier; nonnegative
auxiliary charge and recovery then discharge all flow-safety premises. -/
theorem Flow.safe_of_work_ceiling {n C θ s u} (f : @Flow n C θ s u)
    (signs : FlowSigns C) (rest : 0 ≤ C.auxRest) (rates : RatesNonnegative θ)
    (input : ∀ i p, 0 ≤ (θ i).inputGain p)
    (initialAux : ∀ i p, 0 ≤ s.x i (.m p))
    (initialRecovery : ∀ i, 0 ≤ s.x i .b) (lower : ℝ) (positive : 0 < lower)
    (initialEnergy : ∀ i, lower ≤ s.x i .energy)
    (ceiling : ∀ v ∈ Icc s.time u.time, ∀ i,
      work C θ s (f.path v) i v ≤ C.energyRate * (C.energyTarget - lower)) : f.Safe := by
  apply f.safe_of_initial_and_energy signs rest rates input initialAux initialRecovery
  intro t ht i
  exact positive.trans_le (f.energy_lower signs.energyRate_nonneg i lower
    (initialEnergy i) (fun v hv => ceiling v hv i) ht)

#print axioms Flow.energy_lower
#print axioms Flow.energy_upper
#print axioms Flow.safe_of_work_ceiling

end KernelR.Family
