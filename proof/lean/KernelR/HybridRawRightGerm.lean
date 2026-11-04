import KernelR.Hybrid

/-! Every raw pulse has a short right germ of exponential decay. This includes
inactive future and expired raw entries, without requiring raw validity. -/
namespace KernelR.Hybrid
open Set

/-- A pulse is either inactive or follows exponential decay on a sufficiently
short right interval, including a raw start or expiry exactly at the base time. -/
theorem pulse_right_germ (origin start : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ico start (start + δ),
      pulse origin t = pulse origin start * Real.exp (-a * (t - start)) := by
  by_cases hstart : origin ≤ start
  · by_cases hend : start < origin + 1
    · refine ⟨origin + 1 - start, by linarith, ?_⟩
      intro t ht
      have hactive : origin ≤ t ∧ t < origin + 1 :=
        ⟨hstart.trans ht.1, by linarith [ht.2]⟩
      have hbase : origin ≤ start ∧ start < origin + 1 := ⟨hstart, hend⟩
      simp only [pulse, ite_eq_left hactive, ite_eq_left hbase]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    · refine ⟨1, by norm_num, ?_⟩
      intro t ht
      have htend : ¬ t < origin + 1 := by linarith [ht.1]
      simp only [pulse, htend, and_false, ite_false, hend, zero_mul]
  · refine ⟨origin - start, by linarith, ?_⟩
    intro t ht
    have htbeg : ¬ origin ≤ t := by linarith [ht.2]
    simp only [pulse, htbeg, hstart, false_and, ite_false, zero_mul]

/-- The three ports admit a common positive right interval, without assumptions
on which raw entries are currently active. -/
theorem current_right_germ {n} (s : Snapshot n) (i : Fin n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Port) (t : ℝ), t ∈ Ico s.time (s.time + δ) →
      current s i p t = current s i p s.time * Real.exp (-a * (t - s.time)) := by
  have each : ∀ p : Port, ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ico s.time (s.time + δ),
      current s i p t = current s i p s.time * Real.exp (-a * (t - s.time)) := by
    intro p
    cases hraw : s.raw i p with
    | none => exact ⟨1, by norm_num, by simp [current, hraw]⟩
    | some origin => simpa only [current, hraw] using pulse_right_germ origin s.time
  choose δ hpos htail using each
  refine ⟨min (δ 0) (min (δ 1) (δ 2)),
    lt_min (hpos 0) (lt_min (hpos 1) (hpos 2)), ?_⟩
  intro p t ht
  have hδ : min (δ 0) (min (δ 1) (δ 2)) ≤ δ p := by
    fin_cases p
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  exact htail p t ⟨ht.1, by linarith [ht.2]⟩

end KernelR.Hybrid
