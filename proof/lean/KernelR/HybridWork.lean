import KernelR.HybridRegion

namespace KernelR.Hybrid
open MeasureTheory Set

theorem pulse_bounds (origin t : ℝ) : 0 ≤ pulse origin t ∧ pulse origin t ≤ a := by
  have ha : 0 ≤ a := by linarith [a_coarse_bounds.1]
  unfold pulse
  split_ifs with h
  · have he : Real.exp (-a * (t - origin)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [h.1])
    constructor
    · exact mul_nonneg ha (Real.exp_pos _).le
    · simpa using mul_le_mul_of_nonneg_left he ha
  · exact ⟨le_rfl, ha⟩

theorem current_bounds {n} (s : Snapshot n) (i : Fin n) (p : Port) (t : ℝ) :
    0 ≤ current s i p t ∧ current s i p t ≤ a := by
  unfold current
  cases s.raw i p with
  | none => exact ⟨le_rfl, by linarith [a_coarse_bounds.1]⟩
  | some origin => exact pulse_bounds origin t

theorem sum_three_le {g : Port → ℝ} {c : ℝ} (h : ∀ p, g p ≤ c) :
    (∑ p : Port, g p) ≤ 3 * c := by
  calc
    _ ≤ ∑ p : Port, c := Finset.sum_le_sum (fun p _ => h p)
    _ = _ := by simp [Port, mul_comm]

theorem Flow.main_protected_positive {n θ s u} (f : @Flow n θ s u) (i : Fin n)
    (hm : s.main i ≠ .ready) {t : ℝ} (ht : t ∈ Icc s.time u.time) : 0 < f.path t i .q := by
  have hg := (f.guards s.time ⟨le_rfl, f.positive⟩).1 i
  rw [f.initial] at hg
  cases hmode : s.main i with
  | ready => exact False.elim (hm hmode)
  | fast =>
    rw [hmode] at hg
    rw [f.fast_solution i hmode t ht]
    exact mul_pos (by linarith) (Real.exp_pos _)
  | slow =>
    rw [hmode] at hg
    rw [f.slow_solution i hmode t ht]
    exact mul_pos (by linarith) (Real.exp_pos _)

/-- All actual work terms are bounded before deriving energy positivity. -/
theorem Flow.actual_work_bound {n θ ε s u} (f : @Flow n θ s u) (hb : PhysicalBox θ ε)
    (hi : UpperRegion s) (hcap : ∀ i p, s.x i (.z p) ≤ Real.log ((θ i).cap p))
    (i : Fin n) : f.workBound i := by
  intro t ht
  have ha : 0 ≤ a := by linarith [a_coarse_bounds.1]
  have hq := f.main_upper hb i (hi i).2.1 (hi i).1 t ht
  have hmu (p : Port) := f.aux_upper hb i p ((hi i).2.2 p) t ht
  have hgain (p : Port) : Real.exp (f.path t i (.z p)) ≤ 5 := by
    calc
      _ ≤ Real.exp (Real.log ((θ i).cap p)) := Real.exp_le_exp.mpr (f.gain_cap_on i p (hcap i p) t ht)
      _ = (θ i).cap p := Real.exp_log (hb.cap_positive i p)
      _ ≤ 5 := (hb.coarse_upper i p).1
  have hdrive0 : 0 ≤ drive s (f.path t) i t :=
    Finset.sum_nonneg (fun p _ => mul_nonneg (Real.exp_pos _).le (current_bounds s i p t).1)
  have hdrive : drive s (f.path t) i t ≤ 15 * a := by
    have h := sum_three_le (fun p => mul_le_mul (hgain p) (current_bounds s i p t).2
      (current_bounds s i p t).1 (by norm_num : (0 : ℝ) ≤ 5))
    change drive s (f.path t) i t ≤ 3 * (5 * a) at h
    nlinarith
  have hm0 : 0 ≤ (match s.main i with
      | .ready => drive s (f.path t) i t | .fast => a * f.path t i .q | .slow => 11 / 10) := by
    cases hm : s.main i with
    | ready => exact hdrive0
    | fast => exact mul_nonneg ha (f.main_protected_positive i (by simp [hm]) ht).le
    | slow => norm_num
  have hm : (match s.main i with
      | .ready => drive s (f.path t) i t | .fast => a * f.path t i .q | .slow => 11 / 10) ≤
      16 * a + 11 / 10 := by
    cases hmode : s.main i with
    | ready => linarith
    | fast => nlinarith [mul_le_mul_of_nonneg_left hq ha]
    | slow => nlinarith
  have hx0 (p : Port) : 0 ≤ (if s.aux i p = .ready then (θ i).inputGain p * current s i p t
      else auxDrain (θ i) (s.aux i p) p (f.path t i (.m p))) := by
    split_ifs with h
    · exact mul_nonneg (hb.input_gain_positive i p).le (current_bounds s i p t).1
    · have hpos := (f.protected_aux_positive i p h ht).le
      rcases hb.rates_positive i p with ⟨hmpos, hspos, hepos⟩
      cases hmode : s.aux i p <;> simp_all [auxDrain]
      all_goals positivity
  have hx (p : Port) : (if s.aux i p = .ready then (θ i).inputGain p * current s i p t
      else auxDrain (θ i) (s.aux i p) p (f.path t i (.m p))) ≤ 60 * a + 28 := by
    have hp := hb.coarse_upper i p
    have hmport := hmu p
    cases hmode : s.aux i p with
    | ready =>
      simp only [reduceCtorEq, ite_true]
      have hmul := mul_le_mul hp.2.2.2.2 (current_bounds s i p t).2
        (current_bounds s i p t).1 (by norm_num : (0 : ℝ) ≤ 60)
      linarith
    | mark | silent | error =>
      have hpos := (f.protected_aux_positive i p (by simp [hmode]) ht).le
      simp only [hmode, auxUpper] at hmport
      simp only [reduceCtorEq, ite_false, auxDrain]
      all_goals first
        | nlinarith [mul_le_mul hp.2.1 hmport hpos (by norm_num : (0 : ℝ) ≤ 14)]
        | nlinarith [mul_le_mul hp.2.2.1 hmport hpos (by norm_num : (0 : ℝ) ≤ 3)]
        | nlinarith [mul_le_mul hp.2.2.2.1 hmport hpos (by norm_num : (0 : ℝ) ≤ 11)]
  have hg (p : Port) : errorAct θ s (f.path t) i p ≤ 44 / 5 := by
    unfold errorAct
    split_ifs with h
    · have hmport := hmu p
      rw [h.1] at hmport
      dsimp [auxUpper] at hmport
      have hpos := (f.protected_aux_positive i p (by rw [h.1]; decide) ht).le
      nlinarith [mul_le_mul (hb.coarse_upper i p).2.2.2.1 hmport hpos (by norm_num : (0 : ℝ) ≤ 11)]
    · norm_num
  have hbmark (p : Port) : markAct θ s (f.path t) i p ≤ 7 := by
    unfold markAct
    split_ifs with h
    · have hmport := hmu p
      rw [h.1] at hmport
      dsimp [auxUpper] at hmport
      have hpos := (f.protected_aux_positive i p (by rw [h.1]; decide) ht).le
      nlinarith [mul_le_mul (hb.coarse_upper i p).2.1 hmport hpos (by norm_num : (0 : ℝ) ≤ 14)]
    · norm_num
  constructor
  · dsimp [work]
    exact add_nonneg (add_nonneg (add_nonneg hm0 (Finset.sum_nonneg (fun p _ => hx0 p)))
      (Finset.sum_nonneg (fun p _ => f.error_act_nonnegative hb i p ht)))
      (Finset.sum_nonneg (fun p _ => f.mark_act_nonnegative hb i p ht))
  · have hxsum := sum_three_le hx
    have hgsum := sum_three_le hg
    have hbmsum := sum_three_le hbmark
    calc
      work θ s (f.path t) i t ≤ (16 * a + 11 / 10) + 3 * (60 * a + 28) + 3 * (44 / 5) + 3 * 7 :=
        add_le_add (add_le_add (add_le_add hm hxsum) hgsum) hbmsum
      _ ≤ 500 := by linarith only [a_coarse_bounds.2]

/-- Work bounds are obtained from the initial physical region and propagated
caps; energy positivity is not a premise of this induction. -/
theorem Execution.actual_work_bound {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s)
    (hcap : ∀ i p, s.x i (.z p) ≤ Real.log ((θ i).cap p)) (i : Fin n) : e.WorkBound i := by
  induction e with
  | nil => trivial
  | cons step rest ih =>
    cases step with
    | flow f =>
      refine ⟨f.actual_work_bound hb hi hcap i, ih (f.upper_region hb hi) ?_⟩
      intro j p
      exact f.gain_cap j p (hcap j p)
    | jump j =>
      apply ih (j.upper_region hi)
      intro k p
      simpa only [j.physical_continuous] using hcap k p

/-- Global reserve theorem for the declared birth and fabrication families.
It covers every finite admissible execution, independently of the pulse word. -/
theorem Execution.reserve_birth_invariant {n θ ε route s u} (e : @Execution n θ route s u)
    (hs : BirthState s) (hb : PhysicalBox θ ε) (i : Fin n) :
    50 ≤ u.x i .energy ∧ u.x i .energy ≤ 100 :=
  e.reserve_invariant i (hs.2.2 i).2.2.2.1
    (e.actual_work_bound hb hs.upper_region (fun j p => hs.initial_gain_cap hb j p) i)

theorem Execution.power_gate_open {n θ ε route s u} (e : @Execution n θ route s u)
    (hs : BirthState s) (hb : PhysicalBox θ ε) (i : Fin n) : 0 < u.x i .energy := by
  have he := e.reserve_birth_invariant hs hb i
  linarith [he.1]

noncomputable def Flow.at {n θ s u} (f : @Flow n θ s u) (t : ℝ) : Snapshot n :=
  { s with time := t, x := f.path t }

/-- A real prefix remains an admissible flow, including when its endpoint is a
physical guard. The terminal jump is handled separately by execution semantics. -/
noncomputable def Flow.prefix {n θ s u} (f : @Flow n θ s u) {t : ℝ}
    (hstart : s.time < t) (hend : t ≤ u.time) : Flow θ s (f.at t) where
  positive := hstart
  path := f.path
  initial := f.initial
  final := rfl
  main_fixed := rfl
  aux_fixed := rfl
  raw_fixed := rfl
  queue_fixed := rfl
  continuous := fun i c => (f.continuous i c).mono (Icc_subset_Icc le_rfl hend)
  integrable := fun i c => (f.integrable i c).mono_set (by
    dsimp only [Flow.at]
    rw [uIcc_of_le hstart.le, uIcc_of_le f.positive.le]
    exact Icc_subset_Icc le_rfl hend)
  mark_integrable := fun i p => (f.mark_integrable i p).mono_set (by
    dsimp only [Flow.at]
    rw [uIcc_of_le hstart.le, uIcc_of_le f.positive.le]
    exact Icc_subset_Icc le_rfl hend)
  integral_eq := fun v hv i c => f.integral_eq v ⟨hv.1, hv.2.trans hend⟩ i c
  guards := fun v hv => f.guards v ⟨hv.1, hv.2.trans_le hend⟩
  raw_support := fun i p origin hraw =>
    ⟨(f.raw_support i p origin hraw).1, hend.trans (f.raw_support i p origin hraw).2⟩
  pending_urgent := fun d hd => hend.trans (f.pending_urgent d hd)

theorem Flow.reserve_invariant_on {n θ ε s u} (f : @Flow n θ s u) (hb : PhysicalBox θ ε)
    (hi : UpperRegion s) (hcap : ∀ i p, s.x i (.z p) ≤ Real.log ((θ i).cap p))
    (i : Fin n) (hE : 50 ≤ s.x i .energy ∧ s.x i .energy ≤ 100) :
    ∀ t ∈ Icc s.time u.time, 50 ≤ f.path t i .energy ∧ f.path t i .energy ≤ 100 := by
  intro t ht
  by_cases he : t = s.time
  · simpa only [he, f.initial] using hE
  · have hstart : s.time < t := lt_of_le_of_ne ht.1 (Ne.symm he)
    let flowPrefix := f.prefix hstart ht.2
    exact flowPrefix.reserve_invariant i hE (flowPrefix.actual_work_bound hb hi hcap i)

/-- Positive reserve throughout a real flow reached from the declared birth
family, including both endpoints and all cap-contact times. -/
theorem Flow.reachable_power_gate_open {n θ ε route born s u}
    (past : @Execution n θ route born s) (f : @Flow n θ s u)
    (hborn : BirthState born) (hb : PhysicalBox θ ε) (i : Fin n) :
    ∀ t ∈ Icc s.time u.time, 0 < f.path t i .energy := by
  have hregion := past.upper_region hb hborn.upper_region
  have hcap : ∀ j p, s.x j (.z p) ≤ Real.log ((θ j).cap p) :=
    fun j p => past.gain_cap j p (hborn.initial_gain_cap hb j p)
  have he := f.reserve_invariant_on hb hregion hcap i (past.reserve_birth_invariant hborn hb i)
  intro t ht
  linarith [(he t ht).1]

/-- Energy exposure is derived from reachability. The actual mode chronology
and strict gain-cap inactivity still need a protocol proof. -/
theorem Flow.error_open_of_reachable {n θ ε route born s u}
    (past : @Execution n θ route born s) (f : @Flow n θ s u)
    (hborn : BirthState born) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port)
    (ha : s.aux i p = .error) (hm : s.main i = .ready)
    (hcap : ∀ t ∈ Icc s.time u.time, f.path t i (.z p) < Real.log ((θ i).cap p)) :
    ErrorOpen f i p :=
  ⟨ha, hm, fun t ht => ⟨f.reachable_power_gate_open past hborn hb i t ht, hcap t ht⟩⟩

theorem Flow.mark_open_of_reachable {n θ ε route born s u}
    (past : @Execution n θ route born s) (f : @Flow n θ s u)
    (hborn : BirthState born) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port)
    (ha : s.aux i p = .mark) (hm : s.main i ≠ .ready)
    (hcap : ∀ t ∈ Icc s.time u.time, f.path t i .b < 11 / 10) : MarkOpen f i p :=
  ⟨ha, hm, fun t ht => ⟨f.reachable_power_gate_open past hborn hb i t ht, hcap t ht⟩⟩

end KernelR.Hybrid
