import KernelR.HybridFlow
import KernelR.Recovery

/-! Integral invariants valid even at discontinuous actuator cap contacts. -/
namespace KernelR.Hybrid
open MeasureTheory Set

/-- A continuous integral trajectory cannot cross a cap where its actual
actuation density vanishes. No differentiability at the cap is assumed. -/
theorem integral_upper_barrier {y g : ℝ → ℝ} {s u cap : ℝ} (hsu : s ≤ u)
    (hc : ContinuousOn y (Icc s u)) (hi : IntervalIntegrable g volume s u)
    (hy : ∀ t ∈ Icc s u, y t = y s + ∫ v in s..t, g v)
    (hinit : y s ≤ cap) (hgate : ∀ t ∈ Icc s u, cap ≤ y t → g t ≤ 0) : y u ≤ cap := by
  by_contra hout
  have hout' : cap < y u := lt_of_not_ge hout
  let A : Set ℝ := {t | t ∈ Icc s u ∧ y t ≤ cap}
  have hAc : IsCompact A := by
    have hclosed : IsClosed {t : Icc s u | y t ≤ cap} :=
      isClosed_le hc.domRestrict continuous_const
    have himage := hclosed.isCompact.image continuous_subtype_val
    convert himage using 1
    ext x
    constructor
    · intro hx; exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨v.property, hv⟩
  obtain ⟨c, hcA, hmax⟩ := hAc.exists_isGreatest ⟨s, ⟨⟨le_rfl, hsu⟩, hinit⟩⟩
  have hcs : s ≤ c := hcA.1.1
  have hcu : c < u := by
    have hle := hcA.1.2
    by_contra h
    have he : c = u := le_antisymm hle (le_of_not_gt h)
    have hh := hcA.2
    rw [he] at hh
    linarith
  have hgneg : (∫ v in c..u, g v) ≤ 0 := by
    have he : (∫ v in c..u, g v) = ∫ v in c..u, min (g v) 0 := by
      apply intervalIntegral.integral_congr_Ioo_of_le hcu.le
      intro v hv
      have hvcap : cap < y v := by
        by_contra h
        have hvA : v ∈ A := ⟨⟨hcs.trans hv.1.le, hv.2.le⟩, le_of_not_gt h⟩
        exact (not_le_of_gt hv.1) (hmax hvA)
      exact (min_eq_left (hgate v ⟨hcs.trans hv.1.le, hv.2.le⟩ hvcap.le)).symm
    rw [he]
    have hn : 0 ≤ ∫ v in c..u, -min (g v) 0 :=
      intervalIntegral.integral_nonneg_of_forall hcu.le (fun v => neg_nonneg.mpr (min_le_right _ _))
    rw [intervalIntegral.integral_neg] at hn
    linarith
  have hleft : IntervalIntegrable g volume s c := hi.mono_set (by
    rw [uIcc_of_le hcs, uIcc_of_le hsu]
    exact Icc_subset_Icc le_rfl hcu.le)
  have hright : IntervalIntegrable g volume c u := hi.mono_set (by
    rw [uIcc_of_le hcu.le, uIcc_of_le hsu]
    exact Icc_subset_Icc hcs le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have h₁ := hy c hcA.1
  have h₂ := hy u ⟨hsu, le_rfl⟩
  have hcap := hcA.2
  linarith

/-- Exact cap gates are a special case of the integral barrier. -/
theorem integral_cap_barrier {y g : ℝ → ℝ} {s u cap : ℝ} (hsu : s ≤ u)
    (hc : ContinuousOn y (Icc s u)) (hi : IntervalIntegrable g volume s u)
    (hy : ∀ t ∈ Icc s u, y t = y s + ∫ v in s..t, g v)
    (hinit : y s ≤ cap) (hgate : ∀ t ∈ Icc s u, cap ≤ y t → g t = 0) : y u ≤ cap :=
  integral_upper_barrier hsu hc hi hy hinit (fun t ht hg => (hgate t ht hg).le)

theorem Flow.gain_cap {n θ s u} (f : @Flow n θ s u) (i : Fin n) (p : Port)
    (hinit : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) ≤ Real.log ((θ i).cap p) := by
  have h := integral_cap_barrier f.positive.le (f.continuous i (.z p)) (f.integrable i (.z p))
    (by simpa only [f.initial] using fun t ht => f.integral_eq t ht i (.z p))
    (by simpa only [f.initial] using hinit)
    (fun t ht hcap => by simp [field, errorAct, not_lt.mpr hcap])
  simpa only [f.final] using h

theorem Flow.recovery_cap {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (hinit : s.x i .b ≤ 11 / 10) : u.x i .b ≤ 11 / 10 := by
  have h := integral_cap_barrier f.positive.le (f.continuous i .b) (f.integrable i .b)
    (by simpa only [f.initial] using fun t ht => f.integral_eq t ht i .b)
    (by simpa only [f.initial] using hinit)
    (fun t ht hcap => by simp [field, markAct, not_lt.mpr hcap])
  simpa only [f.final] using h

theorem Execution.gain_cap {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (hinit : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    u.x i (.z p) ≤ Real.log ((θ i).cap p) := by
  induction e with
  | nil => exact hinit
  | cons step rest ih =>
    apply ih
    cases step with
    | flow f => exact f.gain_cap i p hinit
    | jump j => simpa only [j.physical_continuous] using hinit

theorem Execution.recovery_cap {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hinit : s.x i .b ≤ 11 / 10) : u.x i .b ≤ 11 / 10 := by
  induction e with
  | nil => exact hinit
  | cons step rest ih =>
    apply ih
    cases step with
    | flow f => exact f.recovery_cap i hinit
    | jump j => simpa only [j.physical_continuous] using hinit

theorem Flow.protected_aux_positive {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (p : Port) (hm : s.aux i p ≠ .ready) {t : ℝ}
    (ht : t ∈ Icc s.time u.time) : 0 < f.path t i (.m p) := by
  have hguard := (f.guards s.time ⟨le_rfl, f.positive⟩).2 i p
  rw [f.initial] at hguard
  have hstart : 0 < s.x i (.m p) := by
    cases ha : s.aux i p <;> simp_all
    all_goals linarith
  rw [f.aux_decay_solution i p hm t ht]
  exact mul_pos hstart (Real.exp_pos _)

theorem Flow.error_act_nonnegative {n θ ε s u} (f : @Flow n θ s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) {t : ℝ} (ht : t ∈ Icc s.time u.time) :
    0 ≤ errorAct θ s (f.path t) i p := by
  unfold errorAct
  split_ifs with h
  · have hp := f.protected_aux_positive i p (by rw [h.1]; decide) ht
    exact mul_nonneg (mul_nonneg (by norm_num) (hb.rates_positive i p).2.2.le) hp.le
  · exact le_rfl

theorem Flow.mark_act_nonnegative {n θ ε s u} (f : @Flow n θ s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) {t : ℝ} (ht : t ∈ Icc s.time u.time) :
    0 ≤ markAct θ s (f.path t) i p := by
  unfold markAct
  split_ifs with h
  · have hp := f.protected_aux_positive i p (by rw [h.1]; decide) ht
    exact mul_nonneg (mul_nonneg (by norm_num) (hb.rates_positive i p).1.le) hp.le
  · exact le_rfl

theorem Flow.gain_nondecreasing {n θ ε s u} (f : @Flow n θ s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) :
    ∀ t ∈ Icc s.time u.time, s.x i (.z p) ≤ f.path t i (.z p) := by
  intro t ht
  have he := f.integral_eq t ht i (.z p)
  have hn : 0 ≤ ∫ v in s.time..t, errorAct θ s (f.path v) i p :=
    intervalIntegral.integral_nonneg ht.1 (fun v hv =>
      f.error_act_nonnegative hb i p ⟨hv.1, hv.2.trans ht.2⟩)
  simp only [field] at he
  linarith

theorem Flow.recovery_nondecreasing {n θ ε s u} (f : @Flow n θ s u)
    (hb : PhysicalBox θ ε) (i : Fin n) :
    ∀ t ∈ Icc s.time u.time, s.x i .b ≤ f.path t i .b := by
  intro t ht
  have he := f.integral_eq t ht i .b
  have hn : 0 ≤ ∫ v in s.time..t, ∑ p : Port, markAct θ s (f.path v) i p :=
    intervalIntegral.integral_nonneg ht.1 (fun v hv => Finset.sum_nonneg
      (fun p _ => f.mark_act_nonnegative hb i p ⟨hv.1, hv.2.trans ht.2⟩))
  simp only [field] at he
  linarith

theorem Execution.gain_nondecreasing {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) : s.x i (.z p) ≤ u.x i (.z p) := by
  induction e with
  | nil => exact le_rfl
  | @cons s u v step rest ih =>
    apply le_trans _ ih
    cases step with
    | flow f => simpa only [f.final] using f.gain_nondecreasing hb i p u.time ⟨f.positive.le, le_rfl⟩
    | jump j => simp [j.physical_continuous]

theorem Execution.recovery_nondecreasing {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) : s.x i .b ≤ u.x i .b := by
  induction e with
  | nil => exact le_rfl
  | @cons s u v step rest ih =>
    apply le_trans _ ih
    cases step with
    | flow f => simpa only [f.final] using f.recovery_nondecreasing hb i u.time ⟨f.positive.le, le_rfl⟩
    | jump j => simp [j.physical_continuous]

/-- Reserve invariance for actual integral flows, allowing work to jump at cap
contacts. The work bound must still be derived for the physical region. -/
theorem Flow.reserve_invariant {n θ s u} (f : @Flow n θ s u) (i : Fin n)
    (hinit : 50 ≤ s.x i .energy ∧ s.x i .energy ≤ 100)
    (hwork : ∀ t ∈ Icc s.time u.time,
      0 ≤ work θ s (f.path t) i t ∧ work θ s (f.path t) i t ≤ 500) :
    50 ≤ u.x i .energy ∧ u.x i .energy ≤ 100 := by
  have hhi := integral_upper_barrier f.positive.le (f.continuous i .energy) (f.integrable i .energy)
    (by simpa only [f.initial] using fun t ht => f.integral_eq t ht i .energy)
    (by simpa only [f.initial] using hinit.2)
    (fun t ht hcap => by dsimp [field]; linarith [(hwork t ht).1])
  have hlo := integral_upper_barrier (cap := -50) f.positive.le
    ((f.continuous i .energy).neg) ((f.integrable i .energy).neg)
    (by
      intro t ht
      have he := f.integral_eq t ht i .energy
      simp only [Pi.neg_apply]
      rw [intervalIntegral.integral_neg]
      simp only [f.initial]
      linarith)
    (by simpa only [Pi.neg_apply, f.initial] using neg_le_neg hinit.1)
    (fun t ht hcap => by dsimp only [Pi.neg_apply, field] at hcap ⊢; linarith [(hwork t ht).2])
  simp only [Pi.neg_apply] at hlo
  rw [f.final] at hhi hlo
  constructor <;> linarith

theorem BirthState.initial_gain_cap {n θ ε s} (hs : @BirthState n s) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) : s.x i (.z p) ≤ Real.log ((θ i).cap p) := by
  have hnom : 0 < nominalGain p ∧ nominalGain p ≤ 6 / 5 := by
    unfold nominalGain; split_ifs <;> norm_num
  have hsmall : (1 / 100000 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hcap : (12 / 5 : ℝ) ≤ (θ i).cap p := by
    have h := (hb.2 i p).1.1
    rcases hb.1 with he | he <;> rw [he] at h <;> linarith
  have hlognom := Real.log_le_log hnom.1 hnom.2
  have hlogcap := Real.log_le_log (by norm_num : (0 : ℝ) < 12 / 5) hcap
  have hlog : Real.log (12 / 5) = Real.log (6 / 5) + Real.log 2 := by
    rw [show (12 / 5 : ℝ) = (6 / 5) * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hz := ((hs.2.2 i).2.2.2.2 p).1.2
  linarith

theorem Execution.gain_birth_bounds {n θ ε route s u} (e : @Execution n θ route s u)
    (hs : BirthState s) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) :
    s.x i (.z p) ≤ u.x i (.z p) ∧ u.x i (.z p) ≤ Real.log ((θ i).cap p) :=
  ⟨e.gain_nondecreasing hb i p, e.gain_cap i p (hs.initial_gain_cap hb i p)⟩

theorem Execution.recovery_birth_bounds {n θ ε route s u} (e : @Execution n θ route s u)
    (hs : BirthState s) (hb : PhysicalBox θ ε) (i : Fin n) :
    (7999 / 100000 : ℝ) ≤ u.x i .b ∧ u.x i .b ≤ 11 / 10 := by
  have hinit := (hs.2.2 i).2.2.1
  have hmono := e.recovery_nondecreasing hb i
  have hcap := e.recovery_cap i (by linarith [hinit.2])
  constructor <;> linarith [hinit.1]

def Flow.workBound {n θ s u} (f : @Flow n θ s u) (i : Fin n) : Prop :=
  ∀ t ∈ Icc s.time u.time, 0 ≤ work θ s (f.path t) i t ∧ work θ s (f.path t) i t ≤ 500

def Execution.WorkBound {n θ route s u} (i : Fin n) : @Execution n θ route s u → Prop
  | .nil _ => True
  | .cons (.flow f) rest => f.workBound i ∧ rest.WorkBound i
  | .cons (.jump _) rest => rest.WorkBound i

theorem Execution.reserve_invariant {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hinit : 50 ≤ s.x i .energy ∧ s.x i .energy ≤ 100)
    (hw : e.WorkBound i) : 50 ≤ u.x i .energy ∧ u.x i .energy ≤ 100 := by
  induction e with
  | nil => exact hinit
  | cons step rest ih =>
    cases step with
    | flow f => exact ih (f.reserve_invariant i hinit hw.1) hw.2
    | jump j => exact ih (by simpa only [j.physical_continuous] using hinit) hw

theorem Flow.gain_cap_on {n θ s u} (f : @Flow n θ s u) (i : Fin n) (p : Port)
    (hinit : s.x i (.z p) ≤ Real.log ((θ i).cap p)) :
    ∀ t ∈ Icc s.time u.time, f.path t i (.z p) ≤ Real.log ((θ i).cap p) := by
  intro t ht
  have hsub : Icc s.time t ⊆ Icc s.time u.time := Icc_subset_Icc le_rfl ht.2
  apply integral_cap_barrier ht.1 ((f.continuous i (.z p)).mono hsub)
    ((f.integrable i (.z p)).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le f.positive.le]; exact hsub))
  · intro v hv
    simpa only [f.initial] using f.integral_eq v (hsub hv) i (.z p)
  · simpa only [f.initial] using hinit
  · intro v hv hcap
    simp [field, errorAct, not_lt.mpr hcap]

end KernelR.Hybrid
