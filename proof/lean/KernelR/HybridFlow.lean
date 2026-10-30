import KernelR.Refinement
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Solutions derived from integral hybrid flows. No closed-form trajectory is
assumed by the solution lemmas. Protocol reachability is a separate obligation. -/
namespace KernelR.Hybrid
open MeasureTheory Set Filter
open scoped Topology

/-- FTC on each right-hand neighborhood, including the left endpoint. -/
theorem right_derivative_of_integral {y g : ℝ → ℝ} {s u x : ℝ}
    (hg : ContinuousOn g (Icc s u))
    (hy : ∀ t ∈ Icc s u, y t = y s + ∫ v in s..t, g v)
    (hx : x ∈ Ico s u) : HasDerivWithinAt y (g x) (Ici x) x := by
  have hn : Icc s u ∈ 𝓝[Ici x] x := Icc_mem_nhdsGE_of_mem hx
  have hi : IntervalIntegrable g volume s x :=
    (hg.mono (Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable_of_Icc hx.1
  have hn' : Icc s u ∈ 𝓝[Ioi x] x := (nhdsWithin_mono x Ioi_subset_Ici_self) hn
  have hm : StronglyMeasurableAtFilter g (𝓝[Ioi x] x) volume :=
    ⟨Icc s u, hn', hg.aestronglyMeasurable measurableSet_Icc⟩
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (s := Ici x) (t := Ioi x) hi hm
    ((hg x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin hn')
  apply (hd.const_add (y s)).congr_of_eventuallyEq
  · filter_upwards [hn] with t ht
    exact hy t ht
  · exact hy x ⟨hx.1, hx.2.le⟩

/-- Uniqueness for the scalar constant-rate integral equation, up to both ends. -/
theorem decay_of_integral {y : ℝ → ℝ} {s u rate : ℝ}
    (hc : ContinuousOn y (Icc s u))
    (hy : ∀ t ∈ Icc s u, y t = y s + ∫ v in s..t, -rate * y v) :
    ∀ t ∈ Icc s u, y t = y s * Real.exp (-rate * (t - s)) := by
  let F : ℝ → ℝ := fun t => y t * Real.exp (rate * (t - s))
  have hFc : ContinuousOn F (Icc s u) := hc.mul (by fun_prop)
  have hFd : ∀ x ∈ Ico s u, HasDerivWithinAt F 0 (Ici x) x := by
    intro x hx
    have hd := right_derivative_of_integral (hc.const_mul (-rate)) hy hx
    have he := ((((hasDerivAt_id x).sub_const s).const_mul rate).exp).hasDerivWithinAt (s := Ici x)
    convert hd.mul he using 1
    · rfl
    · dsimp; ring
  intro t ht
  have h := constant_of_has_deriv_right_zero hFc hFd t ht
  have h' : y t * Real.exp (rate * (t - s)) = y s := by simpa [F] using h
  have hmul := congrArg (fun z : ℝ => z * Real.exp (-rate * (t - s))) h'
  have he : Real.exp (rate * (t - s)) * Real.exp (-rate * (t - s)) = 1 := by
    rw [← Real.exp_add, show rate * (t - s) + -rate * (t - s) = 0 by ring, Real.exp_zero]
  simpa only [mul_assoc, he, mul_one] using hmul

theorem Flow.fast_solution {n θ s u} (f : @Flow n θ s u) (i : Fin n)
    (hm : s.main i = .fast) :
    ∀ t ∈ Icc s.time u.time,
      f.path t i .q = s.x i .q * Real.exp (-a * (t - s.time)) := by
  have hi : ∀ t ∈ Icc s.time u.time,
      f.path t i .q = f.path s.time i .q + ∫ v in s.time..t, -a * f.path v i .q := by
    intro t ht
    simpa [f.initial, field, hm] using f.integral_eq t ht i .q
  simpa only [f.initial] using decay_of_integral (f.continuous i .q) hi

/-- All three protected auxiliary modes use their actual fabrication rate. -/
theorem Flow.aux_decay_solution {n θ s u} (f : @Flow n θ s u) (i : Fin n) (p : Port)
    (hm : s.aux i p ≠ .ready) :
    ∀ t ∈ Icc s.time u.time,
      f.path t i (.m p) = s.x i (.m p) *
        Real.exp (-(match s.aux i p with
          | .ready => 0 | .mark => (θ i).lm p | .silent => (θ i).ls p | .error => (θ i).le p) *
          (t - s.time)) := by
  let rate := match s.aux i p with
    | .ready => 0 | .mark => (θ i).lm p | .silent => (θ i).ls p | .error => (θ i).le p
  have hd (v : ℝ) : field θ s (f.path v) v i (.m p) = -rate * f.path v i (.m p) := by
    rw [field, ite_eq_right hm]
    dsimp [rate]
    cases ha : s.aux i p <;> simp_all [auxDrain, neg_mul]
  have hi := fun t ht => f.integral_eq t ht i (.m p)
  simp_rw [hd] at hi
  simpa only [f.initial] using decay_of_integral (f.continuous i (.m p)) (by
    simpa only [f.initial] using hi)

/-- Uniqueness with a continuous time-varying rate. In particular, SLOW
uses the accumulated actual recovery, including finite MARK profiles. -/
theorem variable_decay_of_integral {y rate : ℝ → ℝ} {s u : ℝ} (hsu : s ≤ u)
    (hc : ContinuousOn y (Icc s u)) (hr : ContinuousOn rate (Icc s u))
    (hy : ∀ t ∈ Icc s u, y t = y s + ∫ v in s..t, -rate v * y v) :
    ∀ t ∈ Icc s u, y t = y s * Real.exp (-(∫ v in s..t, rate v)) := by
  let B : ℝ → ℝ := fun t => ∫ v in s..t, rate v
  have hBc : ContinuousOn B (Icc s u) := by
    simpa only [uIcc_of_le hsu] using
      intervalIntegral.continuousOn_primitive_interval'
        (hr.intervalIntegrable_of_Icc hsu) (left_mem_uIcc : s ∈ uIcc s u)
  have hBd : ∀ x ∈ Ico s u, HasDerivWithinAt B (rate x) (Ici x) x := by
    intro x hx
    exact right_derivative_of_integral hr (by simp [B]) hx
  let F : ℝ → ℝ := fun t => y t * Real.exp (B t)
  have hFc : ContinuousOn F (Icc s u) := hc.mul (Real.continuous_exp.comp_continuousOn hBc)
  have hFd : ∀ x ∈ Ico s u, HasDerivWithinAt F 0 (Ici x) x := by
    intro x hx
    have hd := right_derivative_of_integral ((hr.neg).mul hc) hy hx
    exact (hd.mul (hBd x hx).exp).congr_deriv (by dsimp; ring)
  intro t ht
  have h := constant_of_has_deriv_right_zero hFc hFd t ht
  have h' : y t * Real.exp (B t) = y s := by simpa [F, B] using h
  have hm := congrArg (fun z : ℝ => z * Real.exp (-B t)) h'
  have he : Real.exp (B t) * Real.exp (-B t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  simpa only [mul_assoc, he, mul_one] using hm

theorem Flow.slow_solution {n θ s u} (f : @Flow n θ s u) (i : Fin n)
    (hm : s.main i = .slow) :
    ∀ t ∈ Icc s.time u.time,
      f.path t i .q = s.x i .q * Real.exp (-(∫ v in s.time..t, f.path v i .b)) := by
  have hi : ∀ t ∈ Icc s.time u.time,
      f.path t i .q = f.path s.time i .q +
        ∫ v in s.time..t, -f.path v i .b * f.path v i .q := by
    intro t ht
    simpa only [field, hm, f.initial] using f.integral_eq t ht i .q
  simpa only [f.initial] using variable_decay_of_integral f.positive.le
    (f.continuous i .q) (f.continuous i .b) hi

/-- The exit time follows from the solved ODE and observed positive endpoints. -/
theorem duration_of_decay {initial final rate duration : ℝ}
    (hi : 0 < initial) (hf : 0 < final) (hr : rate ≠ 0)
    (he : final = initial * Real.exp (-rate * duration)) :
    duration = Real.log (initial / final) / rate := by
  have h := congrArg Real.log he
  rw [Real.log_mul (ne_of_gt hi) (Real.exp_ne_zero _), Real.log_exp] at h
  apply (eq_div_iff hr).2
  rw [Real.log_div (ne_of_gt hi) (ne_of_gt hf)]
  linarith

theorem Flow.fast_duration {n θ s u} (f : @Flow n θ s u) (i : Fin n)
    (hm : s.main i = .fast) (hs : s.x i .q = 1) (hu : u.x i .q = 1 / 4) :
    u.time - s.time = 1 := by
  have he := f.fast_solution i hm u.time ⟨f.positive.le, le_rfl⟩
  rw [f.final, hs, hu] at he
  have h := duration_of_decay (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 4)
    (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 4))) he
  simpa [a, ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 4))] using h

theorem Flow.slow_return_integral {n θ s u} (f : @Flow n θ s u) (i : Fin n)
    (hm : s.main i = .slow) (hs : s.x i .q = 1 / 4) (hu : u.x i .q = 1 / 10) :
    (∫ v in s.time..u.time, f.path v i .b) = Real.log (5 / 2) := by
  have he := f.slow_solution i hm u.time ⟨f.positive.le, le_rfl⟩
  rw [f.final, hs, hu] at he
  have hex : Real.exp (-(∫ v in s.time..u.time, f.path v i .b)) = (2 / 5 : ℝ) := by
    linarith
  have href : Real.exp (-Real.log (5 / 2)) = (2 / 5 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)]; norm_num
  exact neg_injective (Real.exp_injective (hex.trans href.symm))

theorem positive_of_relative_box {ε nominal value : ℝ}
    (he : ε < 1) (hn : 0 < nominal) (h : InRelativeBox ε nominal value) : 0 < value := by
  have hp : 0 < nominal * (1 - ε) := mul_pos hn (by linarith)
  exact hp.trans_le h.1

theorem PhysicalBox.rates_positive {n θ ε} (h : @PhysicalBox n θ ε) (i : Fin n) (p : Port) :
    0 < (θ i).lm p ∧ 0 < (θ i).ls p ∧ 0 < (θ i).le p := by
  have he : ε < 1 := by rcases h.1 with rfl | rfl <;> norm_num
  refine ⟨positive_of_relative_box he ?_ (h.2 i p).2.1,
    positive_of_relative_box he ?_ (h.2 i p).2.2.1,
    positive_of_relative_box he ?_ (h.2 i p).2.2.2.1⟩
  · exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  · exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  · exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

theorem Flow.mark_duration {n θ ε s u} (f : @Flow n θ s u) (i : Fin n) (p : Port)
    (hb : PhysicalBox θ ε) (hm : s.aux i p = .mark)
    (hs : s.x i (.m p) = 1) (hu : u.x i (.m p) = 4 / 5) :
    u.time - s.time = Real.log (5 / 4) / (θ i).lm p := by
  have he := f.aux_decay_solution i p (by simp [hm]) u.time ⟨f.positive.le, le_rfl⟩
  simp only [hm, f.final, hs, hu] at he
  have h := duration_of_decay (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 4 / 5) (ne_of_gt (hb.rates_positive i p).1) he
  norm_num at h ⊢
  exact h

theorem Flow.silent_duration {n θ ε s u} (f : @Flow n θ s u) (i : Fin n) (p : Port)
    (hb : PhysicalBox θ ε) (hm : s.aux i p = .silent)
    (hs : s.x i (.m p) = 4 / 5) (hu : u.x i (.m p) = 1 / 10) :
    u.time - s.time = Real.log 8 / (θ i).ls p := by
  have he := f.aux_decay_solution i p (by simp [hm]) u.time ⟨f.positive.le, le_rfl⟩
  simp only [hm, f.final, hs, hu] at he
  have h := duration_of_decay (by norm_num : (0 : ℝ) < 4 / 5)
    (by norm_num : (0 : ℝ) < 1 / 10) (ne_of_gt (hb.rates_positive i p).2.1) he
  norm_num at h ⊢
  exact h

theorem Flow.error_duration {n θ ε s u} (f : @Flow n θ s u) (i : Fin n) (p : Port)
    (hb : PhysicalBox θ ε) (hm : s.aux i p = .error)
    (hs : s.x i (.m p) = 1 / 10) (hu : u.x i (.m p) = 1 / 40) :
    u.time - s.time = Real.log 4 / (θ i).le p := by
  have he := f.aux_decay_solution i p (by simp [hm]) u.time ⟨f.positive.le, le_rfl⟩
  simp only [hm, f.final, hs, hu] at he
  have h := duration_of_decay (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 40) (ne_of_gt (hb.rates_positive i p).2.2) he
  norm_num at h ⊢
  exact h

/-- A FAST flow cannot pass its first physical exit guard, even if its endpoint
was chosen for another cell's event. -/
theorem Flow.fast_no_overrun {n θ s u} (f : @Flow n θ s u) (i : Fin n)
    (hm : s.main i = .fast) (hs : s.x i .q = 1) : u.time ≤ s.time + 1 := by
  by_contra h
  have ht : s.time + 1 ∈ Ico s.time u.time := ⟨by linarith, lt_of_not_ge h⟩
  have hg := (f.guards (s.time + 1) ht).1 i
  rw [hm] at hg
  have he := f.fast_solution i hm (s.time + 1) ⟨ht.1, ht.2.le⟩
  have hex : f.path (s.time + 1) i .q = 1 / 4 := by
    rw [hs] at he
    have ht' : s.time + 1 - s.time = 1 := by ring
    simpa [ht', a, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)] using he
  rw [hex] at hg
  exact (lt_irrefl _ hg)

/-- The main mode of each actual positive-duration piece, with arbitrary legal
zero-time interleavings retained. This is not a pulse-case word. -/
def Flow.mainIs {n θ s u} (_f : @Flow n θ s u) (i : Fin n) (mode : MainMode) : Prop :=
  s.main i = mode

def Execution.MainFlows {n θ route s u} (i : Fin n) (mode : MainMode) :
    @Execution n θ route s u → Prop
  | .nil _ => True
  | .cons (.flow f) rest => f.mainIs i mode ∧ rest.MainFlows i mode
  | .cons (.jump _) rest => rest.MainFlows i mode

theorem Execution.fast_solution {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .fast) :
    u.x i .q = s.x i .q * Real.exp (-a * (u.time - s.time)) := by
  induction e with
  | nil => simp
  | @cons s u v step rest ih =>
    cases step with
    | flow f =>
      have hf := f.fast_solution i hm.1 u.time ⟨f.positive.le, le_rfl⟩
      rw [f.final] at hf
      rw [ih hm.2, hf, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    | jump j => rw [ih hm, j.physical_continuous, j.time_unchanged]

noncomputable def Flow.accumulatedRecovery {n θ s u} (f : @Flow n θ s u) (i : Fin n) : ℝ :=
  ∫ t in s.time..u.time, f.path t i .b

noncomputable def Execution.accumulatedRecovery {n θ route s u}
    (i : Fin n) : @Execution n θ route s u → ℝ
  | .nil _ => 0
  | .cons (.flow f) rest =>
      f.accumulatedRecovery i + rest.accumulatedRecovery i
  | .cons (.jump _) rest => rest.accumulatedRecovery i

theorem Execution.slow_solution {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .slow) :
    u.x i .q = s.x i .q * Real.exp (-e.accumulatedRecovery i) := by
  induction e with
  | nil => simp [Execution.accumulatedRecovery]
  | @cons s u v step rest ih =>
    cases step with
    | flow f =>
      have hf := f.slow_solution i hm.1 u.time ⟨f.positive.le, le_rfl⟩
      rw [f.final] at hf
      rw [ih hm.2, hf, mul_assoc, ← Real.exp_add]
      simp only [Execution.accumulatedRecovery, Flow.accumulatedRecovery]
      congr 2
      ring
    | jump j =>
      simp only [Execution.accumulatedRecovery]
      rw [ih hm, j.physical_continuous]

theorem Execution.fast_duration {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .fast) (hs : s.x i .q = 1) (hu : u.x i .q = 1 / 4) :
    u.time - s.time = 1 := by
  have he := e.fast_solution i hm
  rw [hs, hu] at he
  have h := duration_of_decay (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 4)
    (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 4))) he
  simpa [a, ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 4))] using h

/-- A genuine observed mode departure exposes the physical exit section. -/
theorem Jump.fast_departure_guard {n route s u} (j : @Jump n route s u) (i : Fin n)
    (hs : s.main i = .fast) (hu : u.main i ≠ .fast) :
    s.x i .q = 1 / 4 ∧ u.main i = .slow := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]

theorem Jump.fast_entry_guard {n route s u} (j : @Jump n route s u) (i : Fin n)
    (hs : s.main i ≠ .fast) (hu : u.main i = .fast) : u.x i .q = 1 := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem Jump.slow_entry_guard {n route s u} (j : @Jump n route s u) (i : Fin n)
    (hs : s.main i ≠ .slow) (hu : u.main i = .slow) : u.x i .q = 1 / 4 := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem Jump.slow_departure_guard {n route s u} (j : @Jump n route s u) (i : Fin n)
    (hs : s.main i = .slow) (hu : u.main i ≠ .slow) : s.x i .q = 1 / 10 := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem Jump.mark_entry_guard {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port)
    (hs : s.aux i p ≠ .mark) (hu : u.aux i p = .mark) : u.x i (.m p) = 1 := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem Jump.mark_departure_guard {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port)
    (hs : s.aux i p = .mark) (hu : u.aux i p ≠ .mark) : s.x i (.m p) = 4 / 5 := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem Jump.silent_entry_guard {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port)
    (hs : s.aux i p ≠ .silent) (hu : u.aux i p = .silent) : u.x i (.m p) = 4 / 5 := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem Jump.silent_departure_guard {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port)
    (hs : s.aux i p = .silent) (hu : u.aux i p ≠ .silent) : s.x i (.m p) = 1 / 10 := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem Jump.error_entry_guard {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port)
    (hs : s.aux i p ≠ .error) (hu : u.aux i p = .error) : u.x i (.m p) = 1 / 10 := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem Jump.error_departure_guard {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port)
    (hs : s.aux i p = .error) (hu : u.aux i p ≠ .error) : s.x i (.m p) = 1 / 40 := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

noncomputable def auxRate (θ : Parameters) (p : Port) : AuxMode → ℝ
  | .ready => 0 | .mark => θ.lm p | .silent => θ.ls p | .error => θ.le p

def Flow.auxIs {n θ s u} (_f : @Flow n θ s u) (i : Fin n) (p : Port) (mode : AuxMode) : Prop :=
  s.aux i p = mode

def Execution.AuxFlows {n θ route s u} (i : Fin n) (p : Port) (mode : AuxMode) :
    @Execution n θ route s u → Prop
  | .nil _ => True
  | .cons (.flow f) rest => f.auxIs i p mode ∧ rest.AuxFlows i p mode
  | .cons (.jump _) rest => rest.AuxFlows i p mode

/-- Auxiliary decay over the complete observed phase, including interleavings. -/
theorem Execution.aux_phase_solution {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (mode : AuxMode) (hne : mode ≠ .ready)
    (hm : e.AuxFlows i p mode) :
    u.x i (.m p) = s.x i (.m p) * Real.exp (-auxRate (θ i) p mode * (u.time - s.time)) := by
  induction e with
  | nil => simp
  | @cons s u v step rest ih =>
    cases step with
    | flow f =>
      have hmode : s.aux i p = mode := hm.1
      have hf := f.aux_decay_solution i p (by rw [hmode]; exact hne)
        u.time ⟨f.positive.le, le_rfl⟩
      have hf' : u.x i (.m p) = s.x i (.m p) *
          Real.exp (-auxRate (θ i) p mode * (u.time - s.time)) := by
        simpa only [f.final, hmode, auxRate] using hf
      rw [ih hm.2, hf', mul_assoc, ← Real.exp_add]
      congr 2
      ring
    | jump j => rw [ih hm, j.physical_continuous, j.time_unchanged]

/-- Entry/exit coordinates are derived from actual jumps, rather than supplied
as independent endpoint equalities. The span must be the observed FAST phase. -/
theorem guarded_fast_duration {n θ route before s u after}
    (entry : @Jump n route before s) (e : @Execution n θ route s u)
    (exit : Jump route u after) (i : Fin n)
    (hb : before.main i ≠ .fast) (hs : s.main i = .fast)
    (hu : u.main i = .fast) (ha : after.main i ≠ .fast)
    (hm : e.MainFlows i .fast) : u.time - s.time = 1 :=
  e.fast_duration i hm (entry.fast_entry_guard i hb hs) (exit.fast_departure_guard i hu ha).1

theorem guarded_error_duration {n θ ε route before s u after}
    (hb : PhysicalBox θ ε) (entry : @Jump n route before s) (e : @Execution n θ route s u)
    (exit : Jump route u after) (i : Fin n) (p : Port)
    (hbefore : before.aux i p ≠ .error) (hs : s.aux i p = .error)
    (hu : u.aux i p = .error) (hafter : after.aux i p ≠ .error)
    (hm : e.AuxFlows i p .error) : u.time - s.time = Real.log 4 / (θ i).le p := by
  have he := e.aux_phase_solution i p .error (by decide) hm
  rw [entry.error_entry_guard i p hbefore hs, exit.error_departure_guard i p hu hafter] at he
  have h := duration_of_decay (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 40) (ne_of_gt (hb.rates_positive i p).2.2) he
  norm_num [auxRate] at h
  exact h

theorem guarded_error_dose {n θ route before s u after}
    (entry : @Jump n route before s) (e : @Execution n θ route s u)
    (exit : Jump route u after) (i : Fin n) (p : Port)
    (hbefore : before.aux i p ≠ .error) (hs : s.aux i p = .error)
    (hu : u.aux i p = .error) (hafter : after.aux i p ≠ .error)
    (ho : e.ErrorExposed i p) : e.ledger.error i p = 3 / 5 :=
  e.full_error_of_open_endpoints i p ho (entry.error_entry_guard i p hbefore hs)
    (exit.error_departure_guard i p hu hafter)

theorem guarded_mark_dose {n θ route before s u after}
    (entry : @Jump n route before s) (e : @Execution n θ route s u)
    (exit : Jump route u after) (i : Fin n) (p : Port)
    (hbefore : before.aux i p ≠ .mark) (hs : s.aux i p = .mark)
    (hu : u.aux i p = .mark) (hafter : after.aux i p ≠ .mark)
    (ho : e.MarkExposed i p) : e.ledger.mark i p = 1 / 10 :=
  e.full_mark_of_open_endpoints i p ho (entry.mark_entry_guard i p hbefore hs)
    (exit.mark_departure_guard i p hu hafter)

/-- READY relaxation follows from the actual zero-input field; gains may vary. -/
theorem Flow.ready_no_current_solution {n θ s u} (f : @Flow n θ s u) (i : Fin n)
    (hm : s.main i = .ready) (hr : ∀ p, s.raw i p = none) :
    ∀ t ∈ Icc s.time u.time, f.path t i .q =
      1 / 10 + (s.x i .q - 1 / 10) * Real.exp (-(1 / 2) * (t - s.time)) := by
  let y : ℝ → ℝ := fun t => f.path t i .q - 1 / 10
  have hd (v : ℝ) : field θ s (f.path v) v i .q = -(1 / 2) * y v := by
    simp [field, hm, drive, current, hr, y]
    ring
  have hi : ∀ t ∈ Icc s.time u.time,
      y t = y s.time + ∫ v in s.time..t, -(1 / 2) * y v := by
    intro t ht
    have h := f.integral_eq t ht i .q
    simp_rw [hd] at h
    dsimp [y]; rw [f.initial]
    linarith
  have h := decay_of_integral ((f.continuous i .q).sub continuousOn_const) hi
  intro t ht
  have he := h t ht
  dsimp [y] at he
  rw [f.initial] at he
  linarith

theorem Flow.aux_ready_no_current_solution {n θ s u} (f : @Flow n θ s u) (i : Fin n) (p : Port)
    (hm : s.aux i p = .ready) (hr : s.raw i p = none) :
    ∀ t ∈ Icc s.time u.time, f.path t i (.m p) =
      1 / 40 + (s.x i (.m p) - 1 / 40) * Real.exp (-(1 / 2) * (t - s.time)) := by
  let y : ℝ → ℝ := fun t => f.path t i (.m p) - 1 / 40
  have hd (v : ℝ) : field θ s (f.path v) v i (.m p) = -(1 / 2) * y v := by
    simp [field, hm, current, hr, y]
    ring
  have hi : ∀ t ∈ Icc s.time u.time,
      y t = y s.time + ∫ v in s.time..t, -(1 / 2) * y v := by
    intro t ht
    have h := f.integral_eq t ht i (.m p)
    simp_rw [hd] at h
    dsimp [y]; rw [f.initial]
    linarith
  have h := decay_of_integral ((f.continuous i (.m p)).sub continuousOn_const) hi
  intro t ht
  have he := h t ht
  dsimp [y] at he
  rw [f.initial] at he
  linarith

theorem Flow.gain_constant_when_protected {n θ s u} (f : @Flow n θ s u) (i : Fin n) (p : Port)
    (hm : s.main i ≠ .ready) : ∀ t ∈ Icc s.time u.time, f.path t i (.z p) = s.x i (.z p) := by
  intro t ht
  simpa [field, errorAct, hm] using f.integral_eq t ht i (.z p)

theorem Flow.gain_constant_without_error {n θ s u} (f : @Flow n θ s u) (i : Fin n) (p : Port)
    (hm : s.aux i p ≠ .error) : ∀ t ∈ Icc s.time u.time, f.path t i (.z p) = s.x i (.z p) := by
  intro t ht
  simpa [field, errorAct, hm] using f.integral_eq t ht i (.z p)

theorem Flow.recovery_constant_when_ready {n θ s u} (f : @Flow n θ s u) (i : Fin n)
    (hm : s.main i = .ready) : ∀ t ∈ Icc s.time u.time, f.path t i .b = s.x i .b := by
  intro t ht
  simpa [field, markAct, hm] using f.integral_eq t ht i .b

theorem guarded_mark_duration {n θ ε route before s u after}
    (hb : PhysicalBox θ ε) (entry : @Jump n route before s) (e : @Execution n θ route s u)
    (exit : Jump route u after) (i : Fin n) (p : Port)
    (hbefore : before.aux i p ≠ .mark) (hs : s.aux i p = .mark)
    (hu : u.aux i p = .mark) (hafter : after.aux i p ≠ .mark)
    (hm : e.AuxFlows i p .mark) : u.time - s.time = Real.log (5 / 4) / (θ i).lm p := by
  have he := e.aux_phase_solution i p .mark (by decide) hm
  rw [entry.mark_entry_guard i p hbefore hs, exit.mark_departure_guard i p hu hafter] at he
  have h := duration_of_decay (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 4 / 5) (ne_of_gt (hb.rates_positive i p).1) he
  norm_num [auxRate] at h
  exact h

theorem guarded_silent_duration {n θ ε route before s u after}
    (hb : PhysicalBox θ ε) (entry : @Jump n route before s) (e : @Execution n θ route s u)
    (exit : Jump route u after) (i : Fin n) (p : Port)
    (hbefore : before.aux i p ≠ .silent) (hs : s.aux i p = .silent)
    (hu : u.aux i p = .silent) (hafter : after.aux i p ≠ .silent)
    (hm : e.AuxFlows i p .silent) : u.time - s.time = Real.log 8 / (θ i).ls p := by
  have he := e.aux_phase_solution i p .silent (by decide) hm
  rw [entry.silent_entry_guard i p hbefore hs, exit.silent_departure_guard i p hu hafter] at he
  have h := duration_of_decay (by norm_num : (0 : ℝ) < 4 / 5)
    (by norm_num : (0 : ℝ) < 1 / 10) (ne_of_gt (hb.rates_positive i p).2.1) he
  norm_num [auxRate] at h
  exact h

theorem guarded_slow_return_integral {n θ route before s u after}
    (entry : @Jump n route before s) (e : @Execution n θ route s u)
    (exit : Jump route u after) (i : Fin n)
    (hb : before.main i ≠ .slow) (hs : s.main i = .slow)
    (hu : u.main i = .slow) (ha : after.main i ≠ .slow)
    (hm : e.MainFlows i .slow) : e.accumulatedRecovery i = Real.log (5 / 2) := by
  have he := e.slow_solution i hm
  rw [entry.slow_entry_guard i hb hs, exit.slow_departure_guard i hu ha] at he
  have hex : Real.exp (-e.accumulatedRecovery i) = (2 / 5 : ℝ) := by linarith
  have href : Real.exp (-Real.log (5 / 2)) = (2 / 5 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)]; norm_num
  exact neg_injective (Real.exp_injective (hex.trans href.symm))

end KernelR.Hybrid
