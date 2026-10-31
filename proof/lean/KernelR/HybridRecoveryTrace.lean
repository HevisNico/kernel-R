import KernelR.HybridMidGainInput
import KernelR.HybridSilentReturn

/-! Actual recovery envelopes and accumulated SLOW-clock budgets. -/
namespace KernelR.Hybrid
open Set MeasureTheory

theorem Flow.recovery_le_final {n θ ε s u} (f : @Flow n θ s u) (hb : PhysicalBox θ ε) (i : Fin n) :
    ∀ t ∈ Icc s.time u.time, f.path t i .b ≤ u.x i .b := by
  intro t ht
  have ha : ∀ᵐ v ∂volume.restrict (Ioc s.time u.time), 0 ≤ field θ s (f.path v) v i .b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact Finset.sum_nonneg (fun p _ => f.mark_act_nonnegative hb i p ⟨hv.1.le,hv.2⟩)
  have hi := intervalIntegral.integral_mono_interval (μ := volume)
    (f := fun v => field θ s (f.path v) v i .b) le_rfl ht.1 ht.2 ha (f.integrable i .b)
  have he := f.integral_eq t ht i .b
  have hu := f.integral_eq u.time ⟨f.positive.le,le_rfl⟩ i .b
  rw [f.final] at hu
  linarith

theorem Flow.recovery_constant_of_end {n θ ε s u} (f : @Flow n θ s u) (hb : PhysicalBox θ ε)
    (i : Fin n) (he : u.x i .b = s.x i .b) :
    ∀ t ∈ Icc s.time u.time, f.path t i .b = s.x i .b := by
  intro t ht
  exact le_antisymm ((f.recovery_le_final hb i t ht).trans_eq he) (f.recovery_nondecreasing hb i t ht)

theorem Execution.recovery_constant_of_end {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (he : u.x i .b = s.x i .b) :
    e.AllStates (fun v => v.x i .b = s.x i .b) ∧
      e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b = s.x i .b) := by
  induction e with
  | nil => exact ⟨rfl,trivial⟩
  | @cons s v u move rest ih => cases move with
    | flow f =>
      have hlo := f.recovery_nondecreasing hb i _ ⟨f.positive.le,le_rfl⟩
      rw [f.final] at hlo
      have hhi := rest.recovery_nondecreasing hb i
      have hv : v.x i .b = s.x i .b := le_antisymm (hhi.trans_eq he) hlo
      have hrest := ih (by rw [he,hv])
      refine ⟨⟨rfl,?_⟩,⟨f.recovery_constant_of_end hb i hv,?_⟩⟩
      · simpa only [hv] using hrest.1
      · simpa only [hv] using hrest.2
    | jump j =>
      have hrest := ih (by simpa only [j.physical_continuous] using he)
      exact ⟨⟨rfl,by simpa only [j.physical_continuous] using hrest.1⟩,
        by simpa only [AllFlows,j.physical_continuous] using hrest.2⟩

theorem Flow.accumulatedRecovery_of_constant {n θ s u} (f : @Flow n θ s u)
    (i : Fin n) (B : ℝ) (h : ∀ t ∈ Icc s.time u.time, f.path t i .b = B) :
    f.accumulatedRecovery i = B * (u.time - s.time) := by
  unfold Flow.accumulatedRecovery
  have hi : (∫ t in s.time..u.time, f.path t i .b) = ∫ _t in s.time..u.time, B := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact h t (by simpa only [uIcc_of_le f.positive.le] using ht)
  rw [hi,intervalIntegral.integral_const,smul_eq_mul]
  ring

theorem Execution.accumulatedRecovery_of_constant {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (B : ℝ)
    (h : e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b = B)) :
    e.accumulatedRecovery i = B * (u.time - s.time) := by
  induction e with
  | nil => simp [accumulatedRecovery]
  | @cons s v u move rest ih => cases move with
    | flow f =>
      rw [accumulatedRecovery,f.accumulatedRecovery_of_constant i B h.1,ih h.2]
      ring
    | jump j => simpa only [accumulatedRecovery,j.time_unchanged] using ih h

theorem Execution.accumulatedRecovery_append {n θ route s v u}
    (segment : @Execution n θ route s v) (rest : Execution θ route v u) (i : Fin n) :
    (segment.append rest).accumulatedRecovery i = segment.accumulatedRecovery i + rest.accumulatedRecovery i := by
  induction segment with
  | nil => simp [append,accumulatedRecovery]
  | cons move tail ih => cases move <;> simp [append,accumulatedRecovery,ih,add_assoc]

theorem Flow.accumulatedRecovery_nonnegative {n θ ε s u} (f : @Flow n θ s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (hs : 0 ≤ s.x i .b) : 0 ≤ f.accumulatedRecovery i :=
  intervalIntegral.integral_nonneg f.positive.le (fun t ht => hs.trans (f.recovery_nondecreasing hb i t ht))

theorem Execution.accumulatedRecovery_nonnegative {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (hs : 0 ≤ s.x i .b) : 0 ≤ e.accumulatedRecovery i := by
  induction e with
  | nil => exact le_rfl
  | @cons s v u move rest ih => cases move with
    | flow f =>
      have hnext := f.recovery_nondecreasing hb i _ ⟨f.positive.le,le_rfl⟩
      rw [f.final] at hnext
      exact add_nonneg (f.accumulatedRecovery_nonnegative hb i hs) (ih (hs.trans hnext))
    | jump j => simpa only [accumulatedRecovery] using ih (by simpa only [j.physical_continuous] using hs)

theorem Execution.slow_exit_accumulation {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (hm : e.MainFlows i .slow) (hs : s.x i .q = 1 / 4) (hu : u.x i .q = 1 / 10) :
    e.accumulatedRecovery i = Real.log (5 / 2) := by
  have he := e.slow_solution i hm
  rw [hs,hu] at he
  have hex : Real.exp (-e.accumulatedRecovery i) = (2 / 5 : ℝ) := by linarith
  have href : Real.exp (-Real.log (5 / 2)) = (2 / 5 : ℝ) := by
    rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)]; norm_num
  exact neg_injective (Real.exp_injective (hex.trans href.symm))

/-- No first SLOW departure can occur before its recovery budget is reached.
The integral includes the actual continuation, rather than a supplied mode word. -/
theorem Execution.slow_stays_of_budget {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (hs : s.main i = .slow) (hq : s.x i .q = 1 / 4)
    (hb₀ : 0 ≤ s.x i .b) (hi : e.accumulatedRecovery i < Real.log (5 / 2)) :
    e.AllStates (fun v => v.main i = .slow) := by
  rcases e.first_state_change (fun v => v.main i) .slow
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact h
  · have hg := exit.slow_departure_guard i hv hw
    have hacc := segment.slow_exit_accumulation i (segment.allStates_main_flows i .slow hstates) hq hg
    have hwpos : 0 ≤ w.x i .b := by
      rw [exit.physical_continuous]; exact hb₀.trans (segment.recovery_nondecreasing hb i)
    have hrest := rest.accumulatedRecovery_nonnegative hb i hwpos
    have hbudget := hi
    rw [he,Execution.accumulatedRecovery_append] at hbudget
    simp only [accumulatedRecovery] at hbudget
    linarith

end KernelR.Hybrid
