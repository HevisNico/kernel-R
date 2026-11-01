import KernelR.HybridSlowProtection

/-! An actual prepared-cell READY return, using accumulated physical recovery. -/
namespace KernelR.Hybrid
open Set MeasureTheory

theorem Flow.accumulatedRecovery_lower {n θ ε s u} (f : @Flow n θ s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (B : ℝ) (hs : B ≤ s.x i .b) :
    B * (u.time - s.time) ≤ f.accumulatedRecovery i := by
  have h : (∫ _t in s.time..u.time, B) ≤ ∫ t in s.time..u.time, f.path t i .b := by
    apply intervalIntegral.integral_mono_on f.positive.le intervalIntegrable_const
      ((f.continuous i .b).intervalIntegrable_of_Icc f.positive.le)
    intro t ht
    exact hs.trans (f.recovery_nondecreasing hb i t ht)
  simpa only [Flow.accumulatedRecovery,intervalIntegral.integral_const,smul_eq_mul,mul_comm] using h

theorem Execution.accumulatedRecovery_lower {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (B : ℝ) (hs : B ≤ s.x i .b) :
    B * (u.time - s.time) ≤ e.accumulatedRecovery i := by
  induction e with
  | nil => simp [accumulatedRecovery]
  | @cons s v u move rest ih => cases move with
    | flow f =>
      have hf := f.accumulatedRecovery_lower hb i B hs
      have hnext := f.recovery_nondecreasing hb i _ ⟨f.positive.le,le_rfl⟩
      rw [f.final] at hnext
      have hrest := ih (hs.trans hnext)
      simp only [accumulatedRecovery]
      linarith
    | jump j => simpa only [accumulatedRecovery,j.time_unchanged] using ih (by simpa only [j.physical_continuous] using hs)

theorem Execution.slow_no_overrun {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (hm : e.MainFlows i .slow) (hq : s.x i .q = 1 / 4)
    (B : ℝ) (hB : 0 < B) (hs : B ≤ s.x i .b) : u.time ≤ s.time + Real.log (5 / 2) / B := by
  have hfloor := e.protected_main_floor i .slow (by decide) hm (by norm_num [mainFloor,hq])
  have hsol := e.slow_solution i hm
  rw [hq] at hsol
  have hacc : e.accumulatedRecovery i ≤ Real.log (5 / 2) := by
    have hd := duration_le_of_decay_floor (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1)
      (show 1 / 10 ≤ u.x i .q from hfloor) (by simpa only [neg_mul,one_mul] using hsol)
    norm_num at hd
    exact hd
  have hlo := e.accumulatedRecovery_lower hb i B hs
  have hdiv : u.time - s.time ≤ Real.log (5 / 2) / B := (le_div_iff₀ hB).mpr (by nlinarith)
  linarith

theorem Execution.slow_phase_completion {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (hs : s.main i = .slow) (hq : s.x i .q = 1 / 4)
    (B : ℝ) (hB : 0 < B) (hb₀ : B ≤ s.x i .b)
    (ht : s.time + Real.log (5 / 2) / B < u.time) :
    ∃ (v w : Snapshot n) (segment : Execution θ route s v) (exit : Jump route v w)
      (rest : Execution θ route w u),
      e = segment.append (.cons (.jump exit) rest) ∧
      segment.AllStates (fun v => v.main i = .slow) ∧ w.main i = .ready ∧
      w.x i .q = 1 / 10 ∧ w.time ≤ s.time + Real.log (5 / 2) / B := by
  rcases e.first_state_change (fun v => v.main i) .slow
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · have hlate := e.slow_no_overrun hb i (e.allStates_main_flows i .slow h) hq B hB hb₀
    exact False.elim (not_lt_of_ge hlate ht)
  · have hbound := segment.slow_no_overrun hb i (segment.allStates_main_flows i .slow hstates) hq B hB hb₀
    exact ⟨v,w,segment,exit,rest,he,hstates,exit.slow_main_departure i hv hw,
      by rw [exit.physical_continuous,exit.slow_departure_guard i hv hw],
      by rw [exit.time_unchanged]; exact hbound⟩

theorem Execution.append_assoc {n θ route s v w u}
    (a : @Execution n θ route s v) (b : Execution θ route v w) (c : Execution θ route w u) :
    (a.append b).append c = a.append (b.append c) := by
  induction a with
  | nil => rfl
  | cons move rest ih => simp only [append,ih]

structure ReadyReturn {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) where
  beforeReturn : Snapshot n
  afterReturn : Snapshot n
  span : Execution θ route s beforeReturn
  exit : Jump route beforeReturn afterReturn
  rest : Execution θ route afterReturn u
  reconstruct : e = span.append (.cons (.jump exit) rest)
  ready_after : afterReturn.main i = .ready
  charge_after : afterReturn.x i .q = 1 / 10
  raw_after : ∀ p, afterReturn.raw i p = none
  date : afterReturn.time < s.time + 6990787 / 1000000

/-- The physical SLOW comparison and the actual FAST exit supply a READY
return before the next 7.5-gap input. Recovery may increase during the trace. -/
theorem MainTrigger.ready_return_of_valid {n θ ε route s u i} {e : @Execution n θ route s u}
    (tr : MainTrigger e i) (hv : RawValid s)
    (hb : PhysicalBox θ ε) (hb₀ : 17999 / 100000 ≤ s.x i .b)
    (p : Port) (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15 / 2 ≤ u.time) : Nonempty (ReadyReturn e i) := by
  have hrstate := e.raw_expired_states i s.time hv
    (fun q => by
      by_cases hq : q = p
      · subst q; exact Or.inr hr
      · exact Or.inl (ho q hq)) hno
  have hstates := hrstate
  rw [tr.reconstruct,Execution.allStates_append] at hstates
  rcases tr.rest.first_state_change (fun v => v.main i) .fast
    (fun f => congrFun f.main_fixed i) tr.fast_after with hfast | ⟨v,w,fastSpan,fastExit,slowRest,hefast,hfast,hv,hw⟩
  · have h := tr.rest.fast_no_overrun i (tr.rest.allStates_main_flows i .fast hfast) tr.charge
    exact False.elim (by linarith [tr.deadline])
  · have hguard := fastExit.fast_departure_guard i hv hw
    have hfd := fastSpan.fast_duration i (fastSpan.allStates_main_flows i .fast hfast) tr.charge hguard.1
    have hwtime : w.time = tr.afterFire.time + 1 := by rw [fastExit.time_unchanged]; linarith
    have hqslow : w.x i .q = 1 / 4 := by rw [fastExit.physical_continuous,hguard.1]
    have hbfire : (17999 / 100000 : ℝ) ≤ tr.afterFire.x i .b := by
      rw [tr.entry.physical_continuous]; exact hb₀.trans (tr.span.recovery_nondecreasing hb i)
    have hbslow : (17999 / 100000 : ℝ) ≤ w.x i .b := by
      rw [fastExit.physical_continuous]; exact hbfire.trans (fastSpan.recovery_nondecreasing hb i)
    have hreturn := KernelR.stable_return_bound (b := (17999 / 100000 : ℝ))
      (f := tr.afterFire.time - s.time) le_rfl (by linarith [tr.deadline])
    have hbound : w.time + Real.log (5 / 2) / (17999 / 100000) < s.time + 6990787 / 1000000 := by
      rw [hwtime]; linarith
    obtain ⟨a,b,slowSpan,slowExit,quietRest,heslow,hslow,hbready,hbq,hbtime⟩ :=
      slowRest.slow_phase_completion hb i hguard.2 hqslow (17999 / 100000) (by norm_num) hbslow (by linarith)
    have hslowRaw := hstates.2.2
    rw [hefast,Execution.allStates_append] at hslowRaw
    have hquietRaw := hslowRaw.2.2
    rw [heslow,Execution.allStates_append] at hquietRaw
    have hraw_b := quietRest.allStates_initial hquietRaw.2.2
    have hafterRaw : s.time + 1 < b.time := by
      have hbtime' := slowSpan.time_monotone
      rw [← slowExit.time_unchanged] at hbtime'
      rw [hwtime] at hbtime'
      linarith [tr.early]
    let head := tr.span.append (.cons (.jump tr.entry) (fastSpan.append (.cons (.jump fastExit) slowSpan)))
    refine ⟨⟨a,b,head,slowExit,quietRest,?_,hbready,hbq,hraw_b hafterRaw,by linarith⟩⟩
    calc
      e = tr.span.append (.cons (.jump tr.entry) tr.rest) := tr.reconstruct
      _ = _ := by rw [hefast,heslow]; simp only [head,Execution.append_assoc,Execution.append]

theorem MainTrigger.ready_return {n θ ε route born s u i} {e : @Execution n θ route s u}
    (tr : MainTrigger e i) (past : Execution θ route born s) (hborn : BirthState born)
    (hb : PhysicalBox θ ε) (hb₀ : 17999 / 100000 ≤ s.x i .b)
    (p : Port) (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15 / 2 ≤ u.time) : Nonempty (ReadyReturn e i) := by
  exact tr.ready_return_of_valid (past.raw_valid hborn.raw_valid) hb hb₀ p hr ho hno ht

theorem ReadyReturn.final_ready {n θ route s u i} {e : @Execution n θ route s u}
    (ret : ReadyReturn e i) (hno : ∀ p, NoArrivalAt e i p) :
    u.main i = .ready ∧ u.x i .q = 1 / 10 := by
  have hrest : ∀ p, NoArrivalAt ret.rest i p := by
    intro p
    have h := hno p
    rw [ret.reconstruct,Execution.noArrivalAt_append] at h
    exact fun d hd => h.2 d (List.mem_append_right _ hd)
  have hquiet := ret.rest.ready_without_input i ret.ready_after ret.charge_after.le ret.raw_after hrest
  have hraw : ∀ p, ret.rest.RawAbsent i p := fun p =>
    (ret.rest.raw_absent_of_no_arrival i p (ret.raw_after p) (hrest p)).2
  refine ⟨ret.rest.allStates_final hquiet,?_⟩
  have hq := ret.rest.ready_no_current_solution i (ret.rest.allStates_main_flows i .ready hquiet) hraw
  simpa only [ret.charge_after,sub_self,zero_mul,add_zero] using hq

end KernelR.Hybrid
