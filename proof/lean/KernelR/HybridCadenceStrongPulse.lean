import KernelR.HybridHighGainTrigger
import KernelR.HybridLowRecovery
import KernelR.HybridCadenceRestRoot

/-! First strong cadence pulses retain their actual FAST exit and SLOW carry. -/
namespace KernelR.Hybrid
open Set

theorem cadence_three_dose_gain_bounds {z : ℝ}
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ z ∧
      z ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000) :
    9 / 5 ≤ Real.exp z ∧ Real.exp z ≤ 19 / 10 := by
  have hsmall : Real.exp (21 / 50 : ℝ) ≤ 19 / 12 := by
    have h := Real.exp_bound (x := (21 / 50 : ℝ)) (n := 2) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have hlarge : Real.exp (9 / 5 + 1 / 100000 : ℝ) ≤ 19 / 3 := by
    calc
      _ ≤ Real.exp (a + 21 / 50) := Real.exp_le_exp.mpr (by dsimp [a]; linarith [KernelR.log_four_bounds.1])
      _ = 4 * Real.exp (21 / 50 : ℝ) := by rw [Real.exp_add]; norm_num [a,Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      _ ≤ _ := by linarith
  refine ⟨(learned_gain_bounds hz.1 hz.2).1,?_⟩
  have h := Real.exp_le_exp.mpr hz.2
  rw [show Real.log (3 / 10) + 9 / 5 + 1 / 100000 =
    Real.log (3 / 10) + (9 / 5 + 1 / 100000) by ring,
    Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 3 / 10)] at h
  linarith

theorem readyPulse_cadence_strong_not_early {initial amplitude start t : ℝ}
    (hi : initial ≤ 3 / 10) (ha : amplitude ≤ 19 / 10)
    (ht : start ≤ t) (hu : t ≤ start + 3 / 10) : readyPulse initial amplitude start t < 1 := by
  have hd := sub_nonneg.mpr ht
  have hc := decay_upper (show initial - 1 / 10 ≤ (1 / 5 : ℝ) by linarith)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd
  have hp := mul_le_mul_of_nonneg_right ha (response_nonnegative hd)
  have hh := mul_le_mul_of_nonneg_left (response_mid_early_upper hd (by linarith))
    (by norm_num : (0 : ℝ) ≤ 19 / 10)
  unfold readyPulse
  linarith

/-- Broader positive residuals still admit the older 0.3 first-fire lower
bound at the actual three-dose gain, proved directly from its guard equation. -/
theorem Execution.cadence_strong_trigger {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (i : Fin n) (p : Port)
    (hm : s.main i = .ready)
    (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 3 / 10)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (ha : s.aux i p = .ready) (hr : s.raw i p = some s.time) (hx : RestBand (s.x i (.m p)))
    (ho : ∀ q, q ≠ p → s.raw i q = none) (hno : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 419 / 300 ≤ u.time) : Nonempty (MainTrigger e i) := by
  have hg := cadence_three_dose_gain_bounds hz
  obtain ⟨tr⟩ := e.high_gain_input_trigger hb hi i p hm ⟨hq.1,by linarith [hq.2]⟩
    ⟨hg.1,by linarith [hg.2]⟩ ha hr hx ho hno ht
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p ha hr hx ht
  have heq := tr.firing_equation cycle hr ho hno
  have hearly : s.time + 3 / 10 < tr.afterFire.time := by
    by_contra hn
    have htime : tr.beforeFire.time ≤ s.time + 3 / 10 := by
      rw [← tr.entry.time_unchanged]
      exact le_of_not_gt hn
    have hm := readyPulse_cadence_strong_not_early hq.2 hg.2 tr.span.time_monotone htime
    rw [heq] at hm
    linarith
  exact ⟨⟨tr.beforeFire,tr.afterFire,tr.span,tr.entry,tr.rest,tr.reconstruct,tr.ready_states,
    tr.fast_after,tr.charge,hearly,tr.deadline⟩⟩

structure CadenceStrongPulse {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) where
  trigger : MainTrigger e i
  slowStart : Snapshot n
  head : Execution θ route s slowStart
  slowSpan : Execution θ route slowStart u
  reconstruct : e = head.append slowSpan
  slow_states : slowSpan.AllStates (fun v => v.main i = .slow)
  slow_date : slowStart.time = trigger.afterFire.time + 1
  slow_charge : slowStart.x i .q = 1 / 4
  integral : slowSpan.accumulatedRecovery i = s.x i .b * (u.time - slowStart.time)
  charge_solution : u.x i .q = (1 / 4) * Real.exp (-s.x i .b * (u.time - trigger.afterFire.time - 1))
  charge : 1 / 10 < u.x i .q ∧ u.x i .q ≤ 1 / 4
  emissions : e.emissionTimes i = [trigger.beforeFire.time]
  error_zero : ∀ p, e.ledger.error i p = 0
  mark_zero : ∀ p, e.ledger.mark i p = 0
  gain_preserved : ∀ p, u.x i (.z p) = s.x i (.z p)
  recovery_preserved : u.x i .b = s.x i .b
  auxiliary : ∀ p, u.aux i p = .ready ∧ RestBand (u.x i (.m p))
  raw_finished : ∀ p, u.raw i p = none

theorem Execution.cadence_strong_pulse {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hm : s.main i = .ready)
    (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 3 / 10)
    (hb₀ : 0 ≤ s.x i .b ∧ s.x i .b ≤ 28001 / 100000)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 19 / 5 ≤ u.time ∧ u.time ≤ s.time + 21 / 5) :
    Nonempty (CadenceStrongPulse e i) := by
  have hi := hf.region
  obtain ⟨tr⟩ := e.cadence_strong_trigger hb hi i p hm hq hz (ha p).1 hr (ha p).2 ho hno (by linarith [ht.1])
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p (ha p).1 hr (ha p).2 (by linarith [ht.1])
  have hbstable := e.learned_recovery_unchanged cycle tr hb hv hr hno ho
    (fun q _ => ⟨(ha q).1,(ha q).2.2⟩)
  have hconst := e.recovery_constant_of_end hb i hbstable
  have hzero := cycle.error_zero_of_protected hv hr (hno p)
    (cycle.error_protected_by_trigger tr (by linarith [hb₀.2]))
  have hother : ∀ q, q ≠ p →
      (u.aux i q = .ready ∧ RestBand (u.x i (.m q))) ∧ u.x i (.z q) = s.x i (.z q) :=
    fun q hq => e.aux_no_input_rest_band i q (ha q).1 (ha q).2 (ho q hq) (hno q)
  have htarget := cycle.final_rest hv hr (hno p)
  have hgain : ∀ q, u.x i (.z q) = s.x i (.z q) := by
    intro q
    by_cases hq : q = p
    · subst q; exact hzero.2
    · exact (hother q hq).2
  have hmark : ∀ q, e.ledger.mark i q = 0 := by
    intro q
    by_cases hq : q = p
    · subst q; exact cycle.mark_zero_of_trigger tr hb hv hr (hno p)
    · have hquiet := e.aux_ready_without_input_band i q (ha q).1 (ha q).2.2 (ho q hq) (hno q)
      exact e.mark_zero_aux i q .ready (by decide) (e.allStates_aux_flows i q .ready hquiet)
  rcases tr.rest.first_state_change (fun v => v.main i) .fast
    (fun f => congrFun f.main_fixed i) tr.fast_after with hfast | ⟨a,b,fastSpan,fastExit,slowSpan,hefast,hfast,hamode,hbmode⟩
  · have h := tr.rest.fast_no_overrun i (tr.rest.allStates_main_flows i .fast hfast) tr.charge
    exact False.elim (by linarith [tr.deadline,ht.1])
  · have hguard := fastExit.fast_departure_guard i hamode hbmode
    have hfd := fastSpan.fast_duration i (fastSpan.allStates_main_flows i .fast hfast) tr.charge hguard.1
    have hbtime : b.time = tr.afterFire.time + 1 := by rw [fastExit.time_unchanged]; linarith
    have hqslow : b.x i .q = 1 / 4 := by rw [fastExit.physical_continuous,hguard.1]
    have hflowConst := hconst.2
    rw [tr.reconstruct,Execution.allFlows_append] at hflowConst
    have htailConst : tr.rest.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b = s.x i .b) := hflowConst.2
    rw [hefast,Execution.allFlows_append] at htailConst
    have hslowConst : slowSpan.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b = s.x i .b) := htailConst.2
    have hI := slowSpan.accumulatedRecovery_of_constant i (s.x i .b) hslowConst
    have hnon : 0 ≤ s.x i .b := by linarith [hb₀.1]
    have hd : 0 ≤ u.time - b.time := sub_nonneg.mpr slowSpan.time_monotone
    have hdu : u.time - b.time ≤ 21 / 5 - 1 - 3 / 10 := by rw [hbtime]; linarith [ht.2,tr.early]
    have hIUpper : slowSpan.accumulatedRecovery i ≤ (28001 / 100000 : ℝ) * (21 / 5 - 1 - 3 / 10) := by
      rw [hI]
      exact (mul_le_mul_of_nonneg_right hb₀.2 hd).trans (mul_le_mul_of_nonneg_left hdu (by norm_num))
    have hbudget : slowSpan.accumulatedRecovery i < Real.log (5 / 2) := by
      norm_num at hIUpper
      linarith [KernelR.log_recovery_bounds.1]
    have hbslow : 0 ≤ b.x i .b := by
      rw [fastExit.physical_continuous]
      have h1 := tr.span.recovery_nondecreasing hb i
      have h2 := fastSpan.recovery_nondecreasing hb i
      rw [tr.entry.physical_continuous] at h2
      linarith
    have hslow := slowSpan.slow_stays_of_budget hb i hguard.2 hqslow hbslow hbudget
    have hqsol := slowSpan.slow_solution i (slowSpan.allStates_main_flows i .slow hslow)
    rw [hqslow] at hqsol
    have hInon : 0 ≤ slowSpan.accumulatedRecovery i := by rw [hI]; exact mul_nonneg hnon hd
    have heLower : (2 / 5 : ℝ) < Real.exp (-slowSpan.accumulatedRecovery i) := by
      have h := Real.exp_lt_exp.mpr (neg_lt_neg hbudget)
      rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)] at h
      norm_num at h
      exact h
    have heUpper : Real.exp (-slowSpan.accumulatedRecovery i) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hInon)
    have hqband : 1 / 10 < u.x i .q ∧ u.x i .q ≤ 1 / 4 := by
      constructor <;> nlinarith
    have hqexact : u.x i .q = (1 / 4) * Real.exp (-s.x i .b * (u.time - tr.afterFire.time - 1)) := by
      rw [hqsol,hI,hbtime]
      congr 2
      ring
    have hraw := e.raw_expired_states i s.time hv
      (fun q => by
        by_cases hq : q = p
        · subst q; exact Or.inr hr
        · exact Or.inl (ho q hq)) hno
    let head := tr.span.append (.cons (.jump tr.entry) (fastSpan.append (.cons (.jump fastExit) (.nil _))))
    refine ⟨{
      trigger := tr
      slowStart := b
      head := head
      slowSpan := slowSpan
      reconstruct := ?_
      slow_states := hslow
      slow_date := hbtime
      slow_charge := hqslow
      integral := hI
      charge_solution := hqexact
      charge := hqband
      emissions := tr.only_emission_of_valid hv p hr ho hno
      error_zero := ?_
      mark_zero := hmark
      gain_preserved := hgain
      recovery_preserved := hbstable
      auxiliary := ?_
      raw_finished := e.allStates_final hraw (by linarith [ht.1])
    }⟩
    · calc
        e = tr.span.append (.cons (.jump tr.entry) tr.rest) := tr.reconstruct
        _ = _ := by rw [hefast]; simp only [head,Execution.append_assoc,Execution.append]
    · intro q
      have h := e.gain_balance i q
      rw [hgain q] at h
      linarith
    · intro q
      by_cases hq : q = p
      · subst q; exact ⟨htarget.1,by rw [htarget.2]; norm_num [RestBand]⟩
      · exact (hother q hq).1


/-- The first strong pulse at b≈0.18 leaves sufficient actual SLOW charge for
its following MARK input. No birth-recovery MarkEntry section is assumed. -/
theorem CadenceStrongPulse.first_strong_charge {n θ route s u i} {e : @Execution n θ route s u}
    (pulse : CadenceStrongPulse e i) (hb : s.x i .b ≤ 18001 / 100000)
    (ht : u.time ≤ s.time + 21 / 5) : 37 / 250 ≤ u.x i .q := by
  have he : (74 / 125 : ℝ) ≤ Real.exp (-(523 / 1000 : ℝ)) := by
    have h := Real.exp_bound (x := -(523 / 1000 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have hd : 0 ≤ u.time - pulse.trigger.afterFire.time - 1 := by
    have h := pulse.slowSpan.time_monotone
    rw [pulse.slow_date] at h
    linarith
  have hu : u.time - pulse.trigger.afterFire.time - 1 ≤ 29 / 10 := by
    linarith [pulse.trigger.early]
  have hI : s.x i .b * (u.time - pulse.trigger.afterFire.time - 1) ≤ 523 / 1000 := by
    have h := (mul_le_mul_of_nonneg_right hb hd).trans
      (mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 18001 / 100000))
    norm_num at h
    linarith
  have hex := Real.exp_le_exp.mpr (neg_le_neg hI)
  rw [pulse.charge_solution,neg_mul]
  linarith

/-- The first period-four strong case at the learned initial recovery. -/
theorem Execution.cadence_first_strong_pulse {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hm : s.main i = .ready)
    (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 3 / 10)
    (hbRange : 17999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 18001 / 100000)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 19 / 5 ≤ u.time ∧ u.time ≤ s.time + 21 / 5) :
    ∃ _pulse : CadenceStrongPulse e i, 37 / 250 ≤ u.x i .q := by
  obtain ⟨pulse⟩ := e.cadence_strong_pulse hb hf hv i p hm hq
    ⟨by linarith [hbRange.1],by linarith [hbRange.2]⟩ hz ha hr ho hno ht
  exact ⟨pulse,pulse.first_strong_charge hbRange.2 ht.2⟩

/-- At exact resting charge, the selected physical trigger uses this cell's
own real response root. This identity is not used for a positive residual. -/
theorem MainTrigger.cadence_rest_firing_bounds {n θ ε route s u i} {e : @Execution n θ route s u}
    (tr : MainTrigger e i) (hb : PhysicalBox θ ε) (hi : UpperRegion s) (p : Port)
    (hq : s.x i .q = 1 / 10)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (ha : s.aux i p = .ready ∧ RestBand (s.x i (.m p)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 419 / 300 ≤ u.time) :
    s.time + 13 / 20 < tr.afterFire.time ∧ tr.afterFire.time < s.time + 33 / 50 := by
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p ha.1 hr ha.2 ht
  have hroot := tr.firing_equation cycle hr ho hno
  rw [hq] at hroot
  have hshift : readyPulse (1 / 10) (Real.exp (s.x i (.z p))) 0
      (tr.beforeFire.time - s.time) = 1 := by
    simpa only [readyPulse,sub_zero] using hroot
  have hlo : s.time + 3 / 10 < tr.beforeFire.time := by
    simpa only [tr.entry.time_unchanged] using tr.early
  have hhi : tr.beforeFire.time < s.time + 9 / 10 := by
    simpa only [tr.entry.time_unchanged] using tr.deadline
  have hg := cadence_three_dose_gain_bounds hz
  have heq := restLatency_unique ⟨hg.1,by linarith [hg.2]⟩
    (t := tr.beforeFire.time - s.time) ⟨by linarith,by linarith⟩ hshift
  have hbound := restLatency_three_doses_bounds hz.1 hz.2
  rw [tr.entry.time_unchanged]
  constructor <;> linarith

/-- The subsequent exact-rest strong input at b≈0.28 lands inside the
numerical SLOW band needed by the mixed MARK/ERROR input. -/
theorem CadenceStrongPulse.second_strong_charge {n θ route s u i} {e : @Execution n θ route s u}
    (pulse : CadenceStrongPulse e i)
    (hb : 27999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 28001 / 100000)
    (hf : s.time + 13 / 20 < pulse.trigger.afterFire.time ∧
      pulse.trigger.afterFire.time < s.time + 33 / 50)
    (ht : s.time + 19 / 5 ≤ u.time ∧ u.time ≤ s.time + 21 / 5) :
    61 / 500 ≤ u.x i .q ∧ u.x i .q ≤ 7 / 50 := by
  have helo : (61 / 125 : ℝ) ≤ Real.exp (-(143 / 200 : ℝ)) := by
    have h := Real.exp_bound (x := -(143 / 200 : ℝ)) (n := 8) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have hehi : Real.exp (-(599 / 1000 : ℝ)) ≤ 14 / 25 := by
    have h := Real.exp_bound (x := -(599 / 1000 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  have hdlo : (107 / 50 : ℝ) ≤ u.time - pulse.trigger.afterFire.time - 1 := by linarith [hf.2,ht.1]
  have hdhi : u.time - pulse.trigger.afterFire.time - 1 ≤ (51 / 20 : ℝ) := by linarith [hf.1,ht.2]
  have hd : 0 ≤ u.time - pulse.trigger.afterFire.time - 1 := by linarith
  have hIlo : (599 / 1000 : ℝ) ≤ s.x i .b * (u.time - pulse.trigger.afterFire.time - 1) := by
    have h := (mul_le_mul_of_nonneg_left hdlo (by norm_num : (0 : ℝ) ≤ 27999 / 100000)).trans
      (mul_le_mul_of_nonneg_right hb.1 hd)
    norm_num at h
    linarith
  have hIhi : s.x i .b * (u.time - pulse.trigger.afterFire.time - 1) ≤ (143 / 200 : ℝ) := by
    have h := (mul_le_mul_of_nonneg_right hb.2 hd).trans
      (mul_le_mul_of_nonneg_left hdhi (by norm_num : (0 : ℝ) ≤ 28001 / 100000))
    norm_num at h
    linarith
  have hexlo := Real.exp_le_exp.mpr (neg_le_neg hIhi)
  have hexhi := Real.exp_le_exp.mpr (neg_le_neg hIlo)
  rw [pulse.charge_solution,neg_mul]
  constructor <;> linarith

/-- The second strong cadence case starts at exact rest, so its own root
bounds give the following mixed-input charge interval. -/
theorem Execution.cadence_second_strong_pulse {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hm : s.main i = .ready) (hq : s.x i .q = 1 / 10)
    (hbRange : 27999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 28001 / 100000)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 19 / 5 ≤ u.time ∧ u.time ≤ s.time + 21 / 5) :
    ∃ _pulse : CadenceStrongPulse e i, 61 / 500 ≤ u.x i .q ∧ u.x i .q ≤ 7 / 50 := by
  obtain ⟨pulse⟩ := e.cadence_strong_pulse hb hf hv i p hm (by rw [hq]; norm_num)
    ⟨by linarith [hbRange.1],hbRange.2⟩ hz ha hr ho hno ht
  have hfire := pulse.trigger.cadence_rest_firing_bounds hb hf.region p hq hz (ha p) hr ho hno (by linarith [ht.1])
  exact ⟨pulse,pulse.second_strong_charge hbRange hfire ht⟩

end KernelR.Hybrid
