import KernelR.HybridRecoveryTrace

/-! The first strong input at birth recovery leaves the actual cell ready for protected MARK. -/
namespace KernelR.Hybrid
open Set

structure MarkEntry {n} (s : Snapshot n) (i : Fin n) : Prop where
  slow : s.main i = .slow
  charge : 7 / 50 ≤ s.x i .q ∧ s.x i .q ≤ 1 / 4
  recovery : 7999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 8001 / 100000
  auxiliary : ∀ p, s.aux i p = .ready ∧ RestBand (s.x i (.m p))

structure LowRecoveryPulse {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) where
  trigger : MainTrigger e i
  slowStart : Snapshot n
  head : Execution θ route s slowStart
  slowSpan : Execution θ route slowStart u
  reconstruct : e = head.append slowSpan
  slow_states : slowSpan.AllStates (fun v => v.main i = .slow)
  slow_date : slowStart.time = trigger.afterFire.time + 1
  slow_charge : slowStart.x i .q = 1 / 4
  integral : slowSpan.accumulatedRecovery i = s.x i .b * (u.time - slowStart.time)
  emissions : e.emissionTimes i = [trigger.beforeFire.time]
  error_zero : ∀ p, e.ledger.error i p = 0
  mark_zero : ∀ p, e.ledger.mark i p = 0
  gain_preserved : ∀ p, u.x i (.z p) = s.x i (.z p)
  recovery_preserved : u.x i .b = s.x i .b
  mark_entry : MarkEntry u i
  raw_finished : ∀ p, u.raw i p = none

theorem exp_low_recovery_lower : (14 / 25 : ℝ) ≤ Real.exp (-(577 / 1000 : ℝ)) := by
  have h := Real.exp_bound (x := -(577 / 1000 : ℝ)) (n := 6) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith [(abs_sub_le_iff.mp h).2]

/-- The first strong input at birth recovery emits once and remains SLOW at
the next input. No MARK word or prepared recovery is assumed. -/
theorem Execution.first_strong_low_recovery_of_valid {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : ReadyCoordinates s i)
    (hb₀ : 7999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 8001 / 100000)
    (hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 15 / 2 ≤ u.time ∧ u.time ≤ s.time + 17 / 2) : Nonempty (LowRecoveryPulse e i) := by
  obtain ⟨tr⟩ := e.mid_gain_input_trigger hb hi i p hs.ready hs.charge hz (hs.auxiliary p).1 hr (hs.auxiliary p).2 ho hno (by linarith [ht.1])
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p (hs.auxiliary p).1 hr (hs.auxiliary p).2 (by linarith [ht.1])
  have hbstable := e.learned_recovery_unchanged cycle tr hb hv hr hno ho
    (fun q _ => ⟨(hs.auxiliary q).1,(hs.auxiliary q).2.2⟩)
  have hconst := e.recovery_constant_of_end hb i hbstable
  have hzero := cycle.error_zero_of_protected hv hr (hno p)
    (cycle.error_protected_by_trigger tr (by linarith [hb₀.2]))
  have hother : ∀ q, q ≠ p →
      (u.aux i q = .ready ∧ RestBand (u.x i (.m q))) ∧ u.x i (.z q) = s.x i (.z q) :=
    fun q hq => e.aux_no_input_rest_band i q (hs.auxiliary q).1 (hs.auxiliary q).2 (ho q hq) (hno q)
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
    · have hquiet := e.aux_ready_without_input_band i q (hs.auxiliary q).1 (hs.auxiliary q).2.2 (ho q hq) (hno q)
      exact e.mark_zero_aux i q .ready (by decide) (e.allStates_aux_flows i q .ready hquiet)
  rcases tr.rest.first_state_change (fun v => v.main i) .fast
    (fun f => congrFun f.main_fixed i) tr.fast_after with hfast | ⟨a,b,fastSpan,fastExit,slowSpan,hefast,hfast,ha,hbmode⟩
  · have h := tr.rest.fast_no_overrun i (tr.rest.allStates_main_flows i .fast hfast) tr.charge
    exact False.elim (by linarith [tr.deadline,ht.1])
  · have hguard := fastExit.fast_departure_guard i ha hbmode
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
    have hdu : u.time - b.time ≤ 17 / 2 - 1 - 3 / 10 := by rw [hbtime]; linarith [ht.2,tr.early]
    have hIUpper : slowSpan.accumulatedRecovery i ≤ (8001 / 100000 : ℝ) * (17 / 2 - 1 - 3 / 10) := by
      rw [hI]
      exact (mul_le_mul_of_nonneg_right hb₀.2 hd).trans (mul_le_mul_of_nonneg_left hdu (by norm_num))
    have hbudget := KernelR.low_recovery_not_returned hIUpper
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
    have hI577 : slowSpan.accumulatedRecovery i ≤ 577 / 1000 := by norm_num at hIUpper; linarith
    have heLower := Real.exp_le_exp.mpr (show -(577 / 1000 : ℝ) ≤ -slowSpan.accumulatedRecovery i by linarith)
    have heUpper : Real.exp (-slowSpan.accumulatedRecovery i) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hInon)
    have hqband : 7 / 50 ≤ u.x i .q ∧ u.x i .q ≤ 1 / 4 := by
      constructor <;> nlinarith [exp_low_recovery_lower]
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
      emissions := tr.only_emission_of_valid hv p hr ho hno
      error_zero := ?_
      mark_zero := hmark
      gain_preserved := hgain
      recovery_preserved := hbstable
      mark_entry := ?_
      raw_finished := e.allStates_final hraw (by linarith [ht.1])
    }⟩
    · calc
        e = tr.span.append (.cons (.jump tr.entry) tr.rest) := tr.reconstruct
        _ = _ := by rw [hefast]; simp only [head,Execution.append_assoc,Execution.append]
    · intro q
      have h := e.gain_balance i q
      rw [hgain q] at h
      linarith
    · refine ⟨slowSpan.allStates_final hslow,hqband,by rw [hbstable]; exact hb₀,?_⟩
      intro q
      by_cases hq : q = p
      · subst q; exact ⟨htarget.1,by rw [htarget.2]; norm_num [RestBand]⟩
      · exact (hother q hq).1

theorem Execution.first_strong_low_recovery {n θ ε route born s u} (e : @Execution n θ route s u)
    (past : Execution θ route born s) (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (i : Fin n) (p : Port) (hs : ReadyCoordinates s i)
    (hb₀ : 7999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 8001 / 100000)
    (hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 15 / 2 ≤ u.time ∧ u.time ≤ s.time + 17 / 2) : Nonempty (LowRecoveryPulse e i) := by
  exact e.first_strong_low_recovery_of_valid hb (past.upper_region hb hborn.upper_region)
    (past.raw_valid hborn.raw_valid) i p hs hb₀ hz hr ho hno ht

end KernelR.Hybrid
