import KernelR.HybridSlowMarkReturn
import KernelR.HybridProtectedPulse

namespace KernelR.Hybrid
open Set

theorem mark_only_log_margin :
    (28001 / 100000 : ℝ) * (419 / 300) < 9 / 23 ∧
      (9 / 23 : ℝ) ≤ Real.log (37 / 25) := by
  constructor
  · norm_num
  · have hbase := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 18 / 175)
    norm_num at hbase
    have hp : (193 / 175 : ℝ) ^ 4 ≤ 37 / 25 := by norm_num
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < (193 / 175 : ℝ) ^ 4) hp
    rw [Real.log_pow] at hl
    norm_num at hl
    linarith

/-- The one-input recovery budget proves protection through ERROR, before
using any MARK dose or actuation exposure. -/
theorem Execution.slow_mark_only_window {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (hs : s.main i = .slow)
    (hq : 37 / 250 ≤ s.x i .q)
    (hb : e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time,
      f.path t i .b ≤ 28001 / 100000)) :
    e.AllStates (fun v => v.time ≤ s.time + 419 / 300 → v.main i = .slow) := by
  have hqin : 0 < s.x i .q := by linarith
  have hlog : (9 / 23 : ℝ) ≤ Real.log (s.x i .q / (1 / 10)) := by
    apply mark_only_log_margin.2.trans (Real.log_le_log (by norm_num) ?_)
    linarith
  rcases e.first_state_change (fun v => v.main i) .slow
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact e.allStates_mono (fun v hv _ => hv) h
  · have hbound := hb
    rw [he,Execution.allFlows_append] at hbound
    have hI := segment.accumulatedRecovery_of_upper i (28001 / 100000) hbound.1
    have hsol := segment.slow_solution i (segment.allStates_main_flows i .slow hstates)
    rw [exit.slow_departure_guard i hv hw] at hsol
    have hi := duration_of_decay hqin (by norm_num : (0 : ℝ) < 1 / 10)
      (by norm_num : (1 : ℝ) ≠ 0) (by simpa only [neg_mul,one_mul] using hsol)
    simp only [div_one] at hi
    have hlate : s.time + 419 / 300 < w.time := by
      by_contra hn
      have ht : v.time ≤ s.time + 419 / 300 := by
        rw [← exit.time_unchanged]
        exact le_of_not_gt hn
      have hmax : segment.accumulatedRecovery i ≤ (28001 / 100000 : ℝ) * (419 / 300) := by
        linarith
      rw [hi] at hmax
      linarith [mark_only_log_margin.1]
    have hseg : segment.AllStates (fun v => v.time ≤ s.time + 419 / 300 → v.main i = .slow) :=
      segment.allStates_mono (fun v hv _ => hv) hstates
    have hrest : rest.AllStates (fun v => v.time ≤ s.time + 419 / 300 → v.main i = .slow) :=
      rest.allStates_mono (fun v hv ht => False.elim (by have h := hv.1; linarith))
        rest.allStates_time_bounds
    rw [he,Execution.allStates_append]
    exact ⟨hseg,segment.allStates_final hseg,hrest⟩

structure CadenceMarkOnlyPulse {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) where
  mark_case : ShortMarkPulse e i p
  protected_window : e.AllStates (fun v => v.time ≤ s.time + 419 / 300 → v.main i = .slow)
  admission_return : ReadyReturn e i
  return_deadline : admission_return.afterReturn.time < s.time + 19 / 5
  emissions : e.emissionTimes i = []
  error_zero : ∀ q, e.ledger.error i q = 0
  gain_preserved : ∀ q, u.x i (.z q) = s.x i (.z q)
  recovery_gain : u.x i .b = s.x i .b + 1 / 10
  ready : u.main i = .ready
  charge_rest : u.x i .q = 1 / 10
  auxiliary : ∀ q, u.aux i q = .ready ∧ RestBand (u.x i (.m q))
  raw_finished : ∀ q, u.raw i q = none

/-- The first cadence MARK input has no output and no ERROR dose. All phases,
the MARK dose and the eventual READY return are extracted from the execution. -/
theorem Execution.cadence_mark_only_pulse {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : s.main i = .slow)
    (hq : 37 / 250 ≤ s.x i .q ∧ s.x i .q ≤ 1 / 4)
    (hbRange : 17999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 18001 / 100000)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 19 / 5 ≤ u.time) :
    Nonempty (CadenceMarkOnlyPulse e i p) := by
  obtain ⟨pulse⟩ := e.short_mark_pulse_of_invariant hb hf hv i p hs
    (by linarith [hq.1]) (by linarith [hbRange.2]) ha hr ho hno (by linarith)
  let cycle := pulse.cycle
  let mk := cycle.phases.markPhase
  have hinputBudget := e.recovery_one_input_budget cycle hb hv hr ho hno
    (fun q _ => ⟨(ha q).1,(ha q).2.2⟩)
  have hbudget := e.recovery_upper_of_end hb i (28001 / 100000) (by
    linarith [hbRange.2])
  have hwindow := e.slow_mark_only_window i hs hq.1 hbudget.2
  have herror : cycle.phases.errorPhase.span.AllStates (fun v => v.main i ≠ .ready) := by
    have hstates := (cycle.error_states hwindow).1
    have hend : cycle.phases.errorPhase.beforeExit.time < s.time + 419 / 300 := by
      rw [← cycle.phases.errorPhase.exit.time_unchanged]
      exact cycle.ready_deadline
    refine cycle.phases.errorPhase.span.allStates_mono ?_
      (cycle.phases.errorPhase.span.allStates_and hstates cycle.phases.errorPhase.span.allStates_time_bounds)
    intro v h
    have hmode := h.1 (by have ht := h.2.2; linarith)
    rw [hmode]; decide
  have herrorTarget := cycle.error_zero_of_protected hv hr (hno p) herror
  have htarget := cycle.final_rest hv hr (hno p)
  have hother : ∀ q, q ≠ p →
      (u.aux i q = .ready ∧ RestBand (u.x i (.m q))) ∧ u.x i (.z q) = s.x i (.z q) :=
    fun q hq => e.aux_no_input_rest_band i q (ha q).1 (ha q).2 (ho q hq) (hno q)
  have hgain : ∀ q, u.x i (.z q) = s.x i (.z q) := by
    intro q
    by_cases hq : q = p
    · subst q
      exact herrorTarget.2
    · exact (hother q hq).2
  have hraw := e.raw_expired_states i s.time hv
    (fun q => by
      by_cases hq : q = p
      · subst q; exact Or.inr hr
      · exact Or.inl (ho q hq)) hno
  have hemissions := e.no_emissions_of_slow_window i hs hwindow hraw hno
  have hhead := pulse.mark_head_facts hb hv ha hr ho hno
  have hB : 0 < s.x i .b + 1 / 10 := by linarith [hbRange.1]
  have hsol := cycle.markHead.slow_solution i (cycle.markHead.allStates_main_flows i .slow hhead.1)
  have hImax := cycle.markHead.accumulatedRecovery_upper i (by linarith [hbRange.2])
  have hIbound : cycle.markHead.accumulatedRecovery i ≤ 11 / 200 := by
    linarith [cycle.mark_ends_early hb]
  have hIpos := cycle.markHead.accumulatedRecovery_nonnegative hb i (by linarith [hbRange.1])
  have hqmark : 1 / 10 < mk.afterExit.x i .q := by
    have he := Real.add_one_le_exp (-cycle.markHead.accumulatedRecovery i)
    have hp := mul_le_mul_of_nonneg_right hq.1 (Real.exp_pos (-cycle.markHead.accumulatedRecovery i)).le
    rw [← hsol] at hp
    nlinarith
  have hqmarkUpper : mk.afterExit.x i .q ≤ 1 / 4 := by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hIpos)
    have hp := mul_le_mul_of_nonneg_left he (show 0 ≤ s.x i .q by linarith [hq.1])
    rw [← hsol] at hp
    nlinarith [hq.2]
  have hlog : Real.log (mk.afterExit.x i .q / (1 / 10)) ≤ Real.log (5 / 2) := by
    apply Real.log_le_log (by positivity) ?_
    linarith
  have hquot : Real.log (mk.afterExit.x i .q / (1 / 10)) / (s.x i .b + 1 / 10) < 15 / 4 := by
    apply (div_lt_iff₀ hB).2
    nlinarith [KernelR.log_recovery_bounds.2,hbRange.1]
  have hconst := mk.rest.recovery_constant_of_end hb i (pulse.recovery_gain.trans hhead.2.1.symm)
  have hconstant : mk.rest.AllFlows (fun {v w} f =>
      ∀ t ∈ Icc v.time w.time, f.path t i .b = s.x i .b + 1 / 10) := by
    refine mk.rest.allFlows_mono ?_ hconst.2
    intro v w f h t ht
    exact (h t ht).trans hhead.2.1
  obtain ⟨ret⟩ := mk.rest.constant_slow_return i (cycle.markHead.allStates_final hhead.1)
    hqmark (s.x i .b + 1 / 10) hB hconstant (by linarith [cycle.mark_ends_early hb])
  have hdeadline : ret.afterReturn.time < s.time + 19 / 5 := by
    rw [ret.date]
    linarith [cycle.mark_ends_early hb]
  let head := cycle.markHead.append ret.span
  have he : e = head.append (.cons (.jump ret.exit) ret.rest) := by
    calc
      e = cycle.markHead.append mk.rest := cycle.markHead_reconstruct
      _ = cycle.markHead.append (ret.span.append (.cons (.jump ret.exit) ret.rest)) :=
        congrArg (fun actual => cycle.markHead.append actual) ret.reconstruct
      _ = _ := by simp only [head,Execution.append_assoc]
  have hwin := hwindow
  rw [he,Execution.allStates_append] at hwin
  have hlate : s.time + 419 / 300 < ret.afterReturn.time := by
    by_contra hn
    have hmode := ret.rest.allStates_initial hwin.2.2 (le_of_not_gt hn)
    rw [ret.ready_after] at hmode
    contradiction
  have hrawRest := hraw
  rw [he,Execution.allStates_append] at hrawRest
  let readyReturn : ReadyReturn e i :=
    ⟨ret.beforeReturn,ret.afterReturn,head,ret.exit,ret.rest,he,ret.ready_after,ret.charge_after,
      ret.rest.allStates_initial hrawRest.2.2 (by linarith),by linarith⟩
  have hfinal := readyReturn.final_ready hno
  refine ⟨⟨pulse,hwindow,readyReturn,hdeadline,hemissions,?_,hgain,pulse.recovery_gain,
    hfinal.1,hfinal.2,?_,e.allStates_final hraw (by linarith)⟩⟩
  · intro q
    have h := e.gain_balance i q
    rw [hgain q] at h
    linarith
  · intro q
    by_cases hq : q = p
    · subst q
      exact ⟨htarget.1,by rw [htarget.2]; norm_num [RestBand]⟩
    · exact (hother q hq).1

end KernelR.Hybrid
