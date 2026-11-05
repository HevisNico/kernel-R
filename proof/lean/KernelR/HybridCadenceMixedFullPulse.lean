import KernelR.HybridCadenceMixedPulse
import KernelR.HybridCadenceStrongPulse
import KernelR.HybridMixedFullSlowReturn
import KernelR.HybridRawFullTailNoFire

/-! The full mixed numerical band retains its actual old RAW tail after an
own READY return later than0.43. All doses and charge bounds are derived from
that same physical execution, including the ERROR phase before RAW expiry. -/
namespace KernelR.Hybrid
open Set

theorem mixed_full_raw_gain_bound {z : ℝ}
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ z ∧
      z ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000) :
    Real.exp (z + 11 / 125) ≤ 11 / 5 := by
  have hg := cadence_three_dose_gain_bounds hz
  have he : Real.exp (11 / 125 : ℝ) ≤ 11 / 10 := by
    have h := Real.exp_bound (x := (11 / 125 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).1]
  rw [Real.exp_add]
  have h := mul_le_mul hg.2 he (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 19 / 10)
  linarith

structure CadenceMixedFullPulse {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) where
  mark_case : ShortMarkPulse e i p
  mixed_return : ShortMarkReturn mark_case
  error_ready : mark_case.cycle.phases.errorPhase.span.AllStates (fun v => v.main i = .ready)
  emissions : e.emissionTimes i = []
  error_dose : e.ledger.error i p = 3 / 5
  error_other : ∀ q, q ≠ p → e.ledger.error i q = 0
  gain_target : u.x i (.z p) = s.x i (.z p) + 3 / 5
  gain_other : ∀ q, q ≠ p → u.x i (.z q) = s.x i (.z q)
  recovery_gain : u.x i .b = s.x i .b + 1 / 10
  ready : u.main i = .ready
  charge : 1 / 10 ≤ u.x i .q ∧ u.x i .q ≤ 1 / 2
  charge_cadence : u.x i .q ≤ 8 / 25
  auxiliary : ∀ q, u.aux i q = .ready ∧ RestBand (u.x i (.m q))
  raw_finished : ∀ q, u.raw i q = none

/-- This helper consumes a proved actual return; the public wrapper below
extracts that return from the numerical input bounds. -/
theorem ShortMarkPulse.mixed_full_case_of_return {n θ ε route s u i p} {e : @Execution n θ route s u}
    (pulse : ShortMarkPulse e i p) (ret : ShortMarkReturn pulse)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q)
    (hafter : s.time + 43 / 100 < ret.returnPhase.afterReturn.time)
    (hbefore : ret.returnPhase.afterReturn.time < s.time + 99 / 100)
    (ht : s.time + 37 / 10 ≤ u.time) : Nonempty (CadenceMixedFullPulse e i p) := by
  let cycle := pulse.cycle
  let mk := cycle.phases.markPhase
  let r := ret.returnPhase
  let head := cycle.markHead.append (r.span.append (.cons (.jump r.exit) (.nil _)))
  have he : e = head.append r.rest := by
    calc
      e = cycle.markHead.append mk.rest := cycle.markHead_reconstruct
      _ = cycle.markHead.append (r.span.append (.cons (.jump r.exit) r.rest)) :=
        congrArg (fun actual => cycle.markHead.append actual) r.reconstruct
      _ = _ := by simp only [head,Execution.append_assoc,Execution.append]
  have hnoHead : ∀ q, NoArrivalAt head i q := by
    intro q
    have h := hno q
    rw [he,Execution.noArrivalAt_append] at h
    exact h.1
  have hnoRest : ∀ q, NoArrivalAt r.rest i q := by
    intro q
    have h := hno q
    rw [he,Execution.noArrivalAt_append] at h
    exact h.2
  have hrawRet : r.afterReturn.raw i p = some s.time := head.raw_persists i p s.time hr (by linarith)
  have hoRet : ∀ q, q ≠ p → r.afterReturn.raw i q = none := fun q hq =>
    (head.raw_absent_of_no_arrival i q (ho q hq) (hnoHead q)).1
  have hcap : Real.exp (s.x i (.z p) + 11 / 125) ≤ 11 / 5 :=
    mixed_full_raw_gain_bound hz
  have hgain := cycle.gain_during_raw hb
  rw [he,Execution.allFlows_append] at hgain
  have hg : r.rest.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      t ≤ s.time + 1 → Real.exp (f.path t i (.z p)) ≤ 11 / 5) := by
    refine r.rest.allFlows_mono ?_ hgain.2
    intro v w f h t ht hu
    exact (Real.exp_le_exp.mpr (h t ⟨ht.1,ht.2.le⟩ hu)).trans hcap
  obtain ⟨tail⟩ := r.rest.raw_full_tail_no_fire i p s.time (11 / 5) r.ready_after r.charge_after
    (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
    hrawRet hoRet hnoRest hg
  have hwindow := ret.ready_window tail.ready_states
  have herror : cycle.phases.errorPhase.span.AllStates (fun v => v.main i = .ready) := by
    have hw := (cycle.error_states hwindow).1
    refine cycle.phases.errorPhase.span.allStates_mono ?_
      (cycle.phases.errorPhase.span.allStates_and hw cycle.phases.errorPhase.span.allStates_time_bounds)
    intro v h
    exact h.1 (by have hl := h.2.1; linarith [cycle.error_starts_late])
  have hh : s.x i (.z p) + 3 / 5 < Real.log ((θ i).cap p) :=
    lt_of_le_of_lt (by linarith [hz.2]) (hb.low_gain_headroom i p)
  have herrorDose := cycle.total_error_of_ready_error hb hf hv herror hh hr (hno p)
  have hother : ∀ q, q ≠ p →
      (u.aux i q = .ready ∧ RestBand (u.x i (.m q))) ∧ u.x i (.z q) = s.x i (.z q) :=
    fun q hq => e.aux_no_input_rest_band i q (ha q).1 (ha q).2 (ho q hq) (hno q)
  have htarget := cycle.final_rest hv hr (hno p)
  have hheadSlow := (pulse.mark_head_facts hb hv ha hr ho hno).1
  have hheadEmission := cycle.markHead.no_emissions_if_not_ready i
    (cycle.markHead.allStates_mono (fun v hv => by rw [hv]; decide) hheadSlow)
  have hspanEmission := r.span.no_emissions_if_not_ready i
    (r.span.allStates_mono (fun v hv => by rw [hv]; decide) r.slow_states)
  have hrestEmission := mk.rest.no_emissions_of_split r.span r.exit r.rest r.reconstruct i hspanEmission
    (r.exit.no_emissions_if_not_ready i (by rw [r.slow_before]; decide)) tail.emissions
  have hemissions : e.emissionTimes i = [] := by
    calc
      _ = (cycle.markHead.append mk.rest).emissionTimes i :=
        congrArg (fun actual => actual.emissionTimes i) cycle.markHead_reconstruct
      _ = [] := by rw [Execution.emissionTimes_append,hheadEmission,hrestEmission]; rfl
  have hdecay : Real.exp (-(1 / 2 : ℝ) * (u.time - tail.departure.afterEnd.time)) ≤ 27 / 100 := by
    have hd : tail.departure.afterEnd.time = s.time + 1 := by
      rw [tail.departure.exit.time_unchanged,tail.departure.date]
    have he : (100 / 27 : ℝ) ≤ Real.exp (27 / 20) := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 27 / 20) 6
      norm_num [Finset.sum_range_succ] at h
      linarith
    calc
      _ ≤ Real.exp (-(27 / 20 : ℝ)) := Real.exp_le_exp.mpr (by rw [hd]; linarith)
      _ ≤ _ := by
        rw [Real.exp_neg,inv_eq_one_div]
        apply (div_le_iff₀ (Real.exp_pos _)).mpr
        nlinarith
  have hqlow : 1 / 10 ≤ u.x i .q := by
    rw [tail.charge_decay]
    exact le_add_of_nonneg_right (mul_nonneg (by linarith [tail.charge_at_end.1]) (Real.exp_pos _).le)
  have hqupper : u.x i .q ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hdecay (show 0 ≤ tail.departure.afterEnd.x i .q - 1 / 10 by
      linarith [tail.charge_at_end.1])
    rw [tail.charge_decay]
    linarith [tail.charge_at_end.2]
  have hqc : u.x i .q ≤ 8 / 25 := by
    have h := mul_le_mul_of_nonneg_left hdecay (show 0 ≤ tail.departure.afterEnd.x i .q - 1 / 10 by
      linarith [tail.charge_at_end.1])
    rw [tail.charge_decay]
    linarith [tail.charge_at_end.2]
  refine ⟨⟨pulse,ret,herror,hemissions,herrorDose.1,?_,herrorDose.2,
    fun q hq => (hother q hq).2,pulse.recovery_gain,
    r.rest.allStates_final tail.ready_states,⟨hqlow,hqupper⟩,hqc,?_,tail.raw_finished⟩⟩
  · intro q hq
    have h := e.gain_balance i q
    rw [(hother q hq).2] at h
    linarith
  · intro q
    by_cases hq : q = p
    · subst q
      exact ⟨htarget.1,by rw [htarget.2]; norm_num [RestBand]⟩
    · exact (hother q hq).1

/-- The mixed cadence case follows solely from the actual numerical input
state and isolated source pulse, including its still-active tail after return. -/
theorem Execution.cadence_mixed_full_pulse {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : s.main i = .slow)
    (hq : 59 / 500 ≤ s.x i .q ∧ s.x i .q ≤ 71 / 500)
    (hbRange : 27999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 28001 / 100000)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 37 / 10 ≤ u.time) :
    Nonempty (CadenceMixedFullPulse e i p) := by
  obtain ⟨pulse⟩ := e.short_mark_pulse_of_invariant hb hf hv i p hs (by linarith [hq.1])
    (by linarith [hbRange.2]) ha hr ho hno (by linarith)
  obtain ⟨ret⟩ := pulse.mixed_full_slow_return hb hv ha hr ho hno hq hbRange
  exact pulse.mixed_full_case_of_return ret.toShortMarkReturn hb hf hv ha hz hr ho hno
    ret.after_forty_three ret.before_deadline ht

end KernelR.Hybrid
