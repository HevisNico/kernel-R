import KernelR.HybridSlowMarkReturn
import KernelR.HybridRawTailNoFire
import KernelR.HybridHighGainTrigger

/-! The second cadence MARK input reopens before ERROR. Its still-active raw
tail is integrated, and the subsequent full ERROR dose is derived locally. -/
namespace KernelR.Hybrid
open Set

theorem SensorCycle.error_dose_of_ready_error {n θ ε route s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s)
    (hm : cycle.phases.errorPhase.span.AllStates (fun v => v.main i = .ready))
    (hh : s.x i (.z p) + 3 / 5 < Real.log ((θ i).cap p)) :
    cycle.phases.errorPhase.span.ledger.error i p = 3 / 5 ∧
      cycle.phases.errorPhase.afterExit.x i (.z p) = s.x i (.z p) + 3 / 5 := by
  let tr := cycle.trigger
  let mk := cycle.phases.markPhase
  let si := cycle.phases.silentPhase
  let er := cycle.phases.errorPhase
  let pastMark := tr.span.append (.cons (.jump tr.entry) (.nil _))
  let pastSilent := pastMark.append (mk.span.append (.cons (.jump mk.exit) (.nil _)))
  let pastError := pastSilent.append (si.span.append (.cons (.jump si.exit) (.nil _)))
  have hmain := er.span.allStates_main_flows i .ready hm
  have hh' : si.afterExit.x i (.z p) + 8 * (si.afterExit.x i (.m p) - 1 / 40) < Real.log ((θ i).cap p) := by
    rw [cycle.error_initial_gain,si.after_charge]
    norm_num only [protectedFloor]
    linarith
  have ho := er.span.error_exposed_of_invariant hb (pastError.physical_invariant hb hf) i p er.flows hmain hh'
  have hd := er.span.full_error_of_open_endpoints i p ho
    (by change si.afterExit.x i (.m p) = 1 / 10; simpa only [protectedFloor] using si.after_charge)
    (by simpa only [protectedFloor] using er.charge)
  refine ⟨hd,?_⟩
  change er.afterExit.x i (.z p) = _
  rw [er.exit.physical_continuous,er.span.gain_balance i p,hd,cycle.error_initial_gain]

theorem SensorCycle.total_error_of_ready_error {n θ ε route s u i p}
    {e : @Execution n θ route s u} (cycle : SensorCycle e i p)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hm : cycle.phases.errorPhase.span.AllStates (fun v => v.main i = .ready))
    (hh : s.x i (.z p) + 3 / 5 < Real.log ((θ i).cap p))
    (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p) :
    e.ledger.error i p = 3 / 5 ∧ u.x i (.z p) = s.x i (.z p) + 3 / 5 := by
  let er := cycle.phases.errorPhase
  have hd := cycle.error_dose_of_ready_error hb hf hm hh
  have hready := cycle.error_rest_ready hv hr hno
  have hgain := (er.rest.gain_constant_aux i p .ready (by decide)
    (er.rest.allStates_aux_flows i p .ready hready)).1
  have hu : u.x i (.z p) = s.x i (.z p) + 3 / 5 := hgain.trans hd.2
  refine ⟨?_,hu⟩
  have h := e.gain_balance i p
  linarith

/-- The first return after MARK fixes the beginning of the later READY window. -/
theorem ShortMarkReturn.ready_window {n θ route s u i p} {e : @Execution n θ route s u}
    {pulse : ShortMarkPulse e i p} (ret : ShortMarkReturn pulse)
    (hq : ret.returnPhase.rest.AllStates (fun v => v.main i = .ready)) :
    e.AllStates (fun v => ret.returnPhase.afterReturn.time < v.time → v.main i = .ready) := by
  let r := ret.returnPhase
  let mk := pulse.cycle.phases.markPhase
  have hbefore : r.span.AllStates (fun v => r.afterReturn.time < v.time → v.main i = .ready) := by
    refine r.span.allStates_mono ?_ r.span.allStates_time_bounds
    intro v hv ht
    exact False.elim (by rw [r.exit.time_unchanged] at ht; linarith [hv.2])
  have htail : mk.rest.AllStates (fun v => r.afterReturn.time < v.time → v.main i = .ready) := by
    apply (congrArg (fun actual => actual.AllStates
      (fun v => r.afterReturn.time < v.time → v.main i = .ready)) r.reconstruct).mpr
    rw [Execution.allStates_append]
    exact ⟨hbefore,r.span.allStates_final hbefore,r.rest.allStates_mono (fun v hv _ => hv) hq⟩
  have hmarkdate : mk.afterExit.time ≤ r.afterReturn.time := by
    rw [r.exit.time_unchanged]
    exact r.span.time_monotone
  have hhead : pulse.cycle.markHead.AllStates
      (fun v => r.afterReturn.time < v.time → v.main i = .ready) := by
    refine pulse.cycle.markHead.allStates_mono ?_ pulse.cycle.markHead.allStates_time_bounds
    intro v hv ht
    exact False.elim (by linarith [hv.2])
  change e.AllStates (fun v => r.afterReturn.time < v.time → v.main i = .ready)
  apply (congrArg (fun actual => actual.AllStates
    (fun v => r.afterReturn.time < v.time → v.main i = .ready)) pulse.cycle.markHead_reconstruct).mpr
  rw [Execution.allStates_append]
  exact ⟨hhead,htail⟩

structure CadenceMixedPulse {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) where
  mark_case : ShortMarkPulse e i p
  mixed_return : ShortMarkReturn mark_case
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
theorem ShortMarkPulse.mixed_case_of_return {n θ ε route s u i p} {e : @Execution n θ route s u}
    (pulse : ShortMarkPulse e i p) (ret : ShortMarkReturn pulse)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q)
    (hafter : s.time + 1 / 2 < ret.returnPhase.afterReturn.time)
    (hbefore : ret.returnPhase.afterReturn.time < s.time + 99 / 100)
    (ht : s.time + 19 / 5 ≤ u.time) : Nonempty (CadenceMixedPulse e i p) := by
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
  have hcap : Real.exp (s.x i (.z p) + 11 / 125) ≤ 7 / 2 :=
    (cadence_high_gain_bounds (by linarith [hz.1]) (by linarith [hz.2])).2
  have hgain := cycle.gain_during_raw hb
  rw [he,Execution.allFlows_append] at hgain
  have hg : r.rest.AllFlows (fun {v w} f => ∀ t ∈ Ico v.time w.time,
      t ≤ s.time + 1 → Real.exp (f.path t i (.z p)) ≤ 7 / 2) := by
    refine r.rest.allFlows_mono ?_ hgain.2
    intro v w f h t ht hu
    exact (Real.exp_le_exp.mpr (h t ⟨ht.1,ht.2.le⟩ hu)).trans hcap
  obtain ⟨tail⟩ := r.rest.raw_tail_no_fire i p s.time (7 / 2) r.ready_after r.charge_after
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
  have hdecay : Real.exp (-(1 / 2 : ℝ) * (u.time - tail.departure.afterEnd.time)) ≤ 1 / 4 := by
    have hd : tail.departure.afterEnd.time = s.time + 1 := by
      rw [tail.departure.exit.time_unchanged,tail.departure.date]
    have he : (4 : ℝ) ≤ Real.exp (7 / 5) := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 5) 6
      norm_num [Finset.sum_range_succ] at h
      linarith
    calc
      _ ≤ Real.exp (-(7 / 5 : ℝ)) := Real.exp_le_exp.mpr (by rw [hd]; linarith)
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
  refine ⟨⟨pulse,ret,hemissions,herrorDose.1,?_,herrorDose.2,
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
theorem Execution.cadence_mixed_pulse {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : s.main i = .slow)
    (hq : 61 / 500 ≤ s.x i .q ∧ s.x i .q ≤ 7 / 50)
    (hbRange : 27999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 28001 / 100000)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 19 / 5 ≤ u.time) :
    Nonempty (CadenceMixedPulse e i p) := by
  obtain ⟨pulse⟩ := e.short_mark_pulse_of_invariant hb hf hv i p hs (by linarith [hq.1])
    (by linarith [hbRange.2]) ha hr ho hno (by linarith)
  obtain ⟨ret⟩ := pulse.mixed_slow_return hb hv ha hr ho hno hq hbRange
  exact pulse.mixed_case_of_return ret.toShortMarkReturn hb hf hv ha hz hr ho hno
    ret.after_half ret.before_deadline ht

end KernelR.Hybrid
