import KernelR.HybridSlowMarkWindow

namespace KernelR.Hybrid
open Set

structure ConstantSlowReturn {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (B : ℝ) where
  beforeReturn : Snapshot n
  afterReturn : Snapshot n
  span : Execution θ route s beforeReturn
  exit : Jump route beforeReturn afterReturn
  rest : Execution θ route afterReturn u
  reconstruct : e = span.append (.cons (.jump exit) rest)
  slow_states : span.AllStates (fun v => v.main i = .slow)
  slow_before : beforeReturn.main i = .slow
  ready_after : afterReturn.main i = .ready
  charge_before : beforeReturn.x i .q = 1 / 10
  charge_after : afterReturn.x i .q = 1 / 10
  date : afterReturn.time = s.time + Real.log (s.x i .q / (1 / 10)) / B

/-- The initial charge is arbitrary: this does not replace it by 1/4. -/
theorem Execution.constant_slow_no_overrun {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (hm : e.MainFlows i .slow)
    (hq : 1 / 10 < s.x i .q) (B : ℝ) (hB : 0 < B)
    (hc : e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b = B)) :
    u.time ≤ s.time + Real.log (s.x i .q / (1 / 10)) / B := by
  have hf := e.protected_main_floor i .slow (by decide) hm (by exact hq.le)
  have he := e.slow_solution i hm
  rw [e.accumulatedRecovery_of_constant i B hc] at he
  rw [← neg_mul] at he
  have hd := duration_le_of_decay_floor (by linarith : 0 < s.x i .q)
    (by norm_num : (0 : ℝ) < 1 / 10) hB hf he
  linarith

/-- A sufficient horizon forces the first actual SLOW departure and identifies
its exact date from the solved physical clock. -/
theorem Execution.constant_slow_return {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (hs : s.main i = .slow)
    (hq : 1 / 10 < s.x i .q) (B : ℝ) (hB : 0 < B)
    (hc : e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, f.path t i .b = B))
    (ht : s.time + Real.log (s.x i .q / (1 / 10)) / B < u.time) :
    Nonempty (ConstantSlowReturn e i B) := by
  rcases e.first_state_change (fun v => v.main i) .slow
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · have hbound := e.constant_slow_no_overrun i (e.allStates_main_flows i .slow h) hq B hB hc
    exact False.elim (not_lt_of_ge hbound ht)
  · have hcseg := hc
    rw [he,Execution.allFlows_append] at hcseg
    have hg := exit.slow_departure_guard i hv hw
    have hsol := segment.slow_solution i (segment.allStates_main_flows i .slow hstates)
    rw [segment.accumulatedRecovery_of_constant i B hcseg.1,hg] at hsol
    rw [← neg_mul] at hsol
    have hd := duration_of_decay (by linarith : 0 < s.x i .q)
      (by norm_num : (0 : ℝ) < 1 / 10) (ne_of_gt hB) hsol
    refine ⟨⟨v,w,segment,exit,rest,he,hstates,hv,
      exit.slow_main_departure i hv hw,hg,?_,?_⟩⟩
    · rw [exit.physical_continuous,hg]
    · rw [exit.time_unchanged]
      linarith

theorem Execution.no_mark_flows_of_ready_aux {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n)
    (ha : ∀ q, e.AuxFlows i q .ready) : e.NoMarkFlows i := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow f =>
      exact ⟨fun q => by rw [(ha q).1]; decide,ih (fun q => (ha q).2)⟩
    | jump j => exact ih ha

/-- Physical data needed after MARK, with no protection assumption about ERROR. -/
theorem ShortMarkPulse.mark_head_facts {n θ ε route s u i p}
    {e : @Execution n θ route s u} (pulse : ShortMarkPulse e i p)
    (hb : PhysicalBox θ ε) (hv : RawValid s)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) :
    pulse.cycle.markHead.AllStates (fun v => v.main i = .slow) ∧
    pulse.cycle.phases.markPhase.afterExit.x i .b = s.x i .b + 1 / 10 ∧
    pulse.cycle.markHead.accumulatedRecovery i =
      (s.x i .b + 1 / 10) * (pulse.cycle.phases.markPhase.afterExit.time - s.time) -
        Cadence.markDeficit (pulse.cycle.trigger.afterMark.time - s.time) ((θ i).lm p) := by
  let cycle := pulse.cycle
  let st := cycle.trigger
  let mk := cycle.phases.markPhase
  have hwindow := pulse.slow_window
  rw [cycle.markHead_reconstruct,Execution.allStates_append] at hwindow
  have hslow : cycle.markHead.AllStates (fun v => v.main i = .slow) := by
    refine cycle.markHead.allStates_mono ?_
      (cycle.markHead.allStates_and hwindow.1 cycle.markHead.allStates_time_bounds)
    intro v h
    exact h.1 (by have ht := h.2.2; linarith [cycle.mark_ends_early hb])
  have hnoHead : ∀ q, NoArrivalAt cycle.markHead i q := by
    intro q
    have hn := hno q
    rw [cycle.markHead_reconstruct,Execution.noArrivalAt_append] at hn
    exact hn.1
  have hdPhase : mk.span.ledger.mark i p = 1 / 10 := by
    rw [← cycle.mark_ledger_eq_phase hv hr (hno p)]
    exact pulse.mark_dose
  have hmark : cycle.markHead.ledger.mark i p = 1 / 10 := by
    have hz := st.span.mark_zero_aux i p .ready (by decide) st.flows
    simp only [SensorCycle.markHead,Execution.mark_append,Execution.ledger,Move.ledger,Ledger.add,
      Ledger.zero,add_zero]
    change st.span.ledger.mark i p + (st.entry.ledger.mark i p +
      (mk.span.ledger.mark i p + mk.exit.ledger.mark i p)) = _
    rw [st.entry.mark_zero,mk.exit.mark_zero,hz,hdPhase]
    ring
  have hother : ∀ q, q ≠ p → cycle.markHead.ledger.mark i q = 0 := by
    intro q hq
    have hquiet := cycle.markHead.aux_ready_without_input_band i q
      (ha q).1 (ha q).2.2 (ho q hq) (hnoHead q)
    exact cycle.markHead.mark_zero_aux i q .ready (by decide)
      (cycle.markHead.allStates_aux_flows i q .ready hquiet)
  have hbgain : mk.afterExit.x i .b = s.x i .b + 1 / 10 := by
    rw [cycle.markHead.recovery_balance i,cycle.markHead.recovery_sum_marks i,
      Finset.sum_eq_single p (fun q _ hq => hother q hq) (by simp),hmark]
  have hpreNoMark : st.span.NoMarkFlows i := by
    apply st.span.no_mark_flows_of_ready_aux i
    intro q
    by_cases hq : q = p
    · subst q; exact st.flows
    · have hquiet := e.aux_ready_without_input_band i q (ha q).1 (ha q).2.2 (ho q hq) (hno q)
      rw [st.reconstruct,Execution.allStates_append] at hquiet
      exact st.span.allStates_aux_flows i q .ready hquiet.1
  have hpre := st.span.recovery_without_mark i hpreNoMark
  have hbmark : st.afterMark.x i .b = s.x i .b := by
    rw [st.entry.physical_continuous,hpre.1]
  have hclock : cycle.markHead.accumulatedRecovery i =
      st.span.accumulatedRecovery i + mk.span.accumulatedRecovery i := by
    simp only [SensorCycle.markHead,Execution.accumulatedRecovery_append,
      Execution.accumulatedRecovery,add_zero]
    rfl
  have hduration : mk.afterExit.time = st.afterMark.time + Cadence.markDuration ((θ i).lm p) := by
    rw [mk.after_time]
    change st.afterMark.time + auxRemaining θ st.afterMark i p .mark = _
    norm_num [auxRemaining,protectedFloor,auxRate,st.charge,Cadence.markDuration]
  refine ⟨hslow,hbgain,?_⟩
  rw [hclock,st.span.accumulatedRecovery_of_constant i (s.x i .b) hpre.2,pulse.mark_integral,
    hbmark,hduration,st.entry.time_unchanged]
  dsimp [Cadence.markDeficit,Cadence.markDuration]
  field_simp
  ring

structure ShortMarkReturn {n θ route s u i p} {e : @Execution n θ route s u}
    (pulse : ShortMarkPulse e i p) where
  returnPhase : ConstantSlowReturn pulse.cycle.phases.markPhase.rest i (s.x i .b + 1 / 10)
  mark_clock : pulse.cycle.markHead.accumulatedRecovery i =
    (s.x i .b + 1 / 10) * (pulse.cycle.phases.markPhase.afterExit.time - s.time) -
      Cadence.markDeficit (pulse.cycle.trigger.afterMark.time - s.time) ((θ i).lm p)
  date : returnPhase.afterReturn.time = s.time +
    (Real.log (s.x i .q / (1 / 10)) +
      Cadence.markDeficit (pulse.cycle.trigger.afterMark.time - s.time) ((θ i).lm p)) /
        (s.x i .b + 1 / 10)
  before_error : returnPhase.afterReturn.time < pulse.cycle.phases.silentPhase.afterExit.time

/-- The first actual return after MARK precedes ERROR whenever its derived
clock date is below .99. No output, ERROR dose or phase word is supplied. -/
theorem ShortMarkPulse.slow_return_before_error {n θ ε route s u i p}
    {e : @Execution n θ route s u} (pulse : ShortMarkPulse e i p)
    (hb : PhysicalBox θ ε) (hv : RawValid s)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (hB : 0 < s.x i .b + 1 / 10)
    (hqmark : 1 / 10 < pulse.cycle.phases.markPhase.afterExit.x i .q)
    (hdate : (Real.log (s.x i .q / (1 / 10)) +
      Cadence.markDeficit (pulse.cycle.trigger.afterMark.time - s.time) ((θ i).lm p)) /
        (s.x i .b + 1 / 10) < 99 / 100) : Nonempty (ShortMarkReturn pulse) := by
  let cycle := pulse.cycle
  let mk := cycle.phases.markPhase
  have hf := pulse.mark_head_facts hb hv ha hr ho hno
  have hs := cycle.markHead.allStates_final hf.1
  have hsol := cycle.markHead.slow_solution i (cycle.markHead.allStates_main_flows i .slow hf.1)
  have hqin : 0 < s.x i .q := by
    by_contra hn
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn)
      (Real.exp_pos (-cycle.markHead.accumulatedRecovery i)).le
    rw [← hsol] at hm
    linarith
  have hlog : Real.log (mk.afterExit.x i .q / (1 / 10)) =
      Real.log (s.x i .q / (1 / 10)) - cycle.markHead.accumulatedRecovery i := by
    rw [Real.log_div (by linarith : mk.afterExit.x i .q ≠ 0) (by norm_num),hsol,
      Real.log_mul (ne_of_gt hqin) (Real.exp_ne_zero _),Real.log_exp,
      Real.log_div (ne_of_gt hqin) (by norm_num)]
    ring
  have hdateeq : mk.afterExit.time + Real.log (mk.afterExit.x i .q / (1 / 10)) /
      (s.x i .b + 1 / 10) = s.time +
        (Real.log (s.x i .q / (1 / 10)) +
          Cadence.markDeficit (cycle.trigger.afterMark.time - s.time) ((θ i).lm p)) /
            (s.x i .b + 1 / 10) := by
    rw [hlog,hf.2.2]
    dsimp only [mk,cycle]
    apply mul_right_cancel₀ (ne_of_gt hB)
    simp only [add_mul,div_mul_cancel₀ _ (ne_of_gt hB)]
    ring
  have hconst := mk.rest.recovery_constant_of_end hb i (pulse.recovery_gain.trans hf.2.1.symm)
  have hconstant : mk.rest.AllFlows (fun {v w} f =>
      ∀ t ∈ Icc v.time w.time, f.path t i .b = s.x i .b + 1 / 10) := by
    refine mk.rest.allFlows_mono ?_ hconst.2
    intro v w f h t ht
    exact (h t ht).trans hf.2.1
  have hu : s.time + 1 < u.time := cycle.ready_after_raw.trans_le cycle.phases.errorPhase.rest.time_monotone
  obtain ⟨ret⟩ := mk.rest.constant_slow_return i hs hqmark (s.x i .b + 1 / 10) hB hconstant (by
    rw [hdateeq]
    linarith)
  refine ⟨⟨ret,hf.2.2,ret.date.trans hdateeq,?_⟩⟩
  rw [ret.date,hdateeq]
  linarith [cycle.error_starts_late]

/-- Converting the residual charge at MARK exit retains the exact MARK clock. -/
theorem ShortMarkPulse.mark_return_delay {n θ ε route s u i p}
    {e : @Execution n θ route s u} (pulse : ShortMarkPulse e i p)
    (hb : PhysicalBox θ ε) (hv : RawValid s)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (hB : 0 < s.x i .b + 1 / 10)
    (hqin : 0 < s.x i .q) (hqmark : 0 < pulse.cycle.phases.markPhase.afterExit.x i .q) :
    pulse.cycle.phases.markPhase.afterExit.time +
        Real.log (pulse.cycle.phases.markPhase.afterExit.x i .q / (1 / 10)) /
          (s.x i .b + 1 / 10) = s.time +
      (Real.log (s.x i .q / (1 / 10)) +
        Cadence.markDeficit (pulse.cycle.trigger.afterMark.time - s.time) ((θ i).lm p)) /
          (s.x i .b + 1 / 10) := by
  have hf := pulse.mark_head_facts hb hv ha hr ho hno
  have hsol := pulse.cycle.markHead.slow_solution i
    (pulse.cycle.markHead.allStates_main_flows i .slow hf.1)
  have hlog : Real.log (pulse.cycle.phases.markPhase.afterExit.x i .q / (1 / 10)) =
      Real.log (s.x i .q / (1 / 10)) - pulse.cycle.markHead.accumulatedRecovery i := by
    rw [Real.log_div (ne_of_gt hqmark) (by norm_num),hsol,
      Real.log_mul (ne_of_gt hqin) (Real.exp_ne_zero _),Real.log_exp,
      Real.log_div (ne_of_gt hqin) (by norm_num)]
    ring
  rw [hlog,hf.2.2]
  apply mul_right_cancel₀ (ne_of_gt hB)
  simp only [add_mul,div_mul_cancel₀ _ (ne_of_gt hB)]
  ring

structure MixedSlowReturn {n θ route s u i p} {e : @Execution n θ route s u}
    (pulse : ShortMarkPulse e i p) extends ShortMarkReturn pulse where
  after_half : s.time + 1 / 2 < returnPhase.afterReturn.time
  before_deadline : returnPhase.afterReturn.time < s.time + 99 / 100

/-- These deliberately broad local state bands suffice for the first mixed
case in all three cells; no previous firing date or cadence word is required. -/
theorem ShortMarkPulse.mixed_slow_return {n θ ε route s u i p}
    {e : @Execution n θ route s u} (pulse : ShortMarkPulse e i p)
    (hb : PhysicalBox θ ε) (hv : RawValid s)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q)
    (hq : 61 / 500 ≤ s.x i .q ∧ s.x i .q ≤ 7 / 50)
    (hbRange : 27999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 28001 / 100000) :
    Nonempty (MixedSlowReturn pulse) := by
  have hf := pulse.mark_head_facts hb hv ha hr ho hno
  have hB : 0 < s.x i .b + 1 / 10 := by linarith [hbRange.1]
  have hqin : 0 < s.x i .q := by linarith [hq.1]
  have hsol := pulse.cycle.markHead.slow_solution i
    (pulse.cycle.markHead.allStates_main_flows i .slow hf.1)
  have hImax := pulse.cycle.markHead.accumulatedRecovery_upper i (by linarith [hbRange.2])
  have hIbound : pulse.cycle.markHead.accumulatedRecovery i ≤ 11 / 200 := by
    linarith [pulse.cycle.mark_ends_early hb]
  have hIpos := pulse.cycle.markHead.accumulatedRecovery_nonnegative hb i (by linarith [hbRange.1])
  have hqmark : 1 / 10 < pulse.cycle.phases.markPhase.afterExit.x i .q := by
    have he := Real.add_one_le_exp (-pulse.cycle.markHead.accumulatedRecovery i)
    have hp := mul_le_mul_of_nonneg_right hq.1
      (Real.exp_pos (-pulse.cycle.markHead.accumulatedRecovery i)).le
    rw [← hsol] at hp
    nlinarith
  have hqmarkUpper : pulse.cycle.phases.markPhase.afterExit.x i .q ≤ 7 / 50 := by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hIpos)
    have hp := mul_le_mul_of_nonneg_left he hqin.le
    rw [← hsol] at hp
    nlinarith [hq.2]
  have hlogUpper : Real.log (7 / 5 : ℝ) < 7 / 20 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).2
    have hh := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 20)
    norm_num at hh ⊢
    linarith
  have hlogMark : Real.log (pulse.cycle.phases.markPhase.afterExit.x i .q / (1 / 10)) < 7 / 20 := by
    apply lt_of_le_of_lt (Real.log_le_log (by positivity) (show
      pulse.cycle.phases.markPhase.afterExit.x i .q / (1 / 10) ≤ (7 / 5 : ℝ) by linarith)) hlogUpper
  have hquot : Real.log (pulse.cycle.phases.markPhase.afterExit.x i .q / (1 / 10)) /
      (s.x i .b + 1 / 10) < 94 / 100 := by
    apply (div_lt_iff₀ hB).2
    nlinarith [hbRange.1]
  have hdelay := pulse.mark_return_delay hb hv ha hr ho hno hB hqin (by linarith)
  have hdate : (Real.log (s.x i .q / (1 / 10)) +
      Cadence.markDeficit (pulse.cycle.trigger.afterMark.time - s.time) ((θ i).lm p)) /
        (s.x i .b + 1 / 10) < 99 / 100 := by
    linarith [pulse.cycle.mark_ends_early hb]
  obtain ⟨ret⟩ := pulse.slow_return_before_error hb hv ha hr ho hno hB hqmark hdate
  have hJ : 0 ≤ Cadence.markDeficit (pulse.cycle.trigger.afterMark.time - s.time) ((θ i).lm p) := by
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
    have hd : 0 ≤ ((1 / 10 : ℝ) - (2 / 5) * Real.log (5 / 4)) / (θ i).lm p := by
      apply div_nonneg _ (hb.rates_positive i p).1.le
      linarith
    dsimp [Cadence.markDeficit]
    linarith [pulse.cycle.trigger.early]
  have hlogLower : (22 / 111 : ℝ) ≤ Real.log (61 / 50 : ℝ) := by
    have hh := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 50)
    norm_num at hh ⊢
    exact hh
  have hlogInput : (22 / 111 : ℝ) ≤ Real.log (s.x i .q / (1 / 10)) := by
    apply hlogLower.trans (Real.log_le_log (by norm_num) ?_)
    linarith [hq.1]
  have hhalf : s.time + 1 / 2 < ret.returnPhase.afterReturn.time := by
    by_contra hn
    have hfrac : (Real.log (s.x i .q / (1 / 10)) +
        Cadence.markDeficit (pulse.cycle.trigger.afterMark.time - s.time) ((θ i).lm p)) /
          (s.x i .b + 1 / 10) ≤ 1 / 2 := by
      linarith [ret.date]
    have hh := (div_le_iff₀ hB).mp hfrac
    linarith [hbRange.2]
  exact ⟨⟨ret,hhalf,by linarith [ret.date]⟩⟩

end KernelR.Hybrid
