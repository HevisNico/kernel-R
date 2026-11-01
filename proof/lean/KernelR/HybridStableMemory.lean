import KernelR.HybridReadyReturn

/-! Actual MARK gates and quiescent sensors preserve learned memories. -/
namespace KernelR.Hybrid
open Set

theorem Execution.aux_ready_without_input_band {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (hs : s.aux i p = .ready) (hx : s.x i (.m p) ≤ 1 / 40 + 1 / 100000)
    (hr : s.raw i p = none) (hno : NoArrivalAt e i p) :
    e.AllStates (fun v => v.aux i p = .ready) := by
  rcases e.first_state_change (fun v => v.aux i p) .ready
    (fun f => congrFun (congrFun f.aux_fixed i) p) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · exact h
  · have hp : e.IsPrefix segment := by rw [he]; exact .append_left _ _
    have hraw := (segment.raw_absent_of_no_arrival i p hr (hp.no_arrival i p hno)).2
    have hsol := segment.aux_ready_no_current_solution i p (segment.allStates_aux_flows i p .ready hstates) hraw
    have hg := exit.ready_aux_departure i p hv hw
    have hd := decay_upper (show s.x i (.m p) - 1 / 40 ≤ (1 / 100000 : ℝ) by linarith)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2) (sub_nonneg.mpr segment.time_monotone)
    rw [hg.1] at hsol
    linarith

theorem MainTrigger.ready_before_fire {n θ route s u i} {e : @Execution n θ route s u}
    (tr : MainTrigger e i) : e.AllStates (fun v => v.time < tr.afterFire.time → v.main i = .ready) := by
  let P : Snapshot n → Prop := fun v => v.time < tr.afterFire.time → v.main i = .ready
  change e.AllStates P
  have hspan : tr.span.AllStates (fun v => v.time < tr.afterFire.time → v.main i = .ready) :=
    tr.span.allStates_mono (fun v hv _ => hv) tr.ready_states
  have hrest : tr.rest.AllStates (fun v => v.time < tr.afterFire.time → v.main i = .ready) :=
    tr.rest.allStates_mono (fun v hv ht => False.elim (not_lt_of_ge hv.1 ht)) tr.rest.allStates_time_bounds
  rw [tr.reconstruct,Execution.allStates_append]
  exact ⟨hspan,tr.span.allStates_final hspan,hrest⟩

theorem PhysicalBox.mark_duration_upper {n θ ε} (hb : @PhysicalBox n θ ε) (i : Fin n) (p : Port) :
    Real.log (5 / 4) / (θ i).lm p ≤ 1 / 45 := by
  have h := (hb.2 i p).2.1.1
  have hl : 0 < Real.log (5 / 4 : ℝ) := Real.log_pos (by norm_num)
  have he := mul_le_mul_of_nonneg_left hb.epsilon_bounds.2 hl.le
  norm_num at h
  apply (div_le_iff₀ (hb.rates_positive i p).1).mpr
  nlinarith

theorem SensorCycle.mark_ends_early {n θ ε route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (hb : PhysicalBox θ ε) :
    cycle.phases.markPhase.afterExit.time < s.time + 1 / 20 := by
  have hremaining : auxRemaining θ cycle.trigger.afterMark i p .mark = Real.log (5 / 4) / (θ i).lm p := by
    norm_num [auxRemaining,protectedFloor,auxRate,cycle.trigger.charge]
  rw [cycle.phases.markPhase.after_time,hremaining]
  linarith [cycle.trigger.deadline,hb.mark_duration_upper i p]

theorem SensorCycle.mark_states {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) {P : Snapshot n → Prop} (h : e.AllStates P) :
    cycle.phases.markPhase.span.AllStates P := by
  rw [cycle.trigger.reconstruct,Execution.allStates_append] at h
  have hrest := h.2.2
  rw [cycle.phases.markPhase.reconstruct,Execution.allStates_append] at hrest
  exact hrest.1

theorem Jump.mark_zero {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port) : j.ledger.mark i p = 0 := by
  cases j <;> rfl

theorem Execution.mark_zero_aux {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (mode : AuxMode) (hne : mode ≠ .mark) (hm : e.AuxFlows i p mode) :
    e.ledger.mark i p = 0 := by
  induction e with
  | nil => rfl
  | @cons s v u move rest ih => cases move with
    | flow f =>
      have hrest := ih hm.2
      have hmode : s.aux i p = mode := hm.1
      simp [Execution.ledger,Move.ledger,Ledger.add,Flow.ledger,markAct,hmode,hne,hrest]
    | jump j => simp [Execution.ledger,Move.ledger,Ledger.add,j.mark_zero,ih hm]

theorem Execution.mark_zero_ready {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (hm : e.MainFlows i .ready) : e.ledger.mark i p = 0 := by
  induction e with
  | nil => rfl
  | @cons s v u move rest ih => cases move with
    | flow f =>
      have hrest := ih hm.2
      have hmode : s.main i = .ready := hm.1
      simp [Execution.ledger,Move.ledger,Ledger.add,Flow.ledger,markAct,hmode,hrest]
    | jump j => simp [Execution.ledger,Move.ledger,Ledger.add,j.mark_zero,ih hm]

theorem Execution.mark_append {n θ route s v u} (segment : @Execution n θ route s v)
    (rest : Execution θ route v u) (i : Fin n) (p : Port) :
    (segment.append rest).ledger.mark i p = segment.ledger.mark i p + rest.ledger.mark i p := by
  induction segment with
  | nil => simp [append,ledger,Ledger.zero]
  | cons move tail ih => simp only [append,ledger,Ledger.add,ih,add_assoc]

theorem Execution.mark_skip_zero_head {n θ route s u v w} (e : @Execution n θ route s u)
    (segment : Execution θ route s v) (exit : Jump route v w) (rest : Execution θ route w u)
    (he : e = segment.append (.cons (.jump exit) rest)) (i : Fin n) (p : Port)
    (hs : segment.ledger.mark i p = 0) : e.ledger.mark i p = rest.ledger.mark i p := by
  calc
    e.ledger.mark i p = (segment.append (.cons (.jump exit) rest)).ledger.mark i p :=
      congrArg (fun actual => actual.ledger.mark i p) he
    _ = _ := by simp [mark_append,ledger,Move.ledger,Ledger.add,exit.mark_zero,hs]

theorem SensorCycle.error_rest_ready {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (hv₀ : RawValid s) (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p) :
    cycle.phases.errorPhase.rest.AllStates (fun v => v.aux i p = .ready) := by
  let er := cycle.phases.errorPhase
  have hvalid := e.allStates_raw_valid hv₀
  have hallowed := e.raw_allowed_states i p s.time (Or.inr hr) hno
  have hv := er.rest.allStates_initial (cycle.error_states hvalid).2
  have ha := er.rest.allStates_initial (cycle.error_states hallowed).2
  have hraw : er.afterExit.raw i p = none := by
    rcases ha with h | h
    · exact h
    · exact False.elim (not_lt_of_ge (hv i p s.time h).2 cycle.ready_after_raw)
  exact er.rest.aux_ready_without_input i p cycle.phases.ready_mode
    (by simpa only [protectedFloor] using er.after_charge.le) hraw (cycle.error_rest_no_arrival p hno)

theorem SensorCycle.mark_zero_of_trigger {n θ ε route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (tr : MainTrigger e i) (hb : PhysicalBox θ ε)
    (hv₀ : RawValid s) (hr : s.raw i p = some s.time) (hno : NoArrivalAt e i p) :
    e.ledger.mark i p = 0 := by
  let st := cycle.trigger
  let mk := cycle.phases.markPhase
  let si := cycle.phases.silentPhase
  let er := cycle.phases.errorPhase
  have hmarkMain := cycle.mark_states tr.ready_before_fire
  have hend : mk.beforeExit.time < s.time + 1 / 20 := by
    rw [← mk.exit.time_unchanged]; exact cycle.mark_ends_early hb
  have hmarkReady : mk.span.AllStates (fun v => v.main i = .ready) := by
    refine mk.span.allStates_mono ?_ (mk.span.allStates_and hmarkMain mk.span.allStates_time_bounds)
    intro v h
    exact h.1 (by have ht := h.2.2; linarith [tr.early])
  have hst := e.mark_skip_zero_head st.span st.entry st.rest st.reconstruct i p
    (st.span.mark_zero_aux i p .ready (by decide) st.flows)
  have hmk := st.rest.mark_skip_zero_head mk.span mk.exit mk.rest mk.reconstruct i p
    (mk.span.mark_zero_ready i p (mk.span.allStates_main_flows i .ready hmarkReady))
  have hsi := mk.rest.mark_skip_zero_head si.span si.exit si.rest si.reconstruct i p
    (si.span.mark_zero_aux i p .silent (by decide) si.flows)
  have her := si.rest.mark_skip_zero_head er.span er.exit er.rest er.reconstruct i p
    (er.span.mark_zero_aux i p .error (by decide) er.flows)
  have htail := er.rest.mark_zero_aux i p .ready (by decide)
    (er.rest.allStates_aux_flows i p .ready (cycle.error_rest_ready hv₀ hr hno))
  exact hst.trans (hmk.trans (hsi.trans (her.trans htail)))

theorem Execution.learned_recovery_unchanged {n θ ε route s u i p} (e : @Execution n θ route s u)
    (cycle : SensorCycle e i p) (tr : MainTrigger e i) (hb : PhysicalBox θ ε)
    (hv₀ : RawValid s) (hr : s.raw i p = some s.time) (hno : ∀ q, NoArrivalAt e i q)
    (ho : ∀ q, q ≠ p → s.raw i q = none)
    (ha : ∀ q, q ≠ p → s.aux i q = .ready ∧ s.x i (.m q) ≤ 1 / 40 + 1 / 100000) :
    u.x i .b = s.x i .b := by
  have hmark : ∀ q, e.ledger.mark i q = 0 := by
    intro q
    by_cases hq : q = p
    · subst q; exact cycle.mark_zero_of_trigger tr hb hv₀ hr (hno p)
    · have hquiet := e.aux_ready_without_input_band i q (ha q hq).1 (ha q hq).2 (ho q hq) (hno q)
      exact e.mark_zero_aux i q .ready (by decide) (e.allStates_aux_flows i q .ready hquiet)
  rw [e.recovery_balance i,e.recovery_sum_marks i]
  simp [hmark]

end KernelR.Hybrid
