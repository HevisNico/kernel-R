import KernelR.HybridProtectedMark

/-! Recovery gained during the actual MARK yields a SLOW return before the next input. -/
namespace KernelR.Hybrid
open Set

theorem Execution.slow_no_overrun_of_charge {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (hm : e.MainFlows i .slow)
    (hq : 1 / 10 ≤ s.x i .q ∧ s.x i .q ≤ 1 / 4)
    (B : ℝ) (hB : 0 < B) (hs : B ≤ s.x i .b) : u.time ≤ s.time + Real.log (5 / 2) / B := by
  have hfloor := e.protected_main_floor i .slow (by decide) hm hq.1
  have hsol := e.slow_solution i hm
  have hquarter : 1 / 10 ≤ (1 / 4 : ℝ) * Real.exp (-e.accumulatedRecovery i) := by
    rw [hsol] at hfloor
    exact hfloor.trans (mul_le_mul_of_nonneg_right hq.2 (Real.exp_pos _).le)
  have hacc : e.accumulatedRecovery i ≤ Real.log (5 / 2) := by
    have hd := duration_le_of_decay_floor (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1) hquarter
      (show (1 / 4 : ℝ) * Real.exp (-e.accumulatedRecovery i) =
        (1 / 4 : ℝ) * Real.exp (-1 * e.accumulatedRecovery i) by ring_nf)
    norm_num at hd
    exact hd
  have hlo := e.accumulatedRecovery_lower hb i B hs
  have hdiv : u.time - s.time ≤ Real.log (5 / 2) / B := (le_div_iff₀ hB).mpr (by nlinarith)
  linarith

theorem Execution.slow_completion_of_charge {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (i : Fin n) (hs : s.main i = .slow)
    (hq : 1 / 10 ≤ s.x i .q ∧ s.x i .q ≤ 1 / 4)
    (B : ℝ) (hB : 0 < B) (hb₀ : B ≤ s.x i .b)
    (ht : s.time + Real.log (5 / 2) / B < u.time) :
    ∃ (v w : Snapshot n) (segment : Execution θ route s v) (exit : Jump route v w)
      (rest : Execution θ route w u),
      e = segment.append (.cons (.jump exit) rest) ∧
      segment.AllStates (fun v => v.main i = .slow) ∧ w.main i = .ready ∧
      w.x i .q = 1 / 10 ∧ w.time ≤ s.time + Real.log (5 / 2) / B := by
  rcases e.first_state_change (fun v => v.main i) .slow
    (fun f => congrFun f.main_fixed i) hs with h | ⟨v,w,segment,exit,rest,he,hstates,hv,hw⟩
  · have hlate := e.slow_no_overrun_of_charge hb i (e.allStates_main_flows i .slow h) hq B hB hb₀
    exact False.elim (not_lt_of_ge hlate ht)
  · have hbound := segment.slow_no_overrun_of_charge hb i (segment.allStates_main_flows i .slow hstates) hq B hB hb₀
    exact ⟨v,w,segment,exit,rest,he,hstates,exit.slow_main_departure i hv hw,
      by rw [exit.physical_continuous,exit.slow_departure_guard i hv hw],
      by rw [exit.time_unchanged]; exact hbound⟩

noncomputable def SensorCycle.markHead {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) : Execution θ route s cycle.phases.markPhase.afterExit :=
  cycle.trigger.span.append (.cons (.jump cycle.trigger.entry)
    (cycle.phases.markPhase.span.append (.cons (.jump cycle.phases.markPhase.exit) (.nil _))))

theorem SensorCycle.markHead_reconstruct {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) : e = cycle.markHead.append cycle.phases.markPhase.rest := by
  calc
    e = cycle.trigger.span.append (.cons (.jump cycle.trigger.entry) cycle.trigger.rest) := cycle.trigger.reconstruct
    _ = cycle.trigger.span.append (.cons (.jump cycle.trigger.entry)
        (cycle.phases.markPhase.span.append (.cons (.jump cycle.phases.markPhase.exit)
          cycle.phases.markPhase.rest))) :=
      congrArg (fun actual => cycle.trigger.span.append (.cons (.jump cycle.trigger.entry) actual))
        cycle.phases.markPhase.reconstruct
    _ = _ := by simp only [markHead,Execution.append_assoc,Execution.append]

theorem SensorCycle.markHead_recovery {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (hs : MarkEntry s i)
    (ho : ∀ q, q ≠ p → s.raw i q = none) (hno : ∀ q, NoArrivalAt e i q)
    (hd : cycle.phases.markPhase.span.ledger.mark i p = 1 / 10) :
    cycle.phases.markPhase.afterExit.x i .b = s.x i .b + 1 / 10 := by
  have hnoHead : ∀ q, NoArrivalAt cycle.markHead i q := by
    intro q
    have hn := hno q
    rw [cycle.markHead_reconstruct,Execution.noArrivalAt_append] at hn
    exact hn.1
  have hmark : cycle.markHead.ledger.mark i p = 1 / 10 := by
    have hz := cycle.trigger.span.mark_zero_aux i p .ready (by decide) cycle.trigger.flows
    simp [markHead,Execution.mark_append,Execution.ledger,Move.ledger,Ledger.add,
      Ledger.zero,cycle.trigger.entry.mark_zero,cycle.phases.markPhase.exit.mark_zero,hz,hd]
  have hother : ∀ q, q ≠ p → cycle.markHead.ledger.mark i q = 0 := by
    intro q hq
    have hquiet := cycle.markHead.aux_ready_without_input_band i q
      (hs.auxiliary q).1 (hs.auxiliary q).2.2 (ho q hq) (hnoHead q)
    exact cycle.markHead.mark_zero_aux i q .ready (by decide)
      (cycle.markHead.allStates_aux_flows i q .ready hquiet)
  rw [cycle.markHead.recovery_balance i,cycle.markHead.recovery_sum_marks i,
    Finset.sum_eq_single p (fun q _ hq => hother q hq) (by simp),hmark]

theorem SensorCycle.protected_return_of_invariant {n θ ε route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s)
    (hv : RawValid s) (hs : MarkEntry s i)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15 / 2 ≤ u.time) : Nonempty (ReadyReturn e i) := by
  let mk := cycle.phases.markPhase
  have hw := (cycle.protected_window hb hv hs hr ho hno).1
  have hd := (cycle.full_protected_mark_of_invariant hb hf hv hs hr ho hno).1
  have hdPhase : mk.span.ledger.mark i p = 1 / 10 := by
    rw [← cycle.mark_ledger_eq_phase hv hr (hno p)]; exact hd
  have hbrecovery := cycle.markHead_recovery hs ho hno hdPhase
  have hheadStates := hw
  rw [cycle.markHead_reconstruct,Execution.allStates_append] at hheadStates
  have hafterMain : mk.afterExit.main i = .slow :=
    cycle.markHead.allStates_final hheadStates.1 (by linarith [cycle.mark_ends_early hb])
  have hheadSlow : cycle.markHead.AllStates (fun v => v.main i = .slow) := by
    refine cycle.markHead.allStates_mono ?_
      (cycle.markHead.allStates_and hheadStates.1 cycle.markHead.allStates_time_bounds)
    intro v h
    exact h.1 (by have ht := h.2.2; linarith [cycle.mark_ends_early hb])
  have hqfloor := cycle.markHead.protected_main_floor i .slow (by decide)
    (cycle.markHead.allStates_main_flows i .slow hheadSlow) (by change 1 / 10 ≤ s.x i .q; linarith [hs.charge.1])
  have hI := cycle.markHead.accumulatedRecovery_nonnegative hb i (by linarith [hs.recovery.1])
  have hsol := cycle.markHead.slow_solution i (cycle.markHead.allStates_main_flows i .slow hheadSlow)
  have hqUpper : mk.afterExit.x i .q ≤ 1 / 4 := by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hI)
    have hp := mul_le_mul_of_nonneg_left he (show 0 ≤ s.x i .q by linarith [hs.charge.1])
    rw [hsol]
    nlinarith [hs.charge.2]
  have hB : (17999 / 100000 : ℝ) ≤ mk.afterExit.x i .b := by rw [hbrecovery]; linarith [hs.recovery.1]
  have hreturn := KernelR.stable_return_bound (b := (17999 / 100000 : ℝ))
    (f := mk.afterExit.time - s.time - 1) le_rfl (by linarith [cycle.mark_ends_early hb])
  have hdeadline : mk.afterExit.time + Real.log (5 / 2) / (17999 / 100000) < s.time + 6990787 / 1000000 := by
    linarith
  obtain ⟨a,b,slowSpan,slowExit,quietRest,heslow,hslow,hready,hq,hdate⟩ :=
    mk.rest.slow_completion_of_charge hb i hafterMain ⟨hqfloor,hqUpper⟩
      (17999 / 100000) (by norm_num) hB (by linarith)
  have hwindow := hheadStates.2
  rw [heslow,Execution.allStates_append] at hwindow
  have hwindowAfter := quietRest.allStates_initial hwindow.2.2
  have hafter : s.time + 419 / 300 < b.time := by
    by_contra hn
    have hbad := hwindowAfter (le_of_not_gt hn)
    rw [hready] at hbad
    contradiction
  have hraw := e.raw_expired_states i s.time hv
    (fun q => by
      by_cases hq : q = p
      · subst q; exact Or.inr hr
      · exact Or.inl (ho q hq)) hno
  rw [cycle.markHead_reconstruct,Execution.allStates_append] at hraw
  have hrawRest := hraw.2
  rw [heslow,Execution.allStates_append] at hrawRest
  refine ⟨⟨a,b,cycle.markHead.append slowSpan,slowExit,quietRest,?_,hready,hq,
    quietRest.allStates_initial hrawRest.2.2 (by linarith),by linarith⟩⟩
  calc
    e = cycle.markHead.append mk.rest := cycle.markHead_reconstruct
    _ = _ := by rw [heslow,Execution.append_assoc]

theorem SensorCycle.protected_return {n θ ε route born s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (past : Execution θ route born s) (hborn : BirthState born)
    (hb : PhysicalBox θ ε) (hs : MarkEntry s i)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 15 / 2 ≤ u.time) : Nonempty (ReadyReturn e i) := by
  exact cycle.protected_return_of_invariant hb (past.physical_invariant hb (hborn.physical_invariant hb))
    (past.raw_valid hborn.raw_valid) hs hr ho hno ht

end KernelR.Hybrid
