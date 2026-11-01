import KernelR.HybridHighGainTrigger

/-! Actual high-gain pulse closure before the next cadence input. -/
namespace KernelR.Hybrid
open Set

theorem HighGainTrigger.ready_before_fire {n θ route s u i} {e : @Execution n θ route s u}
    (tr : HighGainTrigger e i) : e.AllStates (fun v => v.time < tr.afterFire.time → v.main i = .ready) := by
  let P : Snapshot n → Prop := fun v => v.time < tr.afterFire.time → v.main i = .ready
  change e.AllStates P
  have hspan : tr.span.AllStates (fun v => v.time < tr.afterFire.time → v.main i = .ready) :=
    tr.span.allStates_mono (fun v hv _ => hv) tr.ready_states
  have hrest : tr.rest.AllStates (fun v => v.time < tr.afterFire.time → v.main i = .ready) :=
    tr.rest.allStates_mono (fun v hv ht => False.elim (not_lt_of_ge hv.1 ht)) tr.rest.allStates_time_bounds
  rw [tr.reconstruct,Execution.allStates_append]
  exact ⟨hspan,tr.span.allStates_final hspan,hrest⟩


theorem HighGainTrigger.only_emission_of_valid {n θ route s u i} {e : @Execution n θ route s u}
    (tr : HighGainTrigger e i) (hv : RawValid s)
    (p : Port) (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) : e.emissionTimes i = [tr.beforeFire.time] := by
  have hraw := e.raw_expired_states i s.time hv
    (fun q => by
      by_cases hq : q = p
      · subst q; exact Or.inr hr
      · exact Or.inl (ho q hq)) hno
  rw [tr.reconstruct,Execution.allStates_append] at hraw
  have hnoRest : ∀ q, NoArrivalAt tr.rest i q := by
    intro q
    have hn := hno q
    rw [tr.reconstruct,Execution.noArrivalAt_append] at hn
    exact fun d hd => hn.2 d (List.mem_append_right _ hd)
  have hquiet := tr.rest.fast_tail_no_emissions i s.time tr.fast_after tr.charge
    (by linarith [tr.early]) hraw.2.2 hnoRest
  rw [tr.emission_times,hquiet]


theorem HighGainTrigger.sensor_window_protected {n θ route s u i} {e : @Execution n θ route s u}
    (tr : HighGainTrigger e i) (hb : s.x i .b ≤ 11 / 10) :
    e.AllStates (fun v => s.time + 99 / 100 ≤ v.time → v.time ≤ s.time + 419 / 300 → v.main i ≠ .ready) := by
  have hcap : tr.afterFire.x i .b ≤ 11 / 10 := by
    rw [tr.entry.physical_continuous]; exact tr.span.recovery_cap i hb
  have hprotected := tr.rest.fast_protected_until i tr.fast_after tr.charge hcap
  have hrest : tr.rest.AllStates (fun v => s.time + 99 / 100 ≤ v.time → v.time ≤ s.time + 419 / 300 → v.main i ≠ .ready) := tr.rest.allStates_mono (fun v hv _ (ht : v.time ≤ s.time + 419 / 300) =>
    hv (by linarith [tr.early])) hprotected
  have hdeadline : tr.beforeFire.time < s.time + 9 / 10 := by
    simpa only [tr.entry.time_unchanged] using tr.deadline
  have hspan : tr.span.AllStates (fun v => s.time + 99 / 100 ≤ v.time → v.time ≤ s.time + 419 / 300 → v.main i ≠ .ready) := tr.span.allStates_mono
    (fun v hv (ht : s.time + 99 / 100 ≤ v.time) _ => False.elim (by have h := hv.2; linarith))
    tr.span.allStates_time_bounds
  rw [tr.reconstruct,Execution.allStates_append]
  exact ⟨hspan,tr.span.allStates_final hspan,hrest⟩


theorem SensorCycle.error_protected_by_high_gain_trigger {n θ route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (tr : HighGainTrigger e i) (hb : s.x i .b ≤ 11 / 10) :
    cycle.phases.errorPhase.span.AllStates (fun v => v.main i ≠ .ready) := by
  let er := cycle.phases.errorPhase
  have hmain := (cycle.error_states (tr.sensor_window_protected hb)).1
  have hupper : er.beforeExit.time < s.time + 419 / 300 := by
    rw [← er.exit.time_unchanged]; exact cycle.ready_deadline
  refine er.span.allStates_mono ?_ (er.span.allStates_and hmain er.span.allStates_time_bounds)
  intro v h
  exact h.1 (by have ht := h.2.1; linarith [cycle.error_starts_late])
    (by have ht := h.2.2; linarith)


theorem SensorCycle.mark_zero_of_high_gain_trigger {n θ ε route s u i p} {e : @Execution n θ route s u}
    (cycle : SensorCycle e i p) (tr : HighGainTrigger e i) (hb : PhysicalBox θ ε)
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


theorem HighGainTrigger.ready_return_of_valid {n θ ε route s u i} {e : @Execution n θ route s u}
    (tr : HighGainTrigger e i) (hv : RawValid s)
    (hb : PhysicalBox θ ε) (hb₀ : 37999 / 100000 ≤ s.x i .b)
    (p : Port) (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (hsharp : tr.afterFire.time < s.time + 3 / 10)
    (ht : s.time + 19 / 5 ≤ u.time) :
    ∃ ret : ReadyReturn e i, ret.afterReturn.time < s.time + 19 / 5 := by
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
    have hbfire : (37999 / 100000 : ℝ) ≤ tr.afterFire.x i .b := by
      rw [tr.entry.physical_continuous]; exact hb₀.trans (tr.span.recovery_nondecreasing hb i)
    have hbslow : (37999 / 100000 : ℝ) ≤ w.x i .b := by
      rw [fastExit.physical_continuous]; exact hbfire.trans (fastSpan.recovery_nondecreasing hb i)
    have hlog : Real.log (5 / 2 : ℝ) / (37999 / 100000) < 5 / 2 := by
      apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 37999 / 100000)).mpr
      linarith [KernelR.log_recovery_bounds.2]
    have hbound : w.time + Real.log (5 / 2) / (37999 / 100000) < s.time + 19 / 5 := by
      rw [hwtime]; linarith
    obtain ⟨a,b,slowSpan,slowExit,quietRest,heslow,hslow,hbready,hbq,hbtime⟩ :=
      slowRest.slow_phase_completion hb i hguard.2 hqslow (37999 / 100000) (by norm_num) hbslow (by linarith)
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
    have hbdeadline : b.time < s.time + 19 / 5 := hbtime.trans_lt hbound
    refine ⟨⟨a,b,head,slowExit,quietRest,?_,hbready,hbq,hraw_b hafterRaw,by linarith⟩,hbdeadline⟩
    calc
      e = tr.span.append (.cons (.jump tr.entry) tr.rest) := tr.reconstruct
      _ = _ := by rw [hefast,heslow]; simp only [head,Execution.append_assoc,Execution.append]



/-- A closed learned pulse at general recovery, without the old b≈0.18 section. -/
structure CadenceLearnedPulse {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) where
  trigger : HighGainTrigger e i
  admission_return : ReadyReturn e i
  return_deadline : admission_return.afterReturn.time < s.time + 19 / 5
  emissions : e.emissionTimes i = [trigger.beforeFire.time]
  error_zero : ∀ p, e.ledger.error i p = 0
  mark_zero : ∀ p, e.ledger.mark i p = 0
  gain_preserved : ∀ p, u.x i (.z p) = s.x i (.z p)
  recovery_preserved : u.x i .b = s.x i .b
  ready : u.main i = .ready
  charge_rest : u.x i .q = 1 / 10
  auxiliary : ∀ p, u.aux i p = .ready ∧ RestBand (u.x i (.m p))
  raw_finished : ∀ p, u.raw i p = none

/-- All events and doses are derived from a fresh physical input and guards. -/
theorem Execution.high_gain_pulse_of_valid {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s) (i : Fin n) (p : Port)
    (hm : s.main i = .ready)
    (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 1 / 2)
    (hz : 16 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 7 / 2)
    (hrec : 37999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 11 / 10)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 19 / 5 ≤ u.time) :
    Nonempty (CadenceLearnedPulse e i) := by
  obtain ⟨tr⟩ := e.high_gain_input_trigger hb hi i p hm hq ⟨by linarith [hz.1],hz.2⟩
    (ha p).1 hr (ha p).2 ho hno (by linarith)
  have hsharp := tr.high_gain_deadline hb hi p hr hq.1 hz.1
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p (ha p).1 hr (ha p).2 (by linarith)
  obtain ⟨ret,hret⟩ := tr.ready_return_of_valid hv hb hrec.1 p hr ho hno hsharp ht
  have hu := ret.final_ready hno
  have hzero := cycle.error_zero_of_protected hv hr (hno p)
    (cycle.error_protected_by_high_gain_trigger tr hrec.2)
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
    · subst q; exact cycle.mark_zero_of_high_gain_trigger tr hb hv hr (hno p)
    · have hquiet := e.aux_ready_without_input_band i q (ha q).1 (ha q).2.2 (ho q hq) (hno q)
      exact e.mark_zero_aux i q .ready (by decide) (e.allStates_aux_flows i q .ready hquiet)
  have hbfinal : u.x i .b = s.x i .b := by
    rw [e.recovery_balance i,e.recovery_sum_marks i]
    simp [hmark]
  have hraw := e.raw_expired_states i s.time hv
    (fun q => by
      by_cases hq : q = p
      · subst q; exact Or.inr hr
      · exact Or.inl (ho q hq)) hno
  refine ⟨⟨tr,ret,hret,tr.only_emission_of_valid hv p hr ho hno,?_,hmark,hgain,hbfinal,
    hu.1,hu.2,?_,?_⟩⟩
  · intro q
    have h := e.gain_balance i q
    rw [hgain q] at h
    linarith
  · intro q
    by_cases hq : q = p
    · subst q
      exact ⟨htarget.1,by rw [htarget.2]; norm_num [RestBand]⟩
    · exact (hother q hq).1
  · exact e.allStates_final hraw (by linarith)

end KernelR.Hybrid
