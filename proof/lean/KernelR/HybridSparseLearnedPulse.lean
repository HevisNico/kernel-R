import KernelR.HybridResidualPreparedCalendar

/-! Seven-unit sparse learned inputs preserve the existing LearnedPulse and
PreparedTrain contracts. Actual residual charge remains in the first latency. -/
namespace KernelR.Hybrid
open Set

theorem MainTrigger.sparse_ready_return_of_valid {n θ ε route s u i} {e : @Execution n θ route s u}
    (tr : MainTrigger e i) (hv : RawValid s)
    (hb : PhysicalBox θ ε) (hb₀ : 17999 / 100000 ≤ s.x i .b)
    (p : Port) (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 7 ≤ u.time) : Nonempty (ReadyReturn e i) := by
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


theorem MainTrigger.sparse_prepared_case_of_valid {n θ ε route s u i} {e : @Execution n θ route s u}
    (tr : MainTrigger e i)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s)
    (p : Port) (hs : PreparedSection s i)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 7 ≤ u.time) : Nonempty (LearnedPulse e i) := by
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p (hs.auxiliary p).1 hr (hs.auxiliary p).2 (by linarith)
  obtain ⟨ret⟩ := tr.sparse_ready_return_of_valid hv hb hs.recovery.1 p hr ho hno ht
  have hu := ret.final_ready hno
  have hzero := cycle.error_zero_of_protected hv hr (hno p)
    (cycle.error_protected_by_trigger tr (by linarith [hs.recovery.2]))
  have hbfinal := e.learned_recovery_unchanged cycle tr hb hv hr hno ho
    (fun q _ => ⟨(hs.auxiliary q).1,(hs.auxiliary q).2.2⟩)
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
  have hraw := e.raw_expired_states i s.time hv
    (fun q => by
      by_cases hq : q = p
      · subst q; exact Or.inr hr
      · exact Or.inl (ho q hq)) hno
  refine ⟨⟨tr,ret,tr.only_emission_of_valid hv p hr ho hno,?_,hmark,hgain,hbfinal,?_,hu.2,?_⟩⟩
  · intro q
    have h := e.gain_balance i q
    rw [hgain q] at h
    linarith
  · refine ⟨hu.1,by rw [hu.2]; norm_num,by rw [hbfinal]; exact hs.recovery,?_⟩
    intro q
    by_cases hq : q = p
    · subst q
      exact ⟨htarget.1,by rw [htarget.2]; norm_num [RestBand]⟩
    · exact (hother q hq).1
  · exact e.allStates_final hraw (by linarith)



/-- A fresh isolated learned input needs only seven units to complete its
proved return before 6.990787; the original LearnedPulse fields are unchanged. -/
theorem Execution.sparse_learned_pulse_of_valid {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hi : UpperRegion s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hs : PreparedSection s i)
    (hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 7 ≤ u.time) : Nonempty (LearnedPulse e i) := by
  obtain ⟨tr⟩ := e.mid_gain_input_trigger hb hi i p hs.ready hs.charge hz
    (hs.auxiliary p).1 hr (hs.auxiliary p).2 ho hno (by linarith)
  exact tr.sparse_prepared_case_of_valid hb hi hv p hs hr ho hno ht

theorem sparse_prepared_cell_train_of_valid {n θ ε route} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) : ∀ (times : List ℝ) {s u : Snapshot n} (e : Execution θ route s u)
    (_hi : UpperRegion s) (_hv : RawValid s) (_hs : PreparedSection s i)
    (_hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (_hr : s.raw i p = some s.time) (_ho : ∀ q, q ≠ p → s.raw i q = none)
    (_hcalendar : e.cellDeliveries i = times.map (fun t => ⟨i,p,t⟩))
    (_hspace : (s.time :: times).Pairwise (fun t v => t + 7 ≤ v))
    (_hquiet : ∀ t ∈ s.time :: times, t + 7 ≤ u.time),
    Nonempty (PreparedTrain e i (times.length + 1)) := by
  intro times
  induction times with
  | nil =>
    intro s u e hi hv hs hz hr ho hcalendar hspace hquiet
    have hn : ∀ q, NoArrivalAt e i q := (e.cellDeliveries_empty_iff i).mp (by simpa using hcalendar)
    obtain ⟨pulse⟩ := e.sparse_learned_pulse_of_valid hb hi hv i p hs hz hr ho hn (hquiet s.time (by simp))
    exact ⟨⟨by rw [pulse.emissions]; rfl,pulse.error_zero,pulse.mark_zero,pulse.gain_preserved,
      pulse.recovery_preserved,pulse.prepared,pulse.charge_rest,pulse.raw_finished⟩⟩
  | cons next times ih =>
    intro s u e hi hv hs hz hr ho hcalendar hspace hquiet
    have hcal : e.cellDeliveries i = ⟨i,p,next⟩ :: times.map (fun t => ⟨i,p,t⟩) := by simpa using hcalendar
    obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcal
    have hdate := cut.date
    have hgap : s.time + 7 ≤ next := (List.pairwise_cons.mp hspace).1 next (by simp)
    obtain ⟨pulse⟩ := cut.span.sparse_learned_pulse_of_valid hb hi hv i p hs hz hr ho
      cut.no_arrivals_before (by rw [hdate.1]; exact hgap)
    have hnext := cut.prepared pulse.prepared
    have hznext : 9 / 5 ≤ Real.exp (cut.afterArrival.x i (.z p)) ∧
        Real.exp (cut.afterArrival.x i (.z p)) ≤ 12 / 5 := by
      rw [cut.entry.physical_continuous,pulse.gain_preserved p]
      exact hz
    have hrnext : cut.afterArrival.raw i p = some cut.afterArrival.time := cut.raw_after
    have honext : ∀ q, q ≠ p → cut.afterArrival.raw i q = none := by
      intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
    have hspaceNext : (cut.afterArrival.time :: times).Pairwise (fun t v => t + 7 ≤ v) := by
      rw [hdate.2]
      exact (List.pairwise_cons.mp hspace).2
    have hquietNext : ∀ t ∈ cut.afterArrival.time :: times, t + 7 ≤ u.time := by
      rw [hdate.2]
      intro t ht
      exact hquiet t (List.mem_cons_of_mem _ ht)
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    have hinext := advanced.upper_region hb hi
    have hvnext := advanced.raw_valid hv
    obtain ⟨train⟩ := ih cut.rest hinext hvnext hnext hznext hrnext honext cut.later hspaceNext hquietNext
    have hg : ∀ q, u.x i (.z q) = s.x i (.z q) := by
      intro q
      rw [train.gain_preserved q,cut.entry.physical_continuous,pulse.gain_preserved q]
    refine ⟨⟨?_,?_,?_,hg,?_,train.prepared,train.charge_rest,train.raw_finished⟩⟩
    · rw [cut.emissions,List.length_append,pulse.emissions,train.emissions]
      simp only [List.length_cons,List.length_nil]
      omega
    · intro q
      have h := e.gain_balance i q
      rw [hg q] at h
      linarith
    · intro q
      have hsplit := e.mark_split cut.span cut.entry cut.rest cut.reconstruct i q
      rw [pulse.mark_zero q,train.mark_zero q] at hsplit
      simpa only [zero_add] using hsplit
    · rw [train.recovery_preserved,cut.entry.physical_continuous,pulse.recovery_preserved]


theorem LearnedPulse.sparse_emission_at_rest {n θ ε route s u i} {e : @Execution n θ route s u}
    (pulse : LearnedPulse e i) (hb : PhysicalBox θ ε) (hi : UpperRegion s)
    (p : Port) (hs : PreparedSection s i) (hq : s.x i .q = 1 / 10)
    (hg : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 7 ≤ u.time) :
    e.emissionTimes i = [s.time + restLatency (Real.exp (s.x i (.z p)))] := by
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p (hs.auxiliary p).1 hr (hs.auxiliary p).2 (by linarith)
  have hroot := pulse.trigger.firing_equation cycle hr ho hno
  rw [hq] at hroot
  have hshift : readyPulse (1 / 10) (Real.exp (s.x i (.z p))) 0
      (pulse.trigger.beforeFire.time - s.time) = 1 := by
    simpa only [readyPulse,sub_zero] using hroot
  have hlo : s.time + 3 / 10 < pulse.trigger.beforeFire.time := by
    simpa only [pulse.trigger.entry.time_unchanged] using pulse.trigger.early
  have hhi : pulse.trigger.beforeFire.time < s.time + 9 / 10 := by
    simpa only [pulse.trigger.entry.time_unchanged] using pulse.trigger.deadline
  have heq := restLatency_unique hg
    (t := pulse.trigger.beforeFire.time - s.time) ⟨by linarith,by linarith⟩ hshift
  rw [pulse.emissions]
  congr 1
  linarith


theorem sparse_prepared_cell_calendar_of_valid {n θ ε route} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) : ∀ (times : List ℝ) {s u : Snapshot n} (e : Execution θ route s u)
    (_hi : UpperRegion s) (_hv : RawValid s) (_hs : PreparedSection s i)
    (_hq : s.x i .q = 1 / 10)
    (_hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (_hr : s.raw i p = some s.time) (_ho : ∀ q, q ≠ p → s.raw i q = none)
    (_hcalendar : e.cellDeliveries i = times.map (fun t => ⟨i,p,t⟩))
    (_hspace : (s.time :: times).Pairwise (fun t v => t + 7 ≤ v))
    (_hquiet : ∀ t ∈ s.time :: times, t + 7 ≤ u.time),
    e.emissionTimes i = (s.time :: times).map (fun t => t + restLatency (Real.exp (s.x i (.z p)))) := by
  intro times
  induction times with
  | nil =>
    intro s u e hi hv hs hq hz hr ho hcalendar hspace hquiet
    have hn : ∀ q, NoArrivalAt e i q := (e.cellDeliveries_empty_iff i).mp (by simpa using hcalendar)
    obtain ⟨pulse⟩ := e.sparse_learned_pulse_of_valid hb hi hv i p hs hz hr ho hn (hquiet s.time (by simp))
    simpa only [List.map_cons,List.map_nil] using pulse.sparse_emission_at_rest hb hi p hs hq hz hr ho hn (hquiet s.time (by simp))
  | cons next times ih =>
    intro s u e hi hv hs hq hz hr ho hcalendar hspace hquiet
    have hcal : e.cellDeliveries i = ⟨i,p,next⟩ :: times.map (fun t => ⟨i,p,t⟩) := by simpa using hcalendar
    obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcal
    have hdate := cut.date
    have hgap : s.time + 7 ≤ next := (List.pairwise_cons.mp hspace).1 next (by simp)
    obtain ⟨pulse⟩ := cut.span.sparse_learned_pulse_of_valid hb hi hv i p hs hz hr ho
      cut.no_arrivals_before (by rw [hdate.1]; exact hgap)
    have hem := pulse.sparse_emission_at_rest hb hi p hs hq hz hr ho cut.no_arrivals_before
      (by rw [hdate.1]; exact hgap)
    have hnext := cut.prepared pulse.prepared
    have hx : cut.afterArrival.x i (.z p) = s.x i (.z p) := by
      rw [cut.entry.physical_continuous,pulse.gain_preserved p]
    have hqnext : cut.afterArrival.x i .q = 1 / 10 := by
      rw [cut.entry.physical_continuous,pulse.charge_rest]
    have hznext : 9 / 5 ≤ Real.exp (cut.afterArrival.x i (.z p)) ∧
        Real.exp (cut.afterArrival.x i (.z p)) ≤ 12 / 5 := by rw [hx]; exact hz
    have hrnext : cut.afterArrival.raw i p = some cut.afterArrival.time := cut.raw_after
    have honext : ∀ q, q ≠ p → cut.afterArrival.raw i q = none := by
      intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
    have hspaceNext : (cut.afterArrival.time :: times).Pairwise (fun t v => t + 7 ≤ v) := by
      rw [hdate.2]
      exact (List.pairwise_cons.mp hspace).2
    have hquietNext : ∀ t ∈ cut.afterArrival.time :: times, t + 7 ≤ u.time := by
      rw [hdate.2]
      intro t ht
      exact hquiet t (List.mem_cons_of_mem _ ht)
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    have htail := ih cut.rest (advanced.upper_region hb hi) (advanced.raw_valid hv) hnext hqnext hznext
      hrnext honext cut.later hspaceNext hquietNext
    rw [hx,hdate.2] at htail
    rw [cut.emissions,hem,htail]
    rfl

theorem LearnedPulse.sparse_latency_le_rest {n θ ε route s u i} {e : @Execution n θ route s u}
    (pulse : LearnedPulse e i) (hb : PhysicalBox θ ε) (hi : UpperRegion s)
    (p : Port) (hs : PreparedSection s i) (hq : 1 / 10 ≤ s.x i .q)
    (hg : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 7 ≤ u.time) :
    pulse.trigger.beforeFire.time - s.time ≤ restLatency (Real.exp (s.x i (.z p))) := by
  obtain ⟨cycle⟩ := e.sensor_cycle hb hi i p (hs.auxiliary p).1 hr (hs.auxiliary p).2 (by linarith)
  have hroot := pulse.trigger.firing_equation cycle hr ho hno
  have hshift : readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) 0
      (pulse.trigger.beforeFire.time - s.time) = 1 := by
    simpa only [readyPulse,sub_zero] using hroot
  have hlo : s.time + 3 / 10 < pulse.trigger.beforeFire.time := by
    simpa only [pulse.trigger.entry.time_unchanged] using pulse.trigger.early
  have hhi : pulse.trigger.beforeFire.time < s.time + 9 / 10 := by
    simpa only [pulse.trigger.entry.time_unchanged] using pulse.trigger.deadline
  have hsref := restLatency_spec hg
  exact first_firing_le_rest_reference hq hg.1
    ⟨by linarith,by linarith⟩ ⟨by linarith [hsref.1],by linarith [hsref.2.1]⟩ hshift hsref.2.2

theorem LearnedPulse.sparse_residual_calendar {n θ ε route s u i} {e : @Execution n θ route s u}
    (pulse : LearnedPulse e i) (hb : PhysicalBox θ ε) (hi : UpperRegion s)
    (p : Port) (hs : PreparedSection s i) (hq : 1 / 10 ≤ s.x i .q)
    (hg : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) (ht : s.time + 7 ≤ u.time) :
    ∃ first : ℝ, 3 / 10 < first ∧ first < 9 / 10 ∧
      first ≤ restLatency (Real.exp (s.x i (.z p))) ∧ e.emissionTimes i = [s.time + first] := by
  let first := pulse.trigger.beforeFire.time - s.time
  have hlo : s.time + 3 / 10 < pulse.trigger.beforeFire.time := by
    simpa only [pulse.trigger.entry.time_unchanged] using pulse.trigger.early
  have hhi : pulse.trigger.beforeFire.time < s.time + 9 / 10 := by
    simpa only [pulse.trigger.entry.time_unchanged] using pulse.trigger.deadline
  refine ⟨first,by dsimp [first]; linarith,by dsimp [first]; linarith,
    pulse.sparse_latency_le_rest hb hi p hs hq hg hr ho hno ht,?_⟩
  rw [pulse.emissions]
  congr 1
  dsimp [first]
  ring


theorem sparse_prepared_cell_residual_calendar_of_valid {n θ ε route} (hb : @PhysicalBox n θ ε)
    (i : Fin n) (p : Port) (times : List ℝ) {s u : Snapshot n} (e : Execution θ route s u)
    (hi : UpperRegion s) (hv : RawValid s) (hs : PreparedSection s i)
    (hq : 1 / 10 ≤ s.x i .q)
    (hz : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hcalendar : e.cellDeliveries i = times.map (fun t => ⟨i,p,t⟩))
    (hspace : (s.time :: times).Pairwise (fun t v => t + 7 ≤ v))
    (hquiet : ∀ t ∈ s.time :: times, t + 7 ≤ u.time) :
    ∃ first : ℝ, 3 / 10 < first ∧ first < 9 / 10 ∧
      first ≤ restLatency (Real.exp (s.x i (.z p))) ∧
      e.emissionTimes i = (s.time + first) :: times.map (fun t => t + restLatency (Real.exp (s.x i (.z p)))) := by
  cases times with
  | nil =>
    have hn : ∀ q, NoArrivalAt e i q := (e.cellDeliveries_empty_iff i).mp (by simpa using hcalendar)
    obtain ⟨pulse⟩ := e.sparse_learned_pulse_of_valid hb hi hv i p hs hz hr ho hn (hquiet s.time (by simp))
    obtain ⟨first,hlo,hhi,hle,hem⟩ := pulse.sparse_residual_calendar hb hi p hs hq hz hr ho hn (hquiet s.time (by simp))
    exact ⟨first,hlo,hhi,hle,by simpa only [List.map_nil] using hem⟩
  | cons next tail =>
    have hcal : e.cellDeliveries i = ⟨i,p,next⟩ :: tail.map (fun t => ⟨i,p,t⟩) := by simpa using hcalendar
    obtain ⟨cut⟩ := e.first_cell_delivery i _ _ hcal
    have hdate := cut.date
    have hgap : s.time + 7 ≤ next := (List.pairwise_cons.mp hspace).1 next (by simp)
    obtain ⟨pulse⟩ := cut.span.sparse_learned_pulse_of_valid hb hi hv i p hs hz hr ho
      cut.no_arrivals_before (by rw [hdate.1]; exact hgap)
    obtain ⟨first,hlo,hhi,hle,hem⟩ := pulse.sparse_residual_calendar hb hi p hs hq hz hr ho
      cut.no_arrivals_before (by rw [hdate.1]; exact hgap)
    have hnext := cut.prepared pulse.prepared
    have hx : cut.afterArrival.x i (.z p) = s.x i (.z p) := by
      rw [cut.entry.physical_continuous,pulse.gain_preserved p]
    have hqnext : cut.afterArrival.x i .q = 1 / 10 := by
      rw [cut.entry.physical_continuous,pulse.charge_rest]
    have hznext : 9 / 5 ≤ Real.exp (cut.afterArrival.x i (.z p)) ∧
        Real.exp (cut.afterArrival.x i (.z p)) ≤ 12 / 5 := by rw [hx]; exact hz
    have hrnext : cut.afterArrival.raw i p = some cut.afterArrival.time := cut.raw_after
    have honext : ∀ q, q ≠ p → cut.afterArrival.raw i q = none := by
      intro q hq
      rw [cut.raw_other i q (Or.inr hq)]
      exact pulse.raw_finished q
    have hspaceNext : (cut.afterArrival.time :: tail).Pairwise (fun t v => t + 7 ≤ v) := by
      rw [hdate.2]
      exact (List.pairwise_cons.mp hspace).2
    have hquietNext : ∀ t ∈ cut.afterArrival.time :: tail, t + 7 ≤ u.time := by
      rw [hdate.2]
      intro t ht
      exact hquiet t (List.mem_cons_of_mem _ ht)
    let advanced := cut.span.append (.cons (.jump cut.entry) (.nil _))
    have htail := sparse_prepared_cell_calendar_of_valid hb i p tail cut.rest
      (advanced.upper_region hb hi) (advanced.raw_valid hv) hnext hqnext hznext hrnext honext
      cut.later hspaceNext hquietNext
    rw [hx,hdate.2] at htail
    refine ⟨first,hlo,hhi,hle,?_⟩
    rw [cut.emissions,hem,htail]
    rfl


end KernelR.Hybrid
