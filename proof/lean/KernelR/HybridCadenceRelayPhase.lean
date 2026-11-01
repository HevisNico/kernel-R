import KernelR.HybridCadenceSparsePrefix
import KernelR.HybridCadenceHighTrain
import KernelR.HybridCadenceStrongPulse
import KernelR.HybridCadenceMarkOnly
import KernelR.HybridCadenceMixedPulse
import KernelR.HybridHighGainCalendar
import KernelR.HybridCadenceHighTiming

/-! Actual variable-date receiving relays preserve their own memories and
compose the four transient physical cases with the later high-gain train. -/
namespace KernelR.Hybrid
open Set

theorem Execution.cadence_wide_strong_pulse {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hm : s.main i = .ready)
    (hq : 1 / 10 - 1 / 100000 ≤ s.x i .q ∧ s.x i .q ≤ 3 / 10)
    (hb₀ : 0 ≤ s.x i .b ∧ s.x i .b ≤ 28001 / 100000)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 19 / 5 ≤ u.time ∧ u.time ≤ s.time + 9 / 2) :
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
    have hdu : u.time - b.time ≤ 9 / 2 - 1 - 3 / 10 := by rw [hbtime]; linarith [ht.2,tr.early]
    have hIUpper : slowSpan.accumulatedRecovery i ≤ (28001 / 100000 : ℝ) * (9 / 2 - 1 - 3 / 10) := by
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


theorem CadenceStrongPulse.rest_first_strong_charge {n θ route s u i} {e : @Execution n θ route s u}
    (pulse : CadenceStrongPulse e i) (hb : s.x i .b ≤ 18001 / 100000)
    (hfire : s.time + 13 / 20 < pulse.trigger.afterFire.time)
    (ht : u.time ≤ s.time + 9 / 2) : 37 / 250 ≤ u.x i .q := by
  have he : (74 / 125 : ℝ) ≤ Real.exp (-(523 / 1000 : ℝ)) := by
    have h := Real.exp_bound (x := -(523 / 1000 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith [(abs_sub_le_iff.mp h).2]
  have hd : 0 ≤ u.time - pulse.trigger.afterFire.time - 1 := by
    have h := pulse.slowSpan.time_monotone
    rw [pulse.slow_date] at h
    linarith
  have hu : u.time - pulse.trigger.afterFire.time - 1 ≤ 57 / 20 := by
    linarith [hfire]
  have hI : s.x i .b * (u.time - pulse.trigger.afterFire.time - 1) ≤ 523 / 1000 := by
    have h := (mul_le_mul_of_nonneg_right hb hd).trans
      (mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 18001 / 100000))
    norm_num at h
    linarith
  have hex := Real.exp_le_exp.mpr (neg_le_neg hI)
  rw [pulse.charge_solution,neg_mul]
  linarith

/-- Exact rest supplies the stronger own first-fire bound, allowing the
first jittered dense gap to reach 4.5 while preserving the MARK charge floor. -/
theorem Execution.cadence_rest_first_strong_pulse {n θ ε route s u} (e : @Execution n θ route s u)
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (i : Fin n) (p : Port) (hm : s.main i = .ready) (hq : s.x i .q = 1 / 10)
    (hbRange : 17999 / 100000 ≤ s.x i .b ∧ s.x i .b ≤ 18001 / 100000)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (ha : ∀ q, s.aux i q = .ready ∧ RestBand (s.x i (.m q)))
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q)
    (ht : s.time + 19 / 5 ≤ u.time ∧ u.time ≤ s.time + 9 / 2) :
    ∃ _pulse : CadenceStrongPulse e i, 37 / 250 ≤ u.x i .q := by
  obtain ⟨pulse⟩ := e.cadence_wide_strong_pulse hb hf hv i p hm (by rw [hq]; norm_num)
    ⟨by linarith [hbRange.1],by linarith [hbRange.2]⟩ hz ha hr ho hno ht
  have hfire := pulse.trigger.cadence_rest_firing_bounds hb hf.region p hq hz (ha p) hr ho hno (by linarith [ht.1])
  exact ⟨pulse,pulse.rest_first_strong_charge hbRange.2 hfire.1 ht.2⟩

structure CadenceRelayPhase {n θ route s u i p sparseDates firstStrong markTime secondStrong mixedTime firstHigh highTail}
    {e : @Execution n θ route s u}
    (pre : CadenceSparsePrefix e i p sparseDates firstStrong
      ((markTime :: secondStrong :: mixedTime :: firstHigh :: highTail).map (fun t => ⟨i,p,t⟩))) where
  cutMark : CellDeliveryStep pre.rest i ⟨i,p,markTime⟩
    ((secondStrong :: mixedTime :: firstHigh :: highTail).map (fun t => ⟨i,p,t⟩))
  strongFirst : CadenceStrongPulse cutMark.span i
  cutSecond : CellDeliveryStep cutMark.rest i ⟨i,p,secondStrong⟩
    ((mixedTime :: firstHigh :: highTail).map (fun t => ⟨i,p,t⟩))
  markOnly : CadenceMarkOnlyPulse cutSecond.span i p
  cutMixed : CellDeliveryStep cutSecond.rest i ⟨i,p,mixedTime⟩
    ((firstHigh :: highTail).map (fun t => ⟨i,p,t⟩))
  strongSecond : CadenceStrongPulse cutMixed.span i
  cutHigh : CellDeliveryStep cutMixed.rest i ⟨i,p,firstHigh⟩ (highTail.map (fun t => ⟨i,p,t⟩))
  mixed : CadenceMixedPulse cutHigh.span i p
  high : CadenceHighTrain cutHigh.rest i (highTail.length + 1)
  emissions : (e.emissionTimes i).length = sparseDates.length + highTail.length + 3
  error_target : e.ledger.error i p = 3 / 5
  error_other : ∀ q, q ≠ p → e.ledger.error i q = 0
  mark_target : e.ledger.mark i p = 1 / 5
  mark_other : ∀ q, q ≠ p → e.ledger.mark i q = 0
  gain_target : u.x i (.z p) = s.x i (.z p) + 3 / 5
  gain_other : ∀ q, q ≠ p → u.x i (.z q) = s.x i (.z q)
  recovery_gain : u.x i .b = s.x i .b + 1 / 5
  ready : u.main i = .ready
  charge_rest : u.x i .q = 1 / 10
  auxiliary : ∀ q, u.aux i q = .ready ∧ RestBand (u.x i (.m q))
  raw_finished : ∀ q, u.raw i q = none
  physical : PhysicalInvariant θ u
  raw_valid : RawValid u

/-- Only actual incoming calendars and numerical gaps are supplied; all
transient pulse cases, doses and output counts are selected from e. -/
theorem CadenceSparsePrefix.relay_phase
    {n θ ε route s u i p sparseDates firstStrong markTime secondStrong mixedTime firstHigh highTail}
    {e : @Execution n θ route s u}
    (pre : CadenceSparsePrefix e i p sparseDates firstStrong
      ((markTime :: secondStrong :: mixedTime :: firstHigh :: highTail).map (fun t => ⟨i,p,t⟩)))
    (hb : PhysicalBox θ ε) (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hgap1 : firstStrong + 19 / 5 ≤ markTime ∧ markTime ≤ firstStrong + 9 / 2)
    (hgap2 : markTime + 19 / 5 ≤ secondStrong ∧ secondStrong ≤ markTime + 21 / 5)
    (hgap3 : secondStrong + 19 / 5 ≤ mixedTime ∧ mixedTime ≤ secondStrong + 21 / 5)
    (hgap4 : mixedTime + 19 / 5 ≤ firstHigh ∧ firstHigh ≤ mixedTime + 21 / 5)
    (hhighSpace : (firstHigh :: highTail).Pairwise (fun t v => t + 19 / 5 ≤ v))
    (hhighQuiet : ∀ t ∈ firstHigh :: highTail, t + 19 / 5 ≤ u.time) :
    Nonempty (CadenceRelayPhase pre) := by
  have hf0 := pre.head.physical_invariant hb hf
  have hv0 := pre.head.raw_valid hv
  have hz0 : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ pre.entry.x i (.z p) ∧
      pre.entry.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [pre.gain_preserved p]
    exact hz
  have hb0 := pre.prepared.recovery
  have hcal1 : pre.rest.cellDeliveries i = ⟨i,p,markTime⟩ ::
      (secondStrong :: mixedTime :: firstHigh :: highTail).map (fun t => ⟨i,p,t⟩) := by
    simpa only [List.map_cons] using pre.calendar
  obtain ⟨cut1⟩ := pre.rest.first_cell_delivery i _ _ hcal1
  obtain ⟨strong1,hcharge1⟩ := cut1.span.cadence_rest_first_strong_pulse hb hf0 hv0 i p
    pre.prepared.ready pre.charge_rest hb0 hz0 pre.prepared.auxiliary
    pre.raw_active pre.raw_other cut1.no_arrivals_before (by
      rw [pre.date,cut1.date.1]
      exact hgap1)
  let advanced1 := cut1.span.append (.cons (.jump cut1.entry) (.nil _))
  have hf1 := advanced1.physical_invariant hb hf0
  have hv1 := advanced1.raw_valid hv0
  have hs1 : cut1.afterArrival.main i = .slow := by
    rw [cut1.modes_after.1]
    exact strong1.slowSpan.allStates_final strong1.slow_states
  have hq1 : 37 / 250 ≤ cut1.afterArrival.x i .q ∧ cut1.afterArrival.x i .q ≤ 1 / 4 := by
    rw [cut1.entry.physical_continuous]
    exact ⟨hcharge1,strong1.charge.2⟩
  have hb1 : 17999 / 100000 ≤ cut1.afterArrival.x i .b ∧ cut1.afterArrival.x i .b ≤ 18001 / 100000 := by
    rw [cut1.entry.physical_continuous,strong1.recovery_preserved]
    exact hb0
  have hz1 : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ cut1.afterArrival.x i (.z p) ∧
      cut1.afterArrival.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [cut1.entry.physical_continuous,strong1.gain_preserved]
    exact hz0
  have ha1 : ∀ q, cut1.afterArrival.aux i q = .ready ∧ RestBand (cut1.afterArrival.x i (.m q)) := by
    intro q
    rw [cut1.modes_after.2,cut1.entry.physical_continuous]
    exact strong1.auxiliary q
  have hr1 : cut1.afterArrival.raw i p = some cut1.afterArrival.time := cut1.raw_after
  have ho1 : ∀ q, q ≠ p → cut1.afterArrival.raw i q = none := by
    intro q hq
    rw [cut1.raw_other i q (Or.inr hq)]
    exact strong1.raw_finished q
  have hcal2 : cut1.rest.cellDeliveries i = ⟨i,p,secondStrong⟩ ::
      (mixedTime :: firstHigh :: highTail).map (fun t => ⟨i,p,t⟩) := by
    simpa only [List.map_cons] using cut1.later
  obtain ⟨cut2⟩ := cut1.rest.first_cell_delivery i _ _ hcal2
  obtain ⟨markOnly⟩ := cut2.span.cadence_mark_only_pulse hb hf1 hv1 i p hs1 hq1 hb1 ha1 hr1 ho1
    cut2.no_arrivals_before (by rw [cut1.date.2,cut2.date.1]; exact hgap2.1)
  let advanced2 := cut2.span.append (.cons (.jump cut2.entry) (.nil _))
  have hf2 := advanced2.physical_invariant hb hf1
  have hv2 := advanced2.raw_valid hv1
  have hs2 : cut2.afterArrival.main i = .ready := by rw [cut2.modes_after.1]; exact markOnly.ready
  have hq2 : cut2.afterArrival.x i .q = 1 / 10 := by
    rw [cut2.entry.physical_continuous,markOnly.charge_rest]
  have hb2 : 27999 / 100000 ≤ cut2.afterArrival.x i .b ∧ cut2.afterArrival.x i .b ≤ 28001 / 100000 := by
    rw [cut2.entry.physical_continuous,markOnly.recovery_gain]
    constructor <;> linarith [hb1.1,hb1.2]
  have hz2 : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ cut2.afterArrival.x i (.z p) ∧
      cut2.afterArrival.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [cut2.entry.physical_continuous,markOnly.gain_preserved]
    exact hz1
  have ha2 : ∀ q, cut2.afterArrival.aux i q = .ready ∧ RestBand (cut2.afterArrival.x i (.m q)) := by
    intro q
    rw [cut2.modes_after.2,cut2.entry.physical_continuous]
    exact markOnly.auxiliary q
  have hr2 : cut2.afterArrival.raw i p = some cut2.afterArrival.time := cut2.raw_after
  have ho2 : ∀ q, q ≠ p → cut2.afterArrival.raw i q = none := by
    intro q hq
    rw [cut2.raw_other i q (Or.inr hq)]
    exact markOnly.raw_finished q
  have hcal3 : cut2.rest.cellDeliveries i = ⟨i,p,mixedTime⟩ ::
      (firstHigh :: highTail).map (fun t => ⟨i,p,t⟩) := by
    simpa only [List.map_cons] using cut2.later
  obtain ⟨cut3⟩ := cut2.rest.first_cell_delivery i _ _ hcal3
  obtain ⟨strong2,hcharge2⟩ := cut3.span.cadence_second_strong_pulse hb hf2 hv2 i p hs2 hq2 hb2 hz2 ha2 hr2 ho2
    cut3.no_arrivals_before (by rw [cut2.date.2,cut3.date.1]; exact hgap3)
  let advanced3 := cut3.span.append (.cons (.jump cut3.entry) (.nil _))
  have hf3 := advanced3.physical_invariant hb hf2
  have hv3 := advanced3.raw_valid hv2
  have hs3 : cut3.afterArrival.main i = .slow := by
    rw [cut3.modes_after.1]
    exact strong2.slowSpan.allStates_final strong2.slow_states
  have hq3 : 61 / 500 ≤ cut3.afterArrival.x i .q ∧ cut3.afterArrival.x i .q ≤ 7 / 50 := by
    rw [cut3.entry.physical_continuous]
    exact hcharge2
  have hb3 : 27999 / 100000 ≤ cut3.afterArrival.x i .b ∧ cut3.afterArrival.x i .b ≤ 28001 / 100000 := by
    rw [cut3.entry.physical_continuous,strong2.recovery_preserved]
    exact hb2
  have hz3 : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ cut3.afterArrival.x i (.z p) ∧
      cut3.afterArrival.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [cut3.entry.physical_continuous,strong2.gain_preserved]
    exact hz2
  have ha3 : ∀ q, cut3.afterArrival.aux i q = .ready ∧ RestBand (cut3.afterArrival.x i (.m q)) := by
    intro q
    rw [cut3.modes_after.2,cut3.entry.physical_continuous]
    exact strong2.auxiliary q
  have hr3 : cut3.afterArrival.raw i p = some cut3.afterArrival.time := cut3.raw_after
  have ho3 : ∀ q, q ≠ p → cut3.afterArrival.raw i q = none := by
    intro q hq
    rw [cut3.raw_other i q (Or.inr hq)]
    exact strong2.raw_finished q
  have hcal4 : cut3.rest.cellDeliveries i = ⟨i,p,firstHigh⟩ ::
      (highTail).map (fun t => ⟨i,p,t⟩) := by
    simpa only [List.map_cons] using cut3.later
  obtain ⟨cut4⟩ := cut3.rest.first_cell_delivery i _ _ hcal4
  obtain ⟨mixed⟩ := cut4.span.cadence_mixed_pulse hb hf3 hv3 i p hs3 hq3 hb3 ha3 hz3 hr3 ho3
    cut4.no_arrivals_before (by rw [cut3.date.2,cut4.date.1]; exact hgap4.1)
  let advanced4 := cut4.span.append (.cons (.jump cut4.entry) (.nil _))
  have hf4 := advanced4.physical_invariant hb hf3
  have hv4 := advanced4.raw_valid hv3
  have hs4 : cut4.afterArrival.main i = .ready := by rw [cut4.modes_after.1]; exact mixed.ready
  have hq4 : 1 / 10 - 1 / 100000 ≤ cut4.afterArrival.x i .q ∧ cut4.afterArrival.x i .q ≤ 1 / 2 := by
    rw [cut4.entry.physical_continuous]
    constructor <;> linarith [mixed.charge.1,mixed.charge.2]
  have hb4 : 37999 / 100000 ≤ cut4.afterArrival.x i .b := by
    rw [cut4.entry.physical_continuous,mixed.recovery_gain]
    linarith [hb3.1]
  have hz4 : Real.log (3 / 10) + 12 / 5 - 1 / 100000 ≤ cut4.afterArrival.x i (.z p) ∧
      cut4.afterArrival.x i (.z p) ≤ Real.log (3 / 10) + 12 / 5 + 1 / 100000 := by
    rw [cut4.entry.physical_continuous,mixed.gain_target]
    constructor <;> linarith [hz3.1,hz3.2]
  have hGain4 : 16 / 5 ≤ Real.exp (cut4.afterArrival.x i (.z p)) ∧
      Real.exp (cut4.afterArrival.x i (.z p)) ≤ 7 / 2 := by
    exact ⟨cadence_four_dose_gain_lower hz4.1,
      (cadence_high_gain_bounds (by linarith [hz4.1]) hz4.2).2⟩
  have ha4 : ∀ q, cut4.afterArrival.aux i q = .ready ∧ RestBand (cut4.afterArrival.x i (.m q)) := by
    intro q
    rw [cut4.modes_after.2,cut4.entry.physical_continuous]
    exact mixed.auxiliary q
  have hr4 : cut4.afterArrival.raw i p = some cut4.afterArrival.time := cut4.raw_after
  have ho4 : ∀ q, q ≠ p → cut4.afterArrival.raw i q = none := by
    intro q hq
    rw [cut4.raw_other i q (Or.inr hq)]
    exact mixed.raw_finished q
  have hcalHigh : cut4.rest.cellDeliveries i = highTail.map (fun t => ⟨i,p,t⟩) := cut4.later
  have hspace : (cut4.afterArrival.time :: highTail).Pairwise (fun t v => t + 19 / 5 ≤ v) := by
    rw [cut4.date.2]
    exact hhighSpace
  have hquiet : ∀ t ∈ cut4.afterArrival.time :: highTail, t + 19 / 5 ≤ u.time := by
    rw [cut4.date.2]
    exact hhighQuiet
  obtain ⟨high⟩ := cadence_high_train_of_valid hb i p highTail cut4.rest hf4 hv4 hs4 hq4
    hGain4 hb4 ha4 hr4 ho4 hcalHigh hspace hquiet
  have hgain : u.x i (.z p) = s.x i (.z p) + 3 / 5 := by
    rw [high.gain_preserved,cut4.entry.physical_continuous,mixed.gain_target,
      cut3.entry.physical_continuous,strong2.gain_preserved,
      cut2.entry.physical_continuous,markOnly.gain_preserved,
      cut1.entry.physical_continuous,strong1.gain_preserved,pre.gain_preserved p]
  have hother : ∀ q, q ≠ p → u.x i (.z q) = s.x i (.z q) := by
    intro q hq
    rw [high.gain_preserved,cut4.entry.physical_continuous,mixed.gain_other q hq,
      cut3.entry.physical_continuous,strong2.gain_preserved,
      cut2.entry.physical_continuous,markOnly.gain_preserved,
      cut1.entry.physical_continuous,strong1.gain_preserved,pre.gain_preserved q]
  have hbrecovery : u.x i .b = s.x i .b + 1 / 5 := by
    rw [high.recovery_preserved,cut4.entry.physical_continuous,mixed.recovery_gain,
      cut3.entry.physical_continuous,strong2.recovery_preserved,
      cut2.entry.physical_continuous,markOnly.recovery_gain,
      cut1.entry.physical_continuous,strong1.recovery_preserved,pre.recovery_preserved]
    ring
  have hmark (q : Port) : e.ledger.mark i q =
      cut2.span.ledger.mark i q + cut4.span.ledger.mark i q := by
    have hm1 := pre.rest.mark_split cut1.span cut1.entry cut1.rest cut1.reconstruct i q
    have hm2 := cut1.rest.mark_split cut2.span cut2.entry cut2.rest cut2.reconstruct i q
    have hm3 := cut2.rest.mark_split cut3.span cut3.entry cut3.rest cut3.reconstruct i q
    have hm4 := cut3.rest.mark_split cut4.span cut4.entry cut4.rest cut4.reconstruct i q
    have hemark := congrArg (fun actual => actual.ledger.mark i q) pre.reconstruct
    rw [Execution.mark_append] at hemark
    rw [hemark,pre.mark_zero,hm1,hm2,hm3,hm4,
      strong1.mark_zero,strong2.mark_zero,high.mark_zero]
    ring
  refine ⟨{
    cutMark := cut1
    strongFirst := strong1
    cutSecond := cut2
    markOnly := markOnly
    cutMixed := cut3
    strongSecond := strong2
    cutHigh := cut4
    mixed := mixed
    high := high
    emissions := ?_
    error_target := ?_
    error_other := ?_
    mark_target := ?_
    mark_other := ?_
    gain_target := hgain
    gain_other := hother
    recovery_gain := hbrecovery
    ready := high.ready
    charge_rest := high.charge_rest
    auxiliary := high.auxiliary
    raw_finished := high.raw_finished
    physical := cut4.rest.physical_invariant hb hf4
    raw_valid := cut4.rest.raw_valid hv4
  }⟩
  · have hemission := congrArg (fun actual => actual.emissionTimes i) pre.reconstruct
    rw [Execution.emissionTimes_append,pre.emissions] at hemission
    rw [hemission,cut1.emissions,cut2.emissions,cut3.emissions,cut4.emissions,
      strong1.emissions,markOnly.emissions,strong2.emissions,mixed.emissions]
    simp only [List.length_append,List.length_cons,List.length_nil,List.length_map]
    have h := high.emissions
    omega
  · have h := e.gain_balance i p
    rw [hgain] at h
    linarith
  · intro q hq
    have h := e.gain_balance i q
    rw [hother q hq] at h
    linarith
  · rw [hmark,markOnly.mark_case.mark_dose,mixed.mark_case.mark_dose]
    norm_num
  · intro q hq
    rw [hmark,markOnly.mark_case.mark_other q hq,mixed.mark_case.mark_other q hq]
    norm_num


theorem MainTrigger.relay_rest_date {n θ route s u i p}
    {e : @Execution n θ route s u} (tr : MainTrigger e i) (cycle : SensorCycle e i p)
    (hq : s.x i .q = 1 / 10)
    (hg : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) :
    tr.beforeFire.time = s.time + restLatency (Real.exp (s.x i (.z p))) := by
  have hroot := tr.firing_equation cycle hr ho hno
  rw [hq] at hroot
  have hshift : readyPulse (1 / 10) (Real.exp (s.x i (.z p))) 0
      (tr.beforeFire.time - s.time) = 1 := by
    simpa only [readyPulse,sub_zero] using hroot
  have hlo : s.time + 3 / 10 < tr.beforeFire.time := by
    simpa only [tr.entry.time_unchanged] using tr.early
  have hhi : tr.beforeFire.time < s.time + 9 / 10 := by
    simpa only [tr.entry.time_unchanged] using tr.deadline
  have heq := restLatency_unique hg ⟨by linarith,by linarith⟩ hshift
  linarith

structure CadenceRelayCalendar
    {n θ route s u i p sparseDates firstStrong markTime secondStrong mixedTime firstHigh highTail}
    {e : @Execution n θ route s u}
    {pre : CadenceSparsePrefix e i p sparseDates firstStrong
      ((markTime :: secondStrong :: mixedTime :: firstHigh :: highTail).map (fun t => ⟨i,p,t⟩))}
    (phase : CadenceRelayPhase pre) where
  firstResidual : ℝ
  firstResidual_lower : 1 / 10 < firstResidual
  firstResidual_upper : firstResidual < 3 / 10
  firstResidual_le_rest : firstResidual ≤ highRestLatency (Real.exp (s.x i (.z p) + 3 / 5))
  restLow_lower : 13 / 20 < restLatency (Real.exp (s.x i (.z p)))
  restLow_upper : restLatency (Real.exp (s.x i (.z p))) < 33 / 50
  restHigh_lower : 1 / 10 < highRestLatency (Real.exp (s.x i (.z p) + 3 / 5))
  restHigh_upper : highRestLatency (Real.exp (s.x i (.z p) + 3 / 5)) < 3 / 10
  firstResidual_sharp_lower : 4 / 25 < firstResidual
  firstResidual_sharp_upper : firstResidual < 13 / 50
  restHigh_sharp_upper : highRestLatency (Real.exp (s.x i (.z p) + 3 / 5)) < 13 / 50
  emissions : e.emissionTimes i =
    (sparseDates ++ [firstStrong,secondStrong]).map
      (fun t => t + restLatency (Real.exp (s.x i (.z p)))) ++
      (firstHigh + firstResidual) :: highTail.map
        (fun t => t + highRestLatency (Real.exp (s.x i (.z p) + 3 / 5)))

/-- Exact rest is supplied by the sparse prefix and MARK-only return. The
first high response instead retains the mixed pulse's actual residual. -/
theorem CadenceRelayPhase.output_calendar
    {n θ ε route s u i p sparseDates firstStrong markTime secondStrong mixedTime firstHigh highTail}
    {e : @Execution n θ route s u}
    {pre : CadenceSparsePrefix e i p sparseDates firstStrong
      ((markTime :: secondStrong :: mixedTime :: firstHigh :: highTail).map (fun t => ⟨i,p,t⟩))}
    (phase : CadenceRelayPhase pre) (hb : PhysicalBox θ ε)
    (hf : PhysicalInvariant θ s) (hv : RawValid s)
    (hz : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ s.x i (.z p) ∧
      s.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000)
    (hgap1 : firstStrong + 19 / 5 ≤ markTime)
    (hgap3 : secondStrong + 19 / 5 ≤ mixedTime)
    (hhighSpace : (firstHigh :: highTail).Pairwise (fun t v => t + 19 / 5 ≤ v))
    (hhighQuiet : ∀ t ∈ firstHigh :: highTail, t + 19 / 5 ≤ u.time) :
    Nonempty (CadenceRelayCalendar phase) := by
  let cut1 := phase.cutMark
  let cut2 := phase.cutSecond
  let cut3 := phase.cutMixed
  let cut4 := phase.cutHigh
  let advanced1 := cut1.span.append (.cons (.jump cut1.entry) (.nil _))
  let advanced2 := cut2.span.append (.cons (.jump cut2.entry) (.nil _))
  let advanced3 := cut3.span.append (.cons (.jump cut3.entry) (.nil _))
  let advanced4 := cut4.span.append (.cons (.jump cut4.entry) (.nil _))
  have hf0 := pre.head.physical_invariant hb hf
  have hv0 := pre.head.raw_valid hv
  have hf1 := advanced1.physical_invariant hb hf0
  have hv1 := advanced1.raw_valid hv0
  have hf2 := advanced2.physical_invariant hb hf1
  have hv2 := advanced2.raw_valid hv1
  have hf3 := advanced3.physical_invariant hb hf2
  have hv3 := advanced3.raw_valid hv2
  have hf4 := advanced4.physical_invariant hb hf3
  have hv4 := advanced4.raw_valid hv3
  have hG0 : 9 / 5 ≤ Real.exp (pre.entry.x i (.z p)) ∧ Real.exp (pre.entry.x i (.z p)) ≤ 12 / 5 := by
    rw [pre.gain_preserved p]
    have h := learned_gain_bounds hz.1 hz.2
    exact ⟨h.1,by linarith [h.2]⟩
  obtain ⟨cycle0⟩ := cut1.span.sensor_cycle hb hf0.region i p
    (pre.prepared.auxiliary p).1 pre.raw_active (pre.prepared.auxiliary p).2 (by
      rw [pre.date,cut1.date.1]
      linarith)
  have hFirstDate := phase.strongFirst.trigger.relay_rest_date cycle0 pre.charge_rest hG0
    pre.raw_active pre.raw_other cut1.no_arrivals_before
  have hFirstDate' : phase.strongFirst.trigger.beforeFire.time =
      firstStrong + restLatency (Real.exp (s.x i (.z p))) := by
    simpa only [pre.gain_preserved p,pre.date] using hFirstDate
  have hFirstEmission : cut1.span.emissionTimes i = [firstStrong + restLatency (Real.exp (s.x i (.z p)))] := by
    rw [phase.strongFirst.emissions,hFirstDate']
  have hq2 : cut2.afterArrival.x i .q = 1 / 10 := by
    rw [cut2.entry.physical_continuous,phase.markOnly.charge_rest]
  have ha2 : ∀ q, cut2.afterArrival.aux i q = .ready ∧ RestBand (cut2.afterArrival.x i (.m q)) := by
    intro q
    rw [cut2.modes_after.2,cut2.entry.physical_continuous]
    exact phase.markOnly.auxiliary q
  have hr2 : cut2.afterArrival.raw i p = some cut2.afterArrival.time := cut2.raw_after
  have ho2 : ∀ q, q ≠ p → cut2.afterArrival.raw i q = none := by
    intro q hq
    rw [cut2.raw_other i q (Or.inr hq)]
    exact phase.markOnly.raw_finished q
  have hgain2 : cut2.afterArrival.x i (.z p) = s.x i (.z p) := by
    rw [cut2.entry.physical_continuous,phase.markOnly.gain_preserved,
      cut1.entry.physical_continuous,phase.strongFirst.gain_preserved,pre.gain_preserved p]
  have hG2 : 9 / 5 ≤ Real.exp (cut2.afterArrival.x i (.z p)) ∧
      Real.exp (cut2.afterArrival.x i (.z p)) ≤ 12 / 5 := by
    rw [hgain2]
    have h := learned_gain_bounds hz.1 hz.2
    exact ⟨h.1,by linarith [h.2]⟩
  obtain ⟨cycle2⟩ := cut3.span.sensor_cycle hb hf2.region i p (ha2 p).1 hr2 (ha2 p).2 (by
    rw [cut2.date.2,cut3.date.1]
    linarith)
  have hSecondDate := phase.strongSecond.trigger.relay_rest_date cycle2 hq2 hG2 hr2 ho2 cut3.no_arrivals_before
  have hSecondDate' : phase.strongSecond.trigger.beforeFire.time =
      secondStrong + restLatency (Real.exp (s.x i (.z p))) := by
    calc
      phase.strongSecond.trigger.beforeFire.time = cut2.afterArrival.time +
        restLatency (Real.exp (cut2.afterArrival.x i (.z p))) := hSecondDate
      _ = _ := by rw [hgain2,cut2.date.2]
  have hSecondEmission : cut3.span.emissionTimes i = [secondStrong + restLatency (Real.exp (s.x i (.z p)))] := by
    rw [phase.strongSecond.emissions,hSecondDate']
  have hs4 : cut4.afterArrival.main i = .ready := by
    rw [cut4.modes_after.1]
    exact phase.mixed.ready
  have hq4 : 1 / 10 ≤ cut4.afterArrival.x i .q ∧ cut4.afterArrival.x i .q ≤ 8 / 25 := by
    rw [cut4.entry.physical_continuous]
    exact ⟨phase.mixed.charge.1,phase.mixed.charge_cadence⟩
  have hgain4 : cut4.afterArrival.x i (.z p) = s.x i (.z p) + 3 / 5 :=
    (phase.high.gain_preserved p).symm.trans phase.gain_target
  have hG4 : 16 / 5 ≤ Real.exp (cut4.afterArrival.x i (.z p)) ∧
      Real.exp (cut4.afterArrival.x i (.z p)) ≤ 7 / 2 := by
    rw [hgain4]
    exact ⟨cadence_four_dose_gain_lower (by linarith [hz.1]),
      (cadence_high_gain_bounds (by linarith [hz.1]) (by linarith [hz.2])).2⟩
  have hb4 : 37999 / 100000 ≤ cut4.afterArrival.x i .b := by
    rw [cut4.entry.physical_continuous,phase.mixed.recovery_gain,
      cut3.entry.physical_continuous,phase.strongSecond.recovery_preserved,
      cut2.entry.physical_continuous,phase.markOnly.recovery_gain,
      cut1.entry.physical_continuous,phase.strongFirst.recovery_preserved]
    linarith [pre.prepared.recovery.1]
  have ha4 : ∀ q, cut4.afterArrival.aux i q = .ready ∧ RestBand (cut4.afterArrival.x i (.m q)) := by
    intro q
    rw [cut4.modes_after.2,cut4.entry.physical_continuous]
    exact phase.mixed.auxiliary q
  have hr4 : cut4.afterArrival.raw i p = some cut4.afterArrival.time := cut4.raw_after
  have ho4 : ∀ q, q ≠ p → cut4.afterArrival.raw i q = none := by
    intro q hq
    rw [cut4.raw_other i q (Or.inr hq)]
    exact phase.mixed.raw_finished q
  have hcalHigh : cut4.rest.cellDeliveries i = highTail.map (fun t => ⟨i,p,t⟩) := cut4.later
  have hspace : (cut4.afterArrival.time :: highTail).Pairwise (fun t v => t + 19 / 5 ≤ v) := by
    rw [cut4.date.2]
    exact hhighSpace
  have hquiet : ∀ t ∈ cut4.afterArrival.time :: highTail, t + 19 / 5 ≤ u.time := by
    rw [cut4.date.2]
    exact hhighQuiet
  obtain ⟨firstResidual,hHighLower,hHighUpper,hHighLe,hHighEmission⟩ :=
    cadence_high_residual_calendar_sharp_of_valid hb i p highTail cut4.rest hf4 hv4 hs4 hq4 hG4 hb4
      ha4 hr4 ho4 hcalHigh hspace hquiet
  have hHighLe' : firstResidual ≤ highRestLatency (Real.exp (s.x i (.z p) + 3 / 5)) := by
    simpa only [hgain4] using hHighLe
  have hHighEmission' : cut4.rest.emissionTimes i = (firstHigh + firstResidual) ::
      highTail.map (fun t => t + highRestLatency (Real.exp (s.x i (.z p) + 3 / 5))) := by
    simpa only [hgain4,cut4.date.2] using hHighEmission
  have hrestLow := restLatency_three_doses_bounds hz.1 hz.2
  have hrestHigh := highRestLatency_spec (G := Real.exp (s.x i (.z p) + 3 / 5)) (by
    simpa only [hgain4] using hG4)
  refine ⟨{
    firstResidual := firstResidual
    firstResidual_lower := by linarith
    firstResidual_upper := by linarith
    firstResidual_le_rest := hHighLe'
    restLow_lower := hrestLow.1
    restLow_upper := hrestLow.2
    restHigh_lower := hrestHigh.1
    restHigh_upper := hrestHigh.2.1
    firstResidual_sharp_lower := hHighLower
    firstResidual_sharp_upper := hHighUpper
    restHigh_sharp_upper := highRestLatency_lt_twenty_six (by simpa only [hgain4] using hG4)
    emissions := ?_
  }⟩
  have hemission := congrArg (fun actual => actual.emissionTimes i) pre.reconstruct
  rw [Execution.emissionTimes_append,pre.emissions] at hemission
  rw [hemission,cut1.emissions,cut2.emissions,cut3.emissions,cut4.emissions,
    hFirstEmission,phase.markOnly.emissions,hSecondEmission,phase.mixed.emissions,hHighEmission']
  simp only [List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_assoc]

end KernelR.Hybrid
