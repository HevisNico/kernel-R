import KernelR.HybridCadencePrelude
import KernelR.HybridCadenceHighTrain
import KernelR.HybridCadenceStrongPulse
import KernelR.HybridCadenceMarkOnly
import KernelR.HybridCadenceMixedPulse
import KernelR.HybridHighGainCalendar
import KernelR.HybridCadenceHighTiming

namespace KernelR.Hybrid

structure CadenceCPhase {θ route s u} {e : @Execution 3 θ route s u}
    (pre : CadencePrelude e) where
  cut656 : CellDeliveryStep pre.rest 2 ⟨2,0,656⟩ (sourceTrain 2 0 660 4 20)
  strong652 : CadenceStrongPulse cut656.span 2
  cut660 : CellDeliveryStep cut656.rest 2 ⟨2,0,660⟩ (sourceTrain 2 0 664 4 19)
  mark656 : CadenceMarkOnlyPulse cut660.span 2 0
  cut664 : CellDeliveryStep cut660.rest 2 ⟨2,0,664⟩ (sourceTrain 2 0 668 4 18)
  strong660 : CadenceStrongPulse cut664.span 2
  cut668 : CellDeliveryStep cut664.rest 2 ⟨2,0,668⟩ (sourceTrain 2 0 672 4 17)
  mixed664 : CadenceMixedPulse cut668.span 2 0
  high668 : CadenceHighTrain cut668.rest 2 18
  emissions : (e.emissionTimes 2).length = 20
  error_target : e.ledger.error 2 0 = 12 / 5
  error_other : ∀ q, q ≠ 0 → e.ledger.error 2 q = 0
  mark_target : e.ledger.mark 2 0 = 1 / 5
  mark_other : ∀ q, q ≠ 0 → e.ledger.mark 2 q = 0
  gain_target : u.x 2 (.z 0) = s.x 2 (.z 0) + 12 / 5
  gain_other : ∀ q, q ≠ 0 → u.x 2 (.z q) = s.x 2 (.z q)
  recovery_gain : u.x 2 .b = s.x 2 .b + 1 / 5
  ready : u.main 2 = .ready
  charge_rest : u.x 2 .q = 1 / 10
  auxiliary : ∀ q, u.aux 2 q = .ready ∧ RestBand (u.x 2 (.m q))
  raw_finished : ∀ q, u.raw 2 q = none
  physical : PhysicalInvariant θ u
  raw_valid : RawValid u

/-- The twenty-one remaining C deliveries select all five physical pieces.
Their source calendar comes from the preserved initial queue in the prelude. -/
theorem CadencePrelude.c_phase {θ ε route s u} {e : @Execution 3 θ route s u}
    (pre : CadencePrelude e) (hb : PhysicalBox θ ε)
    (hz : Real.log (3 / 10) - 1 / 100000 ≤ s.x 2 (.z 0) ∧
      s.x 2 (.z 0) ≤ Real.log (3 / 10) + 1 / 100000)
    (hbRange : 17999 / 100000 ≤ s.x 2 .b ∧ s.x 2 .b ≤ 18001 / 100000)
    (hu : u.time = 7899 / 10) : Nonempty (CadenceCPhase pre) := by
  have hz0 : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ pre.entry.x 2 (.z 0) ∧
      pre.entry.x 2 (.z 0) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [pre.c_gain_target]
    constructor <;> linarith [hz.1,hz.2]
  have hb0 : 17999 / 100000 ≤ pre.entry.x 2 .b ∧ pre.entry.x 2 .b ≤ 18001 / 100000 := by
    rw [pre.c_recovery]
    exact hbRange
  have hcal1 : pre.rest.cellDeliveries 2 = ⟨2,0,656⟩ :: sourceTrain 2 0 660 4 20 := by
    rw [pre.calendar,sourceTrain_succ]
    norm_num
  obtain ⟨cut1⟩ := pre.rest.first_cell_delivery 2 _ _ hcal1
  obtain ⟨strong1,hcharge1⟩ := cut1.span.cadence_first_strong_pulse hb pre.physical pre.raw_valid 2 0
    pre.c_coordinates.ready pre.c_coordinates.charge hb0 hz0 pre.c_coordinates.auxiliary
    pre.c_raw_active pre.c_raw_other cut1.no_arrivals_before (by
      rw [pre.date,cut1.date.1]
      norm_num)
  let advanced1 := cut1.span.append (.cons (.jump cut1.entry) (.nil _))
  have hf1 := advanced1.physical_invariant hb pre.physical
  have hv1 := advanced1.raw_valid pre.raw_valid
  have hs1 : cut1.afterArrival.main 2 = .slow := by
    rw [cut1.modes_after.1]
    exact strong1.slowSpan.allStates_final strong1.slow_states
  have hq1 : 37 / 250 ≤ cut1.afterArrival.x 2 .q ∧ cut1.afterArrival.x 2 .q ≤ 1 / 4 := by
    rw [cut1.entry.physical_continuous]
    exact ⟨hcharge1,strong1.charge.2⟩
  have hb1 : 17999 / 100000 ≤ cut1.afterArrival.x 2 .b ∧ cut1.afterArrival.x 2 .b ≤ 18001 / 100000 := by
    rw [cut1.entry.physical_continuous,strong1.recovery_preserved]
    exact hb0
  have hz1 : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ cut1.afterArrival.x 2 (.z 0) ∧
      cut1.afterArrival.x 2 (.z 0) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [cut1.entry.physical_continuous,strong1.gain_preserved]
    exact hz0
  have ha1 : ∀ q, cut1.afterArrival.aux 2 q = .ready ∧ RestBand (cut1.afterArrival.x 2 (.m q)) := by
    intro q
    rw [cut1.modes_after.2,cut1.entry.physical_continuous]
    exact strong1.auxiliary q
  have hr1 : cut1.afterArrival.raw 2 0 = some cut1.afterArrival.time := cut1.raw_after
  have ho1 : ∀ q, q ≠ 0 → cut1.afterArrival.raw 2 q = none := by
    intro q hq
    rw [cut1.raw_other 2 q (Or.inr hq)]
    exact strong1.raw_finished q
  have hcal2 : cut1.rest.cellDeliveries 2 = ⟨2,0,660⟩ :: sourceTrain 2 0 664 4 19 := by
    rw [cut1.later,sourceTrain_succ]
    norm_num
  obtain ⟨cut2⟩ := cut1.rest.first_cell_delivery 2 _ _ hcal2
  obtain ⟨markOnly⟩ := cut2.span.cadence_mark_only_pulse hb hf1 hv1 2 0 hs1 hq1 hb1 ha1 hr1 ho1
    cut2.no_arrivals_before (by rw [cut1.date.2,cut2.date.1]; norm_num)
  let advanced2 := cut2.span.append (.cons (.jump cut2.entry) (.nil _))
  have hf2 := advanced2.physical_invariant hb hf1
  have hv2 := advanced2.raw_valid hv1
  have hs2 : cut2.afterArrival.main 2 = .ready := by rw [cut2.modes_after.1]; exact markOnly.ready
  have hq2 : cut2.afterArrival.x 2 .q = 1 / 10 := by
    rw [cut2.entry.physical_continuous,markOnly.charge_rest]
  have hb2 : 27999 / 100000 ≤ cut2.afterArrival.x 2 .b ∧ cut2.afterArrival.x 2 .b ≤ 28001 / 100000 := by
    rw [cut2.entry.physical_continuous,markOnly.recovery_gain]
    constructor <;> linarith [hb1.1,hb1.2]
  have hz2 : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ cut2.afterArrival.x 2 (.z 0) ∧
      cut2.afterArrival.x 2 (.z 0) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [cut2.entry.physical_continuous,markOnly.gain_preserved]
    exact hz1
  have ha2 : ∀ q, cut2.afterArrival.aux 2 q = .ready ∧ RestBand (cut2.afterArrival.x 2 (.m q)) := by
    intro q
    rw [cut2.modes_after.2,cut2.entry.physical_continuous]
    exact markOnly.auxiliary q
  have hr2 : cut2.afterArrival.raw 2 0 = some cut2.afterArrival.time := cut2.raw_after
  have ho2 : ∀ q, q ≠ 0 → cut2.afterArrival.raw 2 q = none := by
    intro q hq
    rw [cut2.raw_other 2 q (Or.inr hq)]
    exact markOnly.raw_finished q
  have hcal3 : cut2.rest.cellDeliveries 2 = ⟨2,0,664⟩ :: sourceTrain 2 0 668 4 18 := by
    rw [cut2.later,sourceTrain_succ]
    norm_num
  obtain ⟨cut3⟩ := cut2.rest.first_cell_delivery 2 _ _ hcal3
  obtain ⟨strong2,hcharge2⟩ := cut3.span.cadence_second_strong_pulse hb hf2 hv2 2 0 hs2 hq2 hb2 hz2 ha2 hr2 ho2
    cut3.no_arrivals_before (by rw [cut2.date.2,cut3.date.1]; norm_num)
  let advanced3 := cut3.span.append (.cons (.jump cut3.entry) (.nil _))
  have hf3 := advanced3.physical_invariant hb hf2
  have hv3 := advanced3.raw_valid hv2
  have hs3 : cut3.afterArrival.main 2 = .slow := by
    rw [cut3.modes_after.1]
    exact strong2.slowSpan.allStates_final strong2.slow_states
  have hq3 : 61 / 500 ≤ cut3.afterArrival.x 2 .q ∧ cut3.afterArrival.x 2 .q ≤ 7 / 50 := by
    rw [cut3.entry.physical_continuous]
    exact hcharge2
  have hb3 : 27999 / 100000 ≤ cut3.afterArrival.x 2 .b ∧ cut3.afterArrival.x 2 .b ≤ 28001 / 100000 := by
    rw [cut3.entry.physical_continuous,strong2.recovery_preserved]
    exact hb2
  have hz3 : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ cut3.afterArrival.x 2 (.z 0) ∧
      cut3.afterArrival.x 2 (.z 0) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [cut3.entry.physical_continuous,strong2.gain_preserved]
    exact hz2
  have ha3 : ∀ q, cut3.afterArrival.aux 2 q = .ready ∧ RestBand (cut3.afterArrival.x 2 (.m q)) := by
    intro q
    rw [cut3.modes_after.2,cut3.entry.physical_continuous]
    exact strong2.auxiliary q
  have hr3 : cut3.afterArrival.raw 2 0 = some cut3.afterArrival.time := cut3.raw_after
  have ho3 : ∀ q, q ≠ 0 → cut3.afterArrival.raw 2 q = none := by
    intro q hq
    rw [cut3.raw_other 2 q (Or.inr hq)]
    exact strong2.raw_finished q
  have hcal4 : cut3.rest.cellDeliveries 2 = ⟨2,0,668⟩ :: sourceTrain 2 0 672 4 17 := by
    rw [cut3.later,sourceTrain_succ]
    norm_num
  obtain ⟨cut4⟩ := cut3.rest.first_cell_delivery 2 _ _ hcal4
  obtain ⟨mixed⟩ := cut4.span.cadence_mixed_pulse hb hf3 hv3 2 0 hs3 hq3 hb3 ha3 hz3 hr3 ho3
    cut4.no_arrivals_before (by rw [cut3.date.2,cut4.date.1]; norm_num)
  let advanced4 := cut4.span.append (.cons (.jump cut4.entry) (.nil _))
  have hf4 := advanced4.physical_invariant hb hf3
  have hv4 := advanced4.raw_valid hv3
  have hs4 : cut4.afterArrival.main 2 = .ready := by rw [cut4.modes_after.1]; exact mixed.ready
  have hq4 : 1 / 10 - 1 / 100000 ≤ cut4.afterArrival.x 2 .q ∧ cut4.afterArrival.x 2 .q ≤ 1 / 2 := by
    rw [cut4.entry.physical_continuous]
    constructor <;> linarith [mixed.charge.1,mixed.charge.2]
  have hb4 : 37999 / 100000 ≤ cut4.afterArrival.x 2 .b := by
    rw [cut4.entry.physical_continuous,mixed.recovery_gain]
    linarith [hb3.1]
  have hz4 : Real.log (3 / 10) + 12 / 5 - 1 / 100000 ≤ cut4.afterArrival.x 2 (.z 0) ∧
      cut4.afterArrival.x 2 (.z 0) ≤ Real.log (3 / 10) + 12 / 5 + 1 / 100000 := by
    rw [cut4.entry.physical_continuous,mixed.gain_target]
    constructor <;> linarith [hz3.1,hz3.2]
  have hGain4 : 16 / 5 ≤ Real.exp (cut4.afterArrival.x 2 (.z 0)) ∧
      Real.exp (cut4.afterArrival.x 2 (.z 0)) ≤ 7 / 2 := by
    exact ⟨cadence_four_dose_gain_lower hz4.1,
      (cadence_high_gain_bounds (by linarith [hz4.1]) hz4.2).2⟩
  have ha4 : ∀ q, cut4.afterArrival.aux 2 q = .ready ∧ RestBand (cut4.afterArrival.x 2 (.m q)) := by
    intro q
    rw [cut4.modes_after.2,cut4.entry.physical_continuous]
    exact mixed.auxiliary q
  have hr4 : cut4.afterArrival.raw 2 0 = some cut4.afterArrival.time := cut4.raw_after
  have ho4 : ∀ q, q ≠ 0 → cut4.afterArrival.raw 2 q = none := by
    intro q hq
    rw [cut4.raw_other 2 q (Or.inr hq)]
    exact mixed.raw_finished q
  let times : List ℝ := List.ofFn (fun k : Fin 17 => (672 : ℝ) + 4 * (k.val : ℝ))
  have hcalHigh : cut4.rest.cellDeliveries 2 = times.map (fun t => ⟨2,0,t⟩) := by
    simpa only [times,sourceTrain,List.map_ofFn,Function.comp_def] using cut4.later
  have htimes : (668 : ℝ) :: times = List.ofFn (fun k : Fin 18 => (668 : ℝ) + 4 * (k.val : ℝ)) := by
    have h := congrArg (List.map Delivery.due) (sourceTrain_succ (2 : Fin 3) 0 668 4 17)
    simpa only [sourceTrain,times,List.map_ofFn,Function.comp_def,List.map_cons,
      show (668 : ℝ) + 4 = 672 by norm_num] using h.symm
  have hspace : (cut4.afterArrival.time :: times).Pairwise (fun t v => t + 19 / 5 ≤ v) := by
    rw [cut4.date.2,htimes]
    apply List.pairwise_ofFn.mpr
    intro k l hkl
    have hk : (k.val : ℝ) + 1 ≤ l.val := by exact_mod_cast (Nat.add_one_le_iff.mpr hkl)
    linarith
  have hquiet : ∀ t ∈ cut4.afterArrival.time :: times, t + 19 / 5 ≤ u.time := by
    intro t hm
    rw [cut4.date.2,htimes] at hm
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hm
    have hk : (k.val : ℝ) ≤ 17 := by exact_mod_cast (show k.val ≤ 17 by omega)
    rw [hu]
    linarith
  obtain ⟨high⟩ := cadence_high_train_of_valid hb (2 : Fin 3) 0 times cut4.rest hf4 hv4 hs4 hq4
    hGain4 hb4 ha4 hr4 ho4 hcalHigh hspace hquiet
  have high' : CadenceHighTrain cut4.rest 2 18 := by simpa only [times,List.length_ofFn] using high
  have hgain : u.x 2 (.z 0) = s.x 2 (.z 0) + 12 / 5 := by
    rw [high'.gain_preserved,cut4.entry.physical_continuous,mixed.gain_target,
      cut3.entry.physical_continuous,strong2.gain_preserved,
      cut2.entry.physical_continuous,markOnly.gain_preserved,
      cut1.entry.physical_continuous,strong1.gain_preserved,pre.c_gain_target]
    ring
  have hother : ∀ q, q ≠ 0 → u.x 2 (.z q) = s.x 2 (.z q) := by
    intro q hq
    rw [high'.gain_preserved,cut4.entry.physical_continuous,mixed.gain_other q hq,
      cut3.entry.physical_continuous,strong2.gain_preserved,
      cut2.entry.physical_continuous,markOnly.gain_preserved,
      cut1.entry.physical_continuous,strong1.gain_preserved,pre.c_gain_other q hq]
  have hbrecovery : u.x 2 .b = s.x 2 .b + 1 / 5 := by
    rw [high'.recovery_preserved,cut4.entry.physical_continuous,mixed.recovery_gain,
      cut3.entry.physical_continuous,strong2.recovery_preserved,
      cut2.entry.physical_continuous,markOnly.recovery_gain,
      cut1.entry.physical_continuous,strong1.recovery_preserved,pre.c_recovery]
    ring
  have hmark (q : Port) : e.ledger.mark 2 q =
      cut2.span.ledger.mark 2 q + cut4.span.ledger.mark 2 q := by
    have hm1 := pre.rest.mark_split cut1.span cut1.entry cut1.rest cut1.reconstruct 2 q
    have hm2 := cut1.rest.mark_split cut2.span cut2.entry cut2.rest cut2.reconstruct 2 q
    have hm3 := cut2.rest.mark_split cut3.span cut3.entry cut3.rest cut3.reconstruct 2 q
    have hm4 := cut3.rest.mark_split cut4.span cut4.entry cut4.rest cut4.reconstruct 2 q
    have hemark := congrArg (fun actual => actual.ledger.mark 2 q) pre.reconstruct
    rw [Execution.mark_append] at hemark
    rw [hemark,pre.c_mark,hm1,hm2,hm3,hm4,
      strong1.mark_zero,strong2.mark_zero,high'.mark_zero]
    ring
  refine ⟨{
    cut656 := cut1
    strong652 := strong1
    cut660 := cut2
    mark656 := markOnly
    cut664 := cut3
    strong660 := strong2
    cut668 := cut4
    mixed664 := mixed
    high668 := high'
    emissions := ?_
    error_target := ?_
    error_other := ?_
    mark_target := ?_
    mark_other := ?_
    gain_target := hgain
    gain_other := hother
    recovery_gain := hbrecovery
    ready := high'.ready
    charge_rest := high'.charge_rest
    auxiliary := high'.auxiliary
    raw_finished := high'.raw_finished
    physical := cut4.rest.physical_invariant hb hf4
    raw_valid := cut4.rest.raw_valid hv4
  }⟩
  · have hemission := congrArg (fun actual => actual.emissionTimes 2) pre.reconstruct
    rw [Execution.emissionTimes_append,pre.c_emissions,List.nil_append] at hemission
    rw [hemission,
      cut1.emissions,cut2.emissions,cut3.emissions,cut4.emissions,
      strong1.emissions,markOnly.emissions,strong2.emissions,mixed.emissions]
    simp only [List.length_append,List.length_cons,List.length_nil]
    have h := high'.emissions
    omega
  · have h := e.gain_balance 2 0
    rw [hgain] at h
    linarith
  · intro q hq
    have h := e.gain_balance 2 q
    rw [hother q hq] at h
    linarith
  · rw [hmark,markOnly.mark_case.mark_dose,mixed.mark_case.mark_dose]
    norm_num
  · intro q hq
    rw [hmark,markOnly.mark_case.mark_other q hq,mixed.mark_case.mark_other q hq]
    norm_num

theorem MainTrigger.cadence_latency_le_rest {n θ route s u i p}
    {e : @Execution n θ route s u} (tr : MainTrigger e i) (cycle : SensorCycle e i p)
    (hq : 1 / 10 ≤ s.x i .q)
    (hg : 9 / 5 ≤ Real.exp (s.x i (.z p)) ∧ Real.exp (s.x i (.z p)) ≤ 12 / 5)
    (hr : s.raw i p = some s.time) (ho : ∀ q, q ≠ p → s.raw i q = none)
    (hno : ∀ q, NoArrivalAt e i q) :
    tr.beforeFire.time - s.time ≤ restLatency (Real.exp (s.x i (.z p))) := by
  have hroot := tr.firing_equation cycle hr ho hno
  have hshift : readyPulse (s.x i .q) (Real.exp (s.x i (.z p))) 0
      (tr.beforeFire.time - s.time) = 1 := by
    simpa only [readyPulse,sub_zero] using hroot
  have hlo : s.time + 3 / 10 < tr.beforeFire.time := by
    simpa only [tr.entry.time_unchanged] using tr.early
  have hhi : tr.beforeFire.time < s.time + 9 / 10 := by
    simpa only [tr.entry.time_unchanged] using tr.deadline
  have href := restLatency_spec hg
  exact first_firing_le_rest_reference hq hg.1 ⟨by linarith,by linarith⟩
    ⟨by linarith [href.1],by linarith [href.2.1]⟩ hshift href.2.2

theorem MainTrigger.cadence_rest_date {n θ route s u i p}
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

structure CadenceCCalendar {θ route s u} {e : @Execution 3 θ route s u}
    {pre : CadencePrelude e} (phase : CadenceCPhase pre) where
  firstLow : ℝ
  firstLow_lower : 3 / 10 < firstLow
  firstLow_upper : firstLow < 9 / 10
  firstLow_le_rest : firstLow ≤ restLatency (Real.exp (s.x 2 (.z 0) + 9 / 5))
  restLow_lower : 13 / 20 < restLatency (Real.exp (s.x 2 (.z 0) + 9 / 5))
  restLow_upper : restLatency (Real.exp (s.x 2 (.z 0) + 9 / 5)) < 33 / 50
  firstHigh : ℝ
  firstHigh_lower : 1 / 10 < firstHigh
  firstHigh_upper : firstHigh < 3 / 10
  firstHigh_le_rest : firstHigh ≤ highRestLatency (Real.exp (s.x 2 (.z 0) + 12 / 5))
  restHigh_lower : 1 / 10 < highRestLatency (Real.exp (s.x 2 (.z 0) + 12 / 5))
  restHigh_upper : highRestLatency (Real.exp (s.x 2 (.z 0) + 12 / 5)) < 3 / 10
  firstHigh_sharp : 4 / 25 < firstHigh
  highRest_sharp : highRestLatency (Real.exp (s.x 2 (.z 0) + 12 / 5)) < 13 / 50
  emissions : e.emissionTimes 2 =
    (652 + firstLow) :: (660 + restLatency (Real.exp (s.x 2 (.z 0) + 9 / 5))) ::
      (668 + firstHigh) :: List.ofFn (fun k : Fin 17 =>
        (672 : ℝ) + 4 * (k.val : ℝ) + highRestLatency (Real.exp (s.x 2 (.z 0) + 12 / 5)))

theorem CadenceCPhase.output_calendar {θ ε route s u} {e : @Execution 3 θ route s u}
    {pre : CadencePrelude e} (phase : CadenceCPhase pre) (hb : PhysicalBox θ ε)
    (hz : Real.log (3 / 10) - 1 / 100000 ≤ s.x 2 (.z 0) ∧
      s.x 2 (.z 0) ≤ Real.log (3 / 10) + 1 / 100000)
    (hbRange : 17999 / 100000 ≤ s.x 2 .b ∧ s.x 2 .b ≤ 18001 / 100000)
    (hu : u.time = 7899 / 10) : Nonempty (CadenceCCalendar phase) := by
  let cut1 := phase.cut656
  let cut2 := phase.cut660
  let cut3 := phase.cut664
  let cut4 := phase.cut668
  let advanced1 := cut1.span.append (.cons (.jump cut1.entry) (.nil _))
  let advanced2 := cut2.span.append (.cons (.jump cut2.entry) (.nil _))
  let advanced3 := cut3.span.append (.cons (.jump cut3.entry) (.nil _))
  let advanced4 := cut4.span.append (.cons (.jump cut4.entry) (.nil _))
  have hf1 := advanced1.physical_invariant hb pre.physical
  have hv1 := advanced1.raw_valid pre.raw_valid
  have hf2 := advanced2.physical_invariant hb hf1
  have hv2 := advanced2.raw_valid hv1
  have hf3 := advanced3.physical_invariant hb hf2
  have hv3 := advanced3.raw_valid hv2
  have hf4 := advanced4.physical_invariant hb hf3
  have hv4 := advanced4.raw_valid hv3
  have hz0 : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ pre.entry.x 2 (.z 0) ∧
      pre.entry.x 2 (.z 0) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [pre.c_gain_target]
    constructor <;> linarith [hz.1,hz.2]
  have hG0 : 9 / 5 ≤ Real.exp (pre.entry.x 2 (.z 0)) ∧ Real.exp (pre.entry.x 2 (.z 0)) ≤ 12 / 5 := by
    have h := cadence_three_dose_gain_bounds hz0
    exact ⟨h.1,by linarith [h.2]⟩
  obtain ⟨cycle0⟩ := cut1.span.sensor_cycle hb pre.physical.region 2 0
    (pre.c_coordinates.auxiliary 0).1 pre.c_raw_active (pre.c_coordinates.auxiliary 0).2 (by
      rw [pre.date,cut1.date.1]; norm_num)
  let firstLow := phase.strong652.trigger.beforeFire.time - pre.entry.time
  have hLowLower : 3 / 10 < firstLow := by
    have h := phase.strong652.trigger.early
    rw [phase.strong652.trigger.entry.time_unchanged] at h
    dsimp [firstLow]
    linarith
  have hLowUpper : firstLow < 9 / 10 := by
    have h := phase.strong652.trigger.deadline
    rw [phase.strong652.trigger.entry.time_unchanged] at h
    dsimp [firstLow]
    linarith
  have hLowLe := phase.strong652.trigger.cadence_latency_le_rest cycle0 pre.c_charge_lower hG0
    pre.c_raw_active pre.c_raw_other cut1.no_arrivals_before
  rw [pre.c_gain_target] at hLowLe
  have hrestLow := restLatency_three_doses_bounds (z := s.x 2 (.z 0) + 9 / 5)
    (by linarith [hz.1]) (by linarith [hz.2])
  have hLowEmission : cut1.span.emissionTimes 2 = [652 + firstLow] := by
    rw [phase.strong652.emissions]
    congr 1
    dsimp [firstLow]
    linarith [pre.date]
  have hq2 : cut2.afterArrival.x 2 .q = 1 / 10 := by
    rw [cut2.entry.physical_continuous,phase.mark656.charge_rest]
  have ha2 : ∀ q, cut2.afterArrival.aux 2 q = .ready ∧ RestBand (cut2.afterArrival.x 2 (.m q)) := by
    intro q
    rw [cut2.modes_after.2,cut2.entry.physical_continuous]
    exact phase.mark656.auxiliary q
  have hr2 : cut2.afterArrival.raw 2 0 = some cut2.afterArrival.time := cut2.raw_after
  have ho2 : ∀ q, q ≠ 0 → cut2.afterArrival.raw 2 q = none := by
    intro q hq
    rw [cut2.raw_other 2 q (Or.inr hq)]
    exact phase.mark656.raw_finished q
  have hgain2 : cut2.afterArrival.x 2 (.z 0) = s.x 2 (.z 0) + 9 / 5 := by
    rw [cut2.entry.physical_continuous,phase.mark656.gain_preserved,
      cut1.entry.physical_continuous,phase.strong652.gain_preserved,pre.c_gain_target]
  have hG2 : 9 / 5 ≤ Real.exp (cut2.afterArrival.x 2 (.z 0)) ∧
      Real.exp (cut2.afterArrival.x 2 (.z 0)) ≤ 12 / 5 := by
    rw [hgain2]
    have hh := learned_gain_bounds (z := s.x 2 (.z 0) + 9 / 5)
      (by linarith [hz.1]) (by linarith [hz.2])
    exact ⟨hh.1,by linarith [hh.2]⟩
  obtain ⟨cycle2⟩ := cut3.span.sensor_cycle hb hf2.region 2 0 (ha2 0).1 hr2 (ha2 0).2 (by
    rw [cut2.date.2,cut3.date.1]; norm_num)
  have hRestDate := phase.strong660.trigger.cadence_rest_date cycle2 hq2 hG2 hr2 ho2 cut3.no_arrivals_before
  rw [hgain2,cut2.date.2] at hRestDate
  have hRestEmission : cut3.span.emissionTimes 2 = [660 + restLatency (Real.exp (s.x 2 (.z 0) + 9 / 5))] := by
    rw [phase.strong660.emissions,hRestDate]
  have hs4 : cut4.afterArrival.main 2 = .ready := by
    rw [cut4.modes_after.1]
    exact phase.mixed664.ready
  have hq4 : 1 / 10 ≤ cut4.afterArrival.x 2 .q ∧ cut4.afterArrival.x 2 .q ≤ 8 / 25 := by
    rw [cut4.entry.physical_continuous]
    exact ⟨phase.mixed664.charge.1,phase.mixed664.charge_cadence⟩
  have hgain4 : cut4.afterArrival.x 2 (.z 0) = s.x 2 (.z 0) + 12 / 5 :=
    (phase.high668.gain_preserved 0).symm.trans phase.gain_target
  have hG4 : 16 / 5 ≤ Real.exp (cut4.afterArrival.x 2 (.z 0)) ∧
      Real.exp (cut4.afterArrival.x 2 (.z 0)) ≤ 7 / 2 := by
    rw [hgain4]
    exact ⟨cadence_four_dose_gain_lower (by linarith [hz.1]),
      (cadence_high_gain_bounds (by linarith [hz.1]) (by linarith [hz.2])).2⟩
  have hb4 : 37999 / 100000 ≤ cut4.afterArrival.x 2 .b := by
    rw [cut4.entry.physical_continuous,phase.mixed664.recovery_gain,
      cut3.entry.physical_continuous,phase.strong660.recovery_preserved,
      cut2.entry.physical_continuous,phase.mark656.recovery_gain,
      cut1.entry.physical_continuous,phase.strong652.recovery_preserved,pre.c_recovery]
    linarith [hbRange.1]
  have ha4 : ∀ q, cut4.afterArrival.aux 2 q = .ready ∧ RestBand (cut4.afterArrival.x 2 (.m q)) := by
    intro q
    rw [cut4.modes_after.2,cut4.entry.physical_continuous]
    exact phase.mixed664.auxiliary q
  have hr4 : cut4.afterArrival.raw 2 0 = some cut4.afterArrival.time := cut4.raw_after
  have ho4 : ∀ q, q ≠ 0 → cut4.afterArrival.raw 2 q = none := by
    intro q hq
    rw [cut4.raw_other 2 q (Or.inr hq)]
    exact phase.mixed664.raw_finished q
  let times : List ℝ := List.ofFn (fun k : Fin 17 => (672 : ℝ) + 4 * (k.val : ℝ))
  have hcalHigh : cut4.rest.cellDeliveries 2 = times.map (fun t => ⟨2,0,t⟩) := by
    simpa only [times,sourceTrain,List.map_ofFn,Function.comp_def] using cut4.later
  have htimes : (668 : ℝ) :: times = List.ofFn (fun k : Fin 18 => (668 : ℝ) + 4 * (k.val : ℝ)) := by
    have h := congrArg (List.map Delivery.due) (sourceTrain_succ (2 : Fin 3) 0 668 4 17)
    simpa only [sourceTrain,times,List.map_ofFn,Function.comp_def,List.map_cons,
      show (668 : ℝ) + 4 = 672 by norm_num] using h.symm
  have hspace : (cut4.afterArrival.time :: times).Pairwise (fun t v => t + 19 / 5 ≤ v) := by
    rw [cut4.date.2,htimes]
    apply List.pairwise_ofFn.mpr
    intro k l hkl
    have hk : (k.val : ℝ) + 1 ≤ l.val := by exact_mod_cast (Nat.add_one_le_iff.mpr hkl)
    linarith
  have hquiet : ∀ t ∈ cut4.afterArrival.time :: times, t + 19 / 5 ≤ u.time := by
    intro t hm
    rw [cut4.date.2,htimes] at hm
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hm
    have hk : (k.val : ℝ) ≤ 17 := by exact_mod_cast (show k.val ≤ 17 by omega)
    rw [hu]
    linarith
  obtain ⟨firstHigh,hHighLower,hHighUpper,hHighLe,hHighEmission⟩ :=
    cadence_high_residual_calendar_sharp_of_valid hb 2 0 times cut4.rest hf4 hv4 hs4 hq4 hG4 hb4
      ha4 hr4 ho4 hcalHigh hspace hquiet
  rw [hgain4] at hHighLe hHighEmission
  rw [cut4.date.2] at hHighEmission
  have hrestHigh := highRestLatency_spec (G := Real.exp (s.x 2 (.z 0) + 12 / 5)) (by
    simpa only [hgain4] using hG4)
  have hrestSharp := highRestLatency_lt_twenty_six (G := Real.exp (s.x 2 (.z 0) + 12 / 5)) (by
    simpa only [hgain4] using hG4)
  refine ⟨⟨firstLow,hLowLower,hLowUpper,hLowLe,hrestLow.1,hrestLow.2,
    firstHigh,by linarith,by linarith,hHighLe,hrestHigh.1,hrestHigh.2.1,hHighLower,hrestSharp,?_⟩⟩
  have hemission := congrArg (fun actual => actual.emissionTimes 2) pre.reconstruct
  rw [Execution.emissionTimes_append,pre.c_emissions,List.nil_append] at hemission
  rw [hemission,cut1.emissions,cut2.emissions,cut3.emissions,cut4.emissions,
    hLowEmission,phase.mark656.emissions,hRestEmission,phase.mixed664.emissions,hHighEmission]
  simp only [List.nil_append,List.cons_append,times,List.map_ofFn,Function.comp_def]

end KernelR.Hybrid
