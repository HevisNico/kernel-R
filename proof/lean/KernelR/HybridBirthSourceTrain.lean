import KernelR.HybridWarmup
/-! The complete first low-port source phase, conditional on an actual complete execution. -/
namespace KernelR.Hybrid

structure BirthSourceTrain {n θ route born u} (e : @Execution n θ route born u)
    (i : Fin n) (p : Port) where
  emissions : (e.emissionTimes i).length = 12
  error_target : e.ledger.error i p = 9 / 5
  error_other : ∀ q, q ≠ p → e.ledger.error i q = 0
  mark_target : e.ledger.mark i p = 1 / 10
  mark_other : ∀ q, q ≠ p → e.ledger.mark i q = 0
  gain_target : u.x i (.z p) = born.x i (.z p) + 9 / 5
  gain_other : ∀ q, q ≠ p → u.x i (.z q) = born.x i (.z q)
  recovery_gain : u.x i .b = born.x i .b + 1 / 10
  prepared : PreparedSection u i
  charge_rest : u.x i .q = 1 / 10
  raw_finished : ∀ q, u.raw i q = none

/-- The sixteen low-port sources from zero to 120 prepare a READY-born cell.
All weak, strong, protected and learned cases are derived from the trace. -/
theorem Execution.birth_low_train {n θ ε route born u} (e : @Execution n θ route born u)
    (hborn : BirthState born) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hp : p ≠ 1)
    (ha : ∀ q, born.aux i q = .ready)
    (hcalendar : e.deliveries = sourceTrain i p 0 8 16) (ht : 128 ≤ u.time) :
    Nonempty (BirthSourceTrain e i p) := by
  obtain ⟨birth⟩ := e.birth_input hborn i p 15 ha hcalendar
  have hbirthx : birth.cut.afterArrival.x = born.x := by
    rw [birth.cut.entry.physical_continuous]
    apply birth.cut.span.zero_duration_continuous
    rw [hborn.1]
    exact birth.cut.date.1
  have hzborn : Real.log (3 / 10) - 1 / 100000 ≤ birth.cut.afterArrival.x i (.z p) ∧
      birth.cut.afterArrival.x i (.z p) ≤ Real.log (3 / 10) + 1 / 100000 := by
    rw [hbirthx]
    simpa only [nominalGain,ite_eq_right hp] using ((hborn.2.2 i).2.2.2.2 p).1
  let pastFirst := birth.cut.span.append (.cons (.jump birth.cut.entry) (.nil _))
  have hfirstCal : birth.cut.rest.deliveries = sourceTrain i p (birth.cut.afterArrival.time + 8) 8 (3 + 12) := by
    rw [birth.cut.later,birth.date]
    norm_num
  obtain ⟨warm⟩ := warmup_prefix hborn hb i p 3 0 12 birth.cut.rest pastFirst birth.coordinates
    (by norm_num) (by simpa using hzborn) birth.raw_active birth.raw_other hfirstCal
  have hwdate : warm.entry.time = 24 := by rw [warm.date,birth.date]; norm_num
  have hzentry : Real.log (3 / 10) + 9 / 5 - 1 / 100000 ≤ warm.entry.x i (.z p) ∧
      warm.entry.x i (.z p) ≤ Real.log (3 / 10) + 9 / 5 + 1 / 100000 := by
    rw [warm.gain_target]
    norm_num
    constructor <;> linarith [hzborn.1,hzborn.2]
  have hgain : 9 / 5 ≤ Real.exp (warm.entry.x i (.z p)) ∧ Real.exp (warm.entry.x i (.z p)) ≤ 12 / 5 := by
    have h := learned_gain_bounds hzentry.1 hzentry.2
    exact ⟨h.1,by linarith [h.2]⟩
  have hbrecovery : 7999 / 100000 ≤ warm.entry.x i .b ∧ warm.entry.x i .b ≤ 8001 / 100000 := by
    rw [warm.recovery_preserved]
    exact birth.recovery
  have hstrongCal : warm.rest.deliveries = ⟨i,p,32⟩ :: sourceTrain i p 40 8 11 := by
    calc
      warm.rest.deliveries = sourceTrain i p 32 8 12 := by rw [warm.calendar,hwdate]; norm_num
      _ = _ := by simpa only [show (32 : ℝ) + 8 = 40 by norm_num] using sourceTrain_succ i p 32 8 11
  obtain ⟨strongCut⟩ := warm.rest.first_delivery _ _ hstrongCal
  have hsdate : strongCut.beforeArrival.time = 32 := strongCut.date.1
  have hsafter : strongCut.afterArrival.time = 32 := strongCut.date.2
  let pastWarm := birth.cut.span.append (.cons (.jump birth.cut.entry) warm.head)
  obtain ⟨strong⟩ := strongCut.span.first_strong_low_recovery pastWarm hborn hb i p warm.coordinates
    hbrecovery hgain warm.raw_active warm.raw_other (strongCut.no_arrivals_before i)
    (by constructor <;> linarith)
  have hprotectedCal : strongCut.rest.deliveries = ⟨i,p,40⟩ :: sourceTrain i p 48 8 10 := by
    calc
      strongCut.rest.deliveries = sourceTrain i p 40 8 11 := strongCut.later
      _ = _ := by simpa only [show (40 : ℝ) + 8 = 48 by norm_num] using sourceTrain_succ i p 40 8 10
  obtain ⟨protectedCut⟩ := strongCut.rest.first_delivery _ _ hprotectedCal
  have hpdate : protectedCut.beforeArrival.time = 40 := protectedCut.date.1
  have hpafter : protectedCut.afterArrival.time = 40 := protectedCut.date.2
  have hmarkEntry := strongCut.mark_entry i strong.mark_entry
  have hsraw : strongCut.afterArrival.raw i p = some strongCut.afterArrival.time := strongCut.raw_after
  have hsother : ∀ q, q ≠ p → strongCut.afterArrival.raw i q = none := by
    intro q hq
    rw [strongCut.raw_other i q (Or.inr hq)]
    exact strong.raw_finished q
  let pastStrong := pastWarm.append (strongCut.span.append (.cons (.jump strongCut.entry) (.nil _)))
  obtain ⟨markPulse⟩ := protectedCut.span.protected_pulse pastStrong hborn hb i p hmarkEntry hsraw hsother
    (protectedCut.no_arrivals_before i) (by linarith)
  have hprepared := protectedCut.prepared i markPulse.prepared
  have hnextgain : 9 / 5 ≤ Real.exp (protectedCut.afterArrival.x i (.z p)) ∧
      Real.exp (protectedCut.afterArrival.x i (.z p)) ≤ 12 / 5 := by
    rw [protectedCut.entry.physical_continuous,markPulse.gain_preserved p,
      strongCut.entry.physical_continuous,strong.gain_preserved p]
    exact hgain
  have hpraw : protectedCut.afterArrival.raw i p = some protectedCut.afterArrival.time := protectedCut.raw_after
  have hpother : ∀ q, q ≠ p → protectedCut.afterArrival.raw i q = none := by
    intro q hq
    rw [protectedCut.raw_other i q (Or.inr hq)]
    exact markPulse.raw_finished q
  have htailCal : protectedCut.rest.deliveries = sourceTrain i p (protectedCut.afterArrival.time + 8) 8 10 := by
    rw [protectedCut.later,hpafter]
    norm_num
  let pastPrepared := pastStrong.append (protectedCut.span.append (.cons (.jump protectedCut.entry) (.nil _)))
  obtain ⟨train⟩ := prepared_train hborn hb i p 10 protectedCut.rest pastPrepared hprepared hnextgain hpraw hpother htailCal
    (by rw [hpafter]; norm_num; linarith)
  have hztarget : u.x i (.z p) = born.x i (.z p) + 9 / 5 := by
    rw [train.gain_preserved p,protectedCut.entry.physical_continuous,markPulse.gain_preserved p,
      strongCut.entry.physical_continuous,strong.gain_preserved p,warm.gain_target,birth.gain_preserved p]
    norm_num
  have hzother : ∀ q, q ≠ p → u.x i (.z q) = born.x i (.z q) := by
    intro q hq
    rw [train.gain_preserved q,protectedCut.entry.physical_continuous,markPulse.gain_preserved q,
      strongCut.entry.physical_continuous,strong.gain_preserved q,warm.gain_other q hq,birth.gain_preserved q]
  have hbgain : u.x i .b = born.x i .b + 1 / 10 := by
    rw [train.recovery_preserved,protectedCut.entry.physical_continuous,markPulse.recovery_gain,
      strongCut.entry.physical_continuous,strong.recovery_preserved,warm.recovery_preserved,hbirthx]
  have hmarkother : ∀ q, q ≠ p → e.ledger.mark i q = 0 := by
    intro q hq
    have hn : NoArrivalAt e i q := by
      intro d hd
      rw [hcalendar] at hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      exact Or.inr (Ne.symm hq)
    have hquiet := e.aux_ready_without_input_band i q (ha q)
      ((hborn.ready_coordinates i ha).auxiliary q).2.2 (hborn.2.1 i q) hn
    exact e.mark_zero_aux i q .ready (by decide) (e.allStates_aux_flows i q .ready hquiet)
  have hmark : e.ledger.mark i p = 1 / 10 := by
    have hsum : e.ledger.recovery i = e.ledger.mark i p := by
      rw [e.recovery_sum_marks i]
      exact Finset.sum_eq_single p (fun q _ hq => hmarkother q hq) (by simp)
    have hbalance := e.recovery_balance i
    rw [hsum] at hbalance
    linarith
  have hwem : birth.cut.rest.emissionTimes i = warm.head.emissionTimes i ++ warm.rest.emissionTimes i := by
    calc
      birth.cut.rest.emissionTimes i = (warm.head.append warm.rest).emissionTimes i :=
        congrArg (fun actual => actual.emissionTimes i) warm.reconstruct
      _ = _ := Execution.emissionTimes_append _ _ i
  refine ⟨⟨?_,?_,?_,hmark,hmarkother,hztarget,hzother,hbgain,train.prepared,train.charge_rest,train.raw_finished⟩⟩
  · rw [birth.cut.emissions i,birth.emissions_before,List.nil_append,hwem,warm.emissions,List.nil_append,
      strongCut.emissions i,strong.emissions,protectedCut.emissions i,markPulse.emissions,List.nil_append,
      List.length_append,List.length_singleton,train.emissions]
  · have h := e.gain_balance i p
    linarith
  · intro q hq
    have h := e.gain_balance i q
    rw [hzother q hq] at h
    linarith

/-- Queue instantiation of the first source phase. CompleteThrough is a premise;
no existence or later staged-birth protocol is asserted. -/
theorem Execution.birth_low_source_queue {n θ ε route born u} (e : @Execution n θ route born u)
    (hborn : BirthState born) (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hp : p ≠ 1)
    (ha : ∀ q, born.aux i q = .ready) (T : ℝ) (hc : CompleteThrough e T)
    (hq : born.pending = sourceTrain i p 0 8 16) (hT : 128 ≤ T) (hr : ∀ i t, route i t = []) :
    Nonempty (BirthSourceTrain e i p) := by
  have hd := e.source_train_deliveries i p 0 8 16 T hc hq (by norm_num) (by norm_num; exact hT) hr
  exact e.birth_low_train hborn hb i p hp ha hd (by rw [hc.1]; exact hT)

end KernelR.Hybrid
