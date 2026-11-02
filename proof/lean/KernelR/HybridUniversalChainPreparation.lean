import KernelR.HybridBirthPreparation
import KernelR.HybridAutonomousCellProjection
import KernelR.HybridEmissionRouterTransport
import KernelR.HybridFiniteChainFamilyPreparation

/-! Universal preparation prefixes. These results quantify over supplied actual
executions, without supplying a prepared endpoint, pulse-case decomposition or
received calendar. Other cells may interleave freely. Routes need only be
closed through the selected preparation horizon. Both nominal training-port regimes are proved from actual source queues. -/
namespace KernelR.Hybrid

/-- Birth bands survive exact projection onto one physical cell. -/
theorem BirthState.autonomousView {n s} (hs : @BirthState n s) (i : Fin n) :
    BirthState (s.autonomousView i) := by
  refine ⟨hs.1,?_,?_⟩
  · intro j p
    exact hs.2.1 i p
  · intro j
    exact hs.2.2 i

private theorem atCell_one (d : Delivery 1) : Delivery.atCell 0 d=some d := by
  rcases d with ⟨cell,port,due⟩
  have hc : cell=0 := Subsingleton.elim _ _
  subst cell
  simp [Delivery.atCell]

private theorem cellQueue_one (Q : List (Delivery 1)) : cellQueue 0 Q=Q := by
  induction Q with
  | nil => rfl
  | cons d Q ih => simpa only [cellQueue,List.filterMap_cons,atCell_one] using congrArg (d :: ·) ih

private theorem cellQueue_head_zero {n} (Q : List (Delivery 1)) :
    cellQueue (0 : Fin (n+1)) (Q.map Delivery.head)=Q := by
  induction Q with
  | nil => rfl
  | cons d Q ih =>
    have hd : Delivery.atCell (0 : Fin (n+1)) (Delivery.head d)=some d := by
      rcases d with ⟨cell,port,due⟩
      have hc : cell=0 := Subsingleton.elim _ _
      subst cell
      simp [Delivery.atCell,Delivery.head]
    simpa only [List.map_cons,cellQueue,List.filterMap_cons,hd] using congrArg (d :: ·) ih

private theorem cellQueue_head_succ {n} (i : Fin n) (Q : List (Delivery 1)) :
    cellQueue i.succ (Q.map Delivery.head)=[] := by
  induction Q with
  | nil => rfl
  | cons d Q ih =>
    have hne : (0 : Fin (n+1))≠i.succ := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_zero,Fin.val_succ] at hv
      omega
    simp [cellQueue,Delivery.atCell,Delivery.head,hne]

private theorem cellQueue_succ_zero {n} (Q : List (Delivery n)) :
    cellQueue (0 : Fin (n+1)) (Q.map Delivery.succ)=[] := by
  induction Q with
  | nil => rfl
  | cons d Q ih => simp [cellQueue,Delivery.atCell,Delivery.succ]

private theorem cellQueue_succ_succ {n} (i : Fin n) (Q : List (Delivery n)) :
    cellQueue i.succ (Q.map Delivery.succ)=cellQueue i Q := by
  induction Q with
  | nil => rfl
  | cons d Q ih =>
    have hd : Delivery.atCell i.succ (Delivery.succ d)=Delivery.atCell i d := by
      simp only [Delivery.atCell,Delivery.succ,Fin.succ_inj]
    cases h : Delivery.atCell i d <;>
      simpa only [cellQueue,List.map_cons,List.filterMap_cons,hd,h,List.cons.injEq,true_and] using ih

/-- The global common-birth source retains every cell's exact own source queue.
This is queue algebra only and contains no physical preparation conclusion. -/
theorem cellQueue_independentFamilySource {n} (bornCells : Fin (n+1)→Snapshot 1)
    (i : Fin (n+1)) :
    cellQueue i (independentFamilySource bornCells).pending=(bornCells i).pending := by
  induction n with
  | zero =>
    fin_cases i
    exact cellQueue_one _
  | succ n ih =>
    rw [independent_family_source_queue_succ,cellQueue_append]
    cases i using Fin.cases with
    | zero => rw [cellQueue_head_zero,cellQueue_succ_zero,List.append_nil]
    | succ i => rw [cellQueue_head_succ,cellQueue_succ_succ,List.nil_append,ih]

private theorem cellQueue_sourceTrain_other {n} (i j : Fin n) (hij : j≠i)
    (p : Port) (start gap : ℝ) (count : ℕ) :
    cellQueue i (sourceTrain j p start gap count)=[] := by
  unfold cellQueue
  apply List.filterMap_eq_nil_iff.mpr
  intro d hd
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
  simp [Delivery.atCell,hij]

/-- An actual cut before contact opening, with its routing-erased exact trace
and one-cell physical projection. The original cut relation is retained. -/
structure UniversalAutonomousPrefix {n θ route born u}
    (e : @Execution n θ route born u) (i : Fin n) (H : ℝ) where
  state : Snapshot n
  date : state.time=H
  span : Execution θ route born state
  is_prefix : e.IsPrefix span
  erased : Execution θ (fun _ _ => []) born state
  erased_ledger : erased.ledger=span.ledger
  erased_deliveries : erased.deliveries=span.deliveries
  projection : AutonomousCellProjection erased i

/-- Contact closure is needed only at actual cut FIREs, not at future times.
This statement applies to every supplied execution reaching H. -/
theorem Execution.universal_autonomous_prefix {n θ route born u}
    (e : @Execution n θ route born u) (i : Fin n) (H : ℝ)
    (hstart : born.time≤H) (hend : H≤u.time)
    (hclosed : ∀ j t, t≤H → route j t=[]) :
    Nonempty (UniversalAutonomousPrefix e i H) := by
  obtain ⟨state,span,hprefix,hdate⟩ := e.prefix_at H hstart hend
  obtain ⟨erased,hledger,hdeliveries⟩ := span.retarget_router (fun _ _ => []) (by
    intro event he
    exact hclosed event.1 event.2 (by
      have h := (span.emission_time_bounds event he).2
      simpa only [hdate] using h))
  obtain ⟨projection⟩ := erased.autonomous_cell_exists i (by
    intro j t d hd
    exact False.elim (List.not_mem_nil hd))
  exact ⟨⟨state,hdate,span,hprefix,erased,hledger,hdeliveries,projection⟩⟩

structure BirthFastSourceTrain {n θ route born u} (e : @Execution n θ route born u)
    (i : Fin n) where
  emissions : (e.emissionTimes i).length = 14
  error_target : e.ledger.error i (1 : Port) = 3 / 5
  error_other : ∀ q, q ≠ (1 : Port) → e.ledger.error i q = 0
  mark_target : e.ledger.mark i (1 : Port) = 1 / 10
  mark_other : ∀ q, q ≠ (1 : Port) → e.ledger.mark i q = 0
  gain_target : u.x i (.z (1 : Port)) = born.x i (.z (1 : Port)) + 3 / 5
  gain_other : ∀ q, q ≠ (1 : Port) → u.x i (.z q) = born.x i (.z q)
  recovery_gain : u.x i .b = born.x i .b + 1 / 10
  prepared : PreparedSection u i
  charge_rest : u.x i .q = 1 / 10
  raw_finished : ∀ q, u.raw i q = none

/-- Every actual isolated nominal-fast-port birth train has its own physical
weak/strong/protected/prepared decomposition; no decomposition is supplied. -/
theorem Execution.birth_fast_train {n θ ε route born u}
    (e : @Execution n θ route born u) (hborn : BirthState born)
    (hb : PhysicalBox θ ε) (i : Fin n) (ha : ∀ q, born.aux i q=.ready)
    (hcalendar : e.deliveries=sourceTrain i 1 0 8 16) (ht : (128:ℝ)≤u.time) :
    Nonempty (BirthFastSourceTrain e i) := by
  obtain ⟨birth⟩ := e.birth_input hborn i 1 15 ha hcalendar
  have hbirthx : birth.cut.afterArrival.x=born.x := by
    rw [birth.cut.entry.physical_continuous]
    apply birth.cut.span.zero_duration_continuous
    rw [hborn.1]
    exact birth.cut.date.1
  have hzborn : Real.log (6/5)-1/100000≤birth.cut.afterArrival.x i (.z 1) ∧
      birth.cut.afterArrival.x i (.z 1)≤Real.log (6/5)+1/100000 := by
    rw [hbirthx]
    simpa only [nominalGain,ite_true] using ((hborn.2.2 i).2.2.2.2 1).1
  let pastFirst := birth.cut.span.append (.cons (.jump birth.cut.entry) (.nil _))
  have hfirstCal : birth.cut.rest.deliveries=⟨i,1,8⟩::sourceTrain i 1 16 8 14 := by
    rw [birth.cut.later]
    simpa only [show (8:ℝ)+8=16 by norm_num] using sourceTrain_succ i 1 8 8 14
  obtain ⟨weakCut⟩ := birth.cut.rest.first_delivery _ _ hfirstCal
  obtain ⟨weak⟩ := weakCut.span.silent_pulse pastFirst hborn hb i 1 birth.coordinates
    (by linarith [hzborn.2]) birth.raw_active birth.raw_other (weakCut.no_arrivals_before i)
    (by have hd := weakCut.date.1; dsimp at hd; rw [birth.date]; linarith)
  let warm : Warmup birth.cut.rest i 1 1 14 := {
    entry:=weakCut.afterArrival
    head:=weakCut.span.append (.cons (.jump weakCut.entry) (.nil _))
    rest:=weakCut.rest
    reconstruct:=by
      calc
        birth.cut.rest=weakCut.span.append (.cons (.jump weakCut.entry) weakCut.rest) := weakCut.reconstruct
        _ = _ := by simp only [Execution.append_assoc,Execution.append]
    coordinates:=weakCut.ready_coordinates i weak.coordinates
    recovery_preserved:=by rw [weakCut.entry.physical_continuous,weak.recovery_preserved]
    gain_target:=by rw [weakCut.entry.physical_continuous,weak.gain_target]; norm_num
    gain_other:=by intro q hq; rw [weakCut.entry.physical_continuous,weak.gain_other q hq]
    emissions:=by
      rw [Execution.emissionTimes_append,weak.emissions]
      simp [Execution.emissionTimes,Execution.ledger,Ledger.zero,Ledger.add,Move.ledger,weakCut.entry.no_emissions_of_delivery _
        (show (⟨i,1,8⟩ : Delivery n)∈weakCut.entry.deliveries by rw [weakCut.delivery]; simp)]
    mark_zero:=by intro q; simp [Execution.mark_append,weak.mark_zero q,Execution.ledger,Move.ledger,weakCut.entry.mark_zero,Ledger.zero,Ledger.add]
    raw_active:=weakCut.raw_after
    raw_other:=by
      intro q hq
      rw [weakCut.raw_other i q (Or.inr hq)]
      exact weak.raw_finished q
    date:=by rw [weakCut.date.2,birth.date]; norm_num
    calendar:=by rw [weakCut.later,weakCut.date.2]; norm_num
  }
  have hwdate : warm.entry.time=8 := by rw [warm.date,birth.date]; norm_num
  have hzentry : Real.log (6/5)+3/5-1/100000≤warm.entry.x i (.z 1) ∧
      warm.entry.x i (.z 1)≤Real.log (6/5)+3/5+1/100000 := by
    rw [warm.gain_target]
    norm_num
    constructor <;> linarith [hzborn.1,hzborn.2]
  have hgain : 9/5≤Real.exp (warm.entry.x i (.z 1)) ∧
      Real.exp (warm.entry.x i (.z 1))≤12/5 := by
    have h := fast_learned_gain_sharp_bounds hzentry.1 hzentry.2
    exact ⟨h.1,by linarith [h.2]⟩
  have hbrecovery : 7999 / 100000 ≤ warm.entry.x i .b ∧ warm.entry.x i .b ≤ 8001 / 100000 := by
    rw [warm.recovery_preserved]
    exact birth.recovery
  have hstrongCal : warm.rest.deliveries = ⟨i,(1 : Port),16⟩ :: sourceTrain i (1 : Port) 24 8 13 := by
    calc
      warm.rest.deliveries = sourceTrain i (1 : Port) 16 8 14 := by rw [warm.calendar,hwdate]; norm_num
      _ = _ := by simpa only [show (16 : ℝ) + 8 = 24 by norm_num] using sourceTrain_succ i (1 : Port) 16 8 13
  obtain ⟨strongCut⟩ := warm.rest.first_delivery _ _ hstrongCal
  have hsdate : strongCut.beforeArrival.time = 16 := strongCut.date.1
  have hsafter : strongCut.afterArrival.time = 16 := strongCut.date.2
  let pastWarm := birth.cut.span.append (.cons (.jump birth.cut.entry) warm.head)
  obtain ⟨strong⟩ := strongCut.span.first_strong_low_recovery pastWarm hborn hb i (1 : Port) warm.coordinates
    hbrecovery hgain warm.raw_active warm.raw_other (strongCut.no_arrivals_before i)
    (by constructor <;> linarith)
  have hprotectedCal : strongCut.rest.deliveries = ⟨i,(1 : Port),24⟩ :: sourceTrain i (1 : Port) 32 8 12 := by
    calc
      strongCut.rest.deliveries = sourceTrain i (1 : Port) 24 8 13 := strongCut.later
      _ = _ := by simpa only [show (24 : ℝ) + 8 = 32 by norm_num] using sourceTrain_succ i (1 : Port) 24 8 12
  obtain ⟨protectedCut⟩ := strongCut.rest.first_delivery _ _ hprotectedCal
  have hpdate : protectedCut.beforeArrival.time = 24 := protectedCut.date.1
  have hpafter : protectedCut.afterArrival.time = 24 := protectedCut.date.2
  have hmarkEntry := strongCut.mark_entry i strong.mark_entry
  have hsraw : strongCut.afterArrival.raw i (1 : Port) = some strongCut.afterArrival.time := strongCut.raw_after
  have hsother : ∀ q, q ≠ (1 : Port) → strongCut.afterArrival.raw i q = none := by
    intro q hq
    rw [strongCut.raw_other i q (Or.inr hq)]
    exact strong.raw_finished q
  let pastStrong := pastWarm.append (strongCut.span.append (.cons (.jump strongCut.entry) (.nil _)))
  obtain ⟨markPulse⟩ := protectedCut.span.protected_pulse pastStrong hborn hb i (1 : Port) hmarkEntry hsraw hsother
    (protectedCut.no_arrivals_before i) (by linarith)
  have hprepared := protectedCut.prepared i markPulse.prepared
  have hnextgain : 9 / 5 ≤ Real.exp (protectedCut.afterArrival.x i (.z (1 : Port))) ∧
      Real.exp (protectedCut.afterArrival.x i (.z (1 : Port))) ≤ 12 / 5 := by
    rw [protectedCut.entry.physical_continuous,markPulse.gain_preserved (1 : Port),
      strongCut.entry.physical_continuous,strong.gain_preserved (1 : Port)]
    exact hgain
  have hpraw : protectedCut.afterArrival.raw i (1 : Port) = some protectedCut.afterArrival.time := protectedCut.raw_after
  have hpother : ∀ q, q ≠ (1 : Port) → protectedCut.afterArrival.raw i q = none := by
    intro q hq
    rw [protectedCut.raw_other i q (Or.inr hq)]
    exact markPulse.raw_finished q
  have htailCal : protectedCut.rest.deliveries = sourceTrain i (1 : Port) (protectedCut.afterArrival.time + 8) 8 12 := by
    rw [protectedCut.later,hpafter]
    norm_num
  let pastPrepared := pastStrong.append (protectedCut.span.append (.cons (.jump protectedCut.entry) (.nil _)))
  obtain ⟨train⟩ := prepared_train hborn hb i (1 : Port) 12 protectedCut.rest pastPrepared hprepared hnextgain hpraw hpother htailCal
    (by rw [hpafter]; norm_num; linarith)
  have hztarget : u.x i (.z (1 : Port)) = born.x i (.z (1 : Port)) + 3 / 5 := by
    rw [train.gain_preserved (1 : Port),protectedCut.entry.physical_continuous,markPulse.gain_preserved (1 : Port),
      strongCut.entry.physical_continuous,strong.gain_preserved (1 : Port),warm.gain_target,birth.gain_preserved (1 : Port)]
    norm_num
  have hzother : ∀ q, q ≠ (1 : Port) → u.x i (.z q) = born.x i (.z q) := by
    intro q hq
    rw [train.gain_preserved q,protectedCut.entry.physical_continuous,markPulse.gain_preserved q,
      strongCut.entry.physical_continuous,strong.gain_preserved q,warm.gain_other q hq,birth.gain_preserved q]
  have hbgain : u.x i .b = born.x i .b + 1 / 10 := by
    rw [train.recovery_preserved,protectedCut.entry.physical_continuous,markPulse.recovery_gain,
      strongCut.entry.physical_continuous,strong.recovery_preserved,warm.recovery_preserved,hbirthx]
  have hmarkother : ∀ q, q ≠ (1 : Port) → e.ledger.mark i q = 0 := by
    intro q hq
    have hn : NoArrivalAt e i q := by
      intro d hd
      rw [hcalendar] at hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      exact Or.inr (Ne.symm hq)
    have hquiet := e.aux_ready_without_input_band i q (ha q)
      ((hborn.ready_coordinates i ha).auxiliary q).2.2 (hborn.2.1 i q) hn
    exact e.mark_zero_aux i q .ready (by decide) (e.allStates_aux_flows i q .ready hquiet)
  have hmark : e.ledger.mark i (1 : Port) = 1 / 10 := by
    have hsum : e.ledger.recovery i = e.ledger.mark i (1 : Port) := by
      rw [e.recovery_sum_marks i]
      exact Finset.sum_eq_single (1 : Port) (fun q _ hq => hmarkother q hq) (by simp)
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
  · have h := e.gain_balance i (1 : Port)
    linarith
  · intro q hq
    have h := e.gain_balance i q
    rw [hzother q hq] at h
    linarith

/-- All first-train deliveries and resulting physical phases are derived from
an initial queue containing the declared sixteen sources and genuinely later
sources. This is universal over the actual one-cell execution. -/
theorem Execution.birth_low_train_at128_future {θ ε born u}
    (e : @Execution 1 θ (fun _ _ => []) born u)
    (hborn : BirthState born) (hb : PhysicalBox θ ε) (p : Port) (hp : p≠1)
    (ha : ∀ q, born.aux 0 q=.ready) (later : List (Delivery 1))
    (hq : born.pending=sourceTrain 0 p 0 8 16++later)
    (hlater : ∀ d∈later, (128:ℝ)<d.due) (hdate : u.time=128) :
    Nonempty (BirthSourceTrain e 0 p) := by
  have hfuture : PendingFuture born := by
    intro d hd
    rw [hq] at hd
    rw [hborn.1]
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      positivity
    · linarith [hlater d hd]
  have hcalendar : e.deliveries=sourceTrain 0 p 0 8 16 := by
    apply e.deliveries_due_prefix_exact (sourceTrain 0 p 0 8 16) later hq
      ?_ ?_ (e.pending_future (by simp [CausalRouter]) hfuture) (by simp) 0 p ?_ ?_
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      rw [hdate]
      have hk : (k.val:ℝ)<16 := by exact_mod_cast k.isLt
      dsimp
      linarith
    · simpa only [hdate] using hlater
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      exact ⟨rfl,rfl⟩
    · apply List.pairwise_ofFn.mpr
      intro k l hkl
      have hk : (k.val:ℝ)≤l.val := by exact_mod_cast hkl.le
      dsimp
      linarith
  exact e.birth_low_train hborn hb 0 p hp ha hcalendar (by rw [hdate])

/-- All first-train deliveries and resulting physical phases are derived from
an initial queue containing the declared sixteen sources and genuinely later
sources. This is universal over the actual one-cell execution. -/
theorem Execution.birth_fast_train_at128_future {θ ε born u}
    (e : @Execution 1 θ (fun _ _ => []) born u)
    (hborn : BirthState born) (hb : PhysicalBox θ ε)
    (ha : ∀ q, born.aux 0 q=.ready) (later : List (Delivery 1))
    (hq : born.pending=sourceTrain 0 (1 : Port) 0 8 16++later)
    (hlater : ∀ d∈later, (128:ℝ)<d.due) (hdate : u.time=128) :
    Nonempty (BirthFastSourceTrain e 0) := by
  have hfuture : PendingFuture born := by
    intro d hd
    rw [hq] at hd
    rw [hborn.1]
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      dsimp
      positivity
    · linarith [hlater d hd]
  have hcalendar : e.deliveries=sourceTrain 0 (1 : Port) 0 8 16 := by
    apply e.deliveries_due_prefix_exact (sourceTrain 0 (1 : Port) 0 8 16) later hq
      ?_ ?_ (e.pending_future (by simp [CausalRouter]) hfuture) (by simp) 0 (1 : Port) ?_ ?_
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      rw [hdate]
      have hk : (k.val:ℝ)<16 := by exact_mod_cast k.isLt
      dsimp
      linarith
    · simpa only [hdate] using hlater
    · intro d hd
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
      exact ⟨rfl,rfl⟩
    · apply List.pairwise_ofFn.mpr
      intro k l hkl
      have hk : (k.val:ℝ)≤l.val := by exact_mod_cast hkl.le
      dsimp
      linarith
  exact e.birth_fast_train hborn hb 0 ha hcalendar (by rw [hdate])

/-- Universal relay preparation inside a larger finite network. Only the
initial projected source queue and pre-opening contact closure are supplied;
the received calendar, prepared state and memories are consequences. -/
structure UniversalLowPreparation {n θ route born u}
    (e : @Execution n θ route born u) (i : Fin n) (p : Port) where
  cut : UniversalAutonomousPrefix e i 128
  train : BirthSourceTrain cut.projection.execution 0 p
  prepared : PreparedSection cut.state i
  charge : cut.state.x i .q=1/10
  gain_target : cut.state.x i (.z p)=born.x i (.z p)+9/5
  gain_other : ∀ q, q≠p → cut.state.x i (.z q)=born.x i (.z q)
  recovery : cut.state.x i .b=born.x i .b+1/10
  raw_none : ∀ q, cut.state.raw i q=none
  emission_count : (cut.span.emissionTimes i).length=12

/-- Every execution reaching time128 prepares each isolated low-port cell,
including arbitrary interleavings in all other cells and retained future
sources. This is not an all-N terminal theorem or a high-port leaf theorem. -/
theorem Execution.universal_low_preparation {n θ ε route born u}
    (e : @Execution n θ route born u) (hborn : BirthState born)
    (hb : PhysicalBox θ ε) (i : Fin n) (p : Port) (hp : p≠1)
    (ha : ∀ q, born.aux i q=.ready) (later : List (Delivery 1))
    (hq : cellQueue i born.pending=sourceTrain 0 p 0 8 16++later)
    (hlater : ∀ d∈later, (128:ℝ)<d.due) (hend : (128:ℝ)≤u.time)
    (hclosed : ∀ j t, t≤(128:ℝ) → route j t=[]) :
    Nonempty (UniversalLowPreparation e i p) := by
  obtain ⟨cut⟩ := e.universal_autonomous_prefix i 128 (by rw [hborn.1]; norm_num) hend hclosed
  obtain ⟨train⟩ := cut.projection.execution.birth_low_train_at128_future
    (hborn.autonomousView i) (autonomous_physical_box hb i) p hp ha later hq hlater cut.date
  have htimes : cut.projection.execution.emissionTimes 0=cut.span.emissionTimes i := by
    rw [cut.projection.emission_times]
    simp only [Execution.emissionTimes,cut.erased_ledger]
  have hprepared : PreparedSection cut.state i :=
    ⟨train.prepared.ready,train.prepared.charge,train.prepared.recovery,train.prepared.auxiliary⟩
  exact ⟨⟨cut,train,hprepared,train.charge_rest,train.gain_target,
    train.gain_other,train.recovery_gain,train.raw_finished,
    (congrArg List.length htimes).symm.trans train.emissions⟩⟩

private theorem independent_family_source_aux_ready {n} (bornCells : Fin (n+1)→Snapshot 1)
    (ha : ∀ j q, (bornCells j).aux 0 q=.ready) (i : Fin (n+1)) (q : Port) :
    (independentFamilySource bornCells).aux i q=.ready := by
  induction n with
  | zero =>
    fin_cases i
    exact ha 0 q
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact ha 0 q
    | succ i => exact ih (fun j => bornCells j.succ) (fun j q => ha j.succ q) i

/-- Direct specialization to every relay of the current common-birth finite
chain. All other-cell sources are retained in the original global execution;
the required one-cell source queue is derived from the family queue. -/
theorem Execution.universal_chain_relay_preparation {n θ ε bornCells K route u}
    (e : Execution θ route (familyPreparationBornSource bornCells K) u)
    (hborn : ∀ j : Fin (n+1), BirthState (bornCells j))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ j q, (bornCells j).aux 0 q=.ready)
    (hqueue : ∀ j, (bornCells j).pending=sourceTrain 0 (finiteChainPreparationPort n j) 0 8 16)
    (i : Fin (n+1)) (hi : i≠Fin.last n) (hend : (128:ℝ)≤u.time)
    (hclosed : ∀ j t, t≤(128:ℝ) → route j t=[]) :
    Nonempty (UniversalLowPreparation e i 2) := by
  obtain ⟨family⟩ := finite_chain_family_preparation_exists (K:=K) hborn hb ha hqueue
  apply e.universal_low_preparation family.source_birth hb i 2 (by decide) ?_ [] ?_
    (by intro d hd; contradiction) hend hclosed
  · intro q
    change (independentFamilySource bornCells).aux i q=.ready
    exact independent_family_source_aux_ready bornCells ha i q
  · change cellQueue i ((independentFamilySource bornCells).pending++sourceTrain (Fin.last n) 0 160 4 K)=_
    rw [cellQueue_append,cellQueue_independentFamilySource,cellQueue_sourceTrain_other i (Fin.last n) (Ne.symm hi),List.append_nil,hqueue]
    simp only [finiteChainPreparationPort,hi,ite_false,List.append_nil]

/-- The actual nominal-fast-port leaf preparation, universal over supplied
network executions rather than a chosen constructive witness. -/
structure UniversalFastPreparation {n θ route born u}
    (e : @Execution n θ route born u) (i : Fin n) where
  cut : UniversalAutonomousPrefix e i 128
  train : BirthFastSourceTrain cut.projection.execution 0
  prepared : PreparedSection cut.state i
  charge : cut.state.x i .q=1/10
  gain_target : cut.state.x i (.z 1)=born.x i (.z 1)+3/5
  gain_other : ∀ q, q≠1 → cut.state.x i (.z q)=born.x i (.z q)
  recovery : cut.state.x i .b=born.x i .b+1/10
  raw_none : ∀ q, cut.state.raw i q=none
  emission_count : (cut.span.emissionTimes i).length=14

theorem Execution.universal_fast_preparation {n θ ε route born u}
    (e : @Execution n θ route born u) (hborn : BirthState born)
    (hb : PhysicalBox θ ε) (i : Fin n) (ha : ∀ q, born.aux i q=.ready)
    (later : List (Delivery 1))
    (hq : cellQueue i born.pending=sourceTrain 0 1 0 8 16++later)
    (hlater : ∀ d∈later, (128:ℝ)<d.due) (hend : (128:ℝ)≤u.time)
    (hclosed : ∀ j t, t≤(128:ℝ) → route j t=[]) :
    Nonempty (UniversalFastPreparation e i) := by
  obtain ⟨cut⟩ := e.universal_autonomous_prefix i 128 (by rw [hborn.1]; norm_num) hend hclosed
  obtain ⟨train⟩ := cut.projection.execution.birth_fast_train_at128_future
    (hborn.autonomousView i) (autonomous_physical_box hb i) ha later hq hlater cut.date
  have htimes : cut.projection.execution.emissionTimes 0=cut.span.emissionTimes i := by
    rw [cut.projection.emission_times]
    simp only [Execution.emissionTimes,cut.erased_ledger]
  have hprepared : PreparedSection cut.state i :=
    ⟨train.prepared.ready,train.prepared.charge,train.prepared.recovery,train.prepared.auxiliary⟩
  exact ⟨⟨cut,train,hprepared,train.charge_rest,train.gain_target,train.gain_other,
    train.recovery_gain,train.raw_finished,
    (congrArg List.length htimes).symm.trans train.emissions⟩⟩

private theorem cellQueue_sourceTrain_self {n} (i : Fin n) (p : Port)
    (start gap : ℝ) (count : ℕ) :
    cellQueue i (sourceTrain i p start gap count)=sourceTrain 0 p start gap count := by
  induction count generalizing start with
  | zero => simp [sourceTrain,cellQueue]
  | succ count ih =>
    rw [sourceTrain_succ,sourceTrain_succ]
    simp only [cellQueue,List.filterMap_cons,Delivery.atCell,ite_true]
    exact congrArg (fun tail => (⟨0,p,start⟩ : Delivery 1)::tail) (ih (start+gap))

/-- Every current common-birth chain execution that reaches128 contains the
leaf's own preparation. Its later K port-zero sources remain in its original
birth queue and are proved to be strictly future at the preparation horizon. -/
theorem Execution.universal_chain_leaf_preparation {n θ ε bornCells K route u}
    (e : Execution θ route (familyPreparationBornSource bornCells K) u)
    (hborn : ∀ j : Fin (n+1), BirthState (bornCells j))
    (hb : @PhysicalBox (n+1) θ ε) (ha : ∀ j q, (bornCells j).aux 0 q=.ready)
    (hqueue : ∀ j, (bornCells j).pending=sourceTrain 0 (finiteChainPreparationPort n j) 0 8 16)
    (hend : (128:ℝ)≤u.time)
    (hclosed : ∀ j t, t≤(128:ℝ) → route j t=[]) :
    Nonempty (UniversalFastPreparation e (Fin.last n)) := by
  obtain ⟨family⟩ := finite_chain_family_preparation_exists (K:=K) hborn hb ha hqueue
  apply e.universal_fast_preparation family.source_birth hb (Fin.last n) ?_
    (sourceTrain 0 0 160 4 K) ?_ ?_ hend hclosed
  · intro q
    change (independentFamilySource bornCells).aux (Fin.last n) q=.ready
    exact independent_family_source_aux_ready bornCells ha (Fin.last n) q
  · change cellQueue (Fin.last n) ((independentFamilySource bornCells).pending++sourceTrain (Fin.last n) 0 160 4 K)=_
    rw [cellQueue_append,cellQueue_independentFamilySource,cellQueue_sourceTrain_self,hqueue]
    simp only [finiteChainPreparationPort,ite_true]
  · intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    change (128:ℝ)<160+4*(k.val:ℝ)
    nlinarith [Nat.cast_nonneg (α:=ℝ) k.val]

end KernelR.Hybrid
