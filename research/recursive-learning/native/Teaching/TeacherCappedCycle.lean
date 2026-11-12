import Teaching.CappedWorkRun

/-! A teacher's ignition FIRE produces both of its local timer deliveries.
The subsequent selector FIRE reads the retained memory. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

noncomputable def cycleWork (delay : ℝ → ℝ) (fire : ℝ) : Delivery 1 :=
  ⟨0, 0, fire + delay fire⟩

noncomputable def cycleRead (delay : ℝ → ℝ) (fire : ℝ) : Delivery 1 :=
  ⟨0, 2, (cycleWork delay fire).due + 7 / 5⟩

/-- Only the ignition window starts the local timers. The read does not
start them again. -/
noncomputable def cappedCycleRouter (origin : ℝ) (delay : ℝ → ℝ) : Router 1 :=
  fun _ fire => if fire < origin + 1 then [cycleRead delay fire, cycleWork delay fire] else []

theorem cycle_delay_gt_one {delay σ : ℝ} (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : delay ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ)) :
    1 < delay := by
  have lower := wire.1
  simp only [cappedTeacherWorkOffset, cappedTeacherWorkJitter] at lower budget
  linarith [capped_teacher_period_bounds.1]

theorem capped_cycle_router_causal {origin delay σ} (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : ∀ fire, delay fire ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ)) :
    StrictCausalRouter (cappedCycleRouter origin delay) := by
  intro i fire d hd
  have positive := cycle_delay_gt_one budget (wire fire)
  simp only [cappedCycleRouter] at hd
  split at hd
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · change fire < fire + delay fire + 7 / 5
      linarith
    · change fire < fire + delay fire
      linarith
  · simp at hd

private theorem cycle_future_transverse {n θ route s u} (e : @Execution n θ route s u)
    (future : List (Delivery n)) (later : ∀ d ∈ future, u.time ≤ d.due)
    (positive : e.ContactsTransversal) : (e.withFuture future later).ContactsTransversal := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow f => exact ih later positive
    | jump j => exact ⟨(j.contactTransversal_requeue (j.withFuture future)).1 positive.1,
        ih later positive.2⟩

private theorem cycle_jump_future_deliveries {n route s u} (j : @Jump n route s u)
    (future : List (Delivery n)) : (j.withFuture future).deliveries = j.deliveries := by
  have one {a b : Snapshot n} (k : Jump route a b) (d : Delivery n) :
      (k.withOneFuture d).deliveries = k.deliveries := by cases k <;> rfl
  induction future with
  | nil => rfl
  | cons d ds ih => exact (one _ d).trans ih

private theorem cycle_future_deliveries {n θ route s u} (e : @Execution n θ route s u)
    (future : List (Delivery n)) (later : ∀ d ∈ future, u.time ≤ d.due) :
    (e.withFuture future later).deliveries = e.deliveries := by
  induction e with
  | nil => rfl
  | cons move rest ih =>
    cases move with
    | flow f => simpa [Execution.withFuture, Execution.deliveries, Move.deliveries] using ih later
    | jump j =>
      change (j.withFuture future).deliveries ++ (rest.withFuture future later).deliveries =
        j.deliveries ++ rest.deliveries
      rw [cycle_jump_future_deliveries, ih later]

structure CappedTeacherCycle (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (delay : ℝ → ℝ) (high : Bool) where
  ignition : ℝ
  work : Snapshot 1
  workDate : work.time = (cycleWork delay ignition).due
  lead : Execution θ (cappedCycleRouter s.time delay) s (withFuture work [cycleRead delay ignition])
  leadFires : lead.ledger.emissions = [(0, ignition)]
  leadDeliveries : lead.deliveries = [cycleWork delay ignition]
  ignitionWindow : s.time + 3 / 10 < ignition ∧ ignition < s.time + 9 / 10
  ignitionRoot : readyPulse (s.x 0 .q) (Real.exp (s.x 0 (.z 1))) s.time ignition = 1
  read : CappedWorkRead θ work high
  readDate : read.admitted.time = (cycleRead delay ignition).due
  continuation : Execution θ (cappedCycleRouter s.time delay)
    (withFuture work [cycleRead delay ignition]) read.read.final
  complete : CompleteThrough (lead.append continuation) read.read.horizon
  transverse : (lead.append continuation).ContactsTransversal
  fires : continuation.ledger.emissions = [(0, (cycleRead delay ignition).due + read.read.latency)]
  gains : ∀ p, read.read.final.x 0 (.z p) = s.x 0 (.z p)
  recovery : read.read.final.x 0 .b = 11 / 10

/-- From an admitted ignition pulse on port 1, a single native execution
routes its own work and read pulses. The initial queue is empty. -/
theorem capped_teacher_cycle_exists {θ ε s delay high σ} (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s) (valid : RawValid s) (ready : ReadyCoordinates s 0)
    (ignitionGain : 9 / 5 ≤ Real.exp (s.x 0 (.z 1)) ∧ Real.exp (s.x 0 (.z 1)) ≤ 11 / 5)
    (active : s.raw 0 1 = some s.time) (other : ∀ q, q ≠ 1 → s.raw 0 q = none)
    (recovery : s.x 0 .b = 11 / 10) (workGain : s.x 0 (.z 0) = Real.log ((θ 0).cap 0))
    (readGain : s.x 0 (.z 2) = selectorReadLogGain high) (empty : s.pending = [])
    (nonnegative : 0 ≤ σ) (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : ∀ fire, delay fire ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ)) :
    Nonempty (CappedTeacherCycle θ s delay high) := by
  let work : Port := 0
  have otherAll (i : Fin 1) (p : Port) (h : i ≠ 0 ∨ p ≠ 1) : s.raw i p = none := by
    rw [Subsingleton.elim i 0]
    exact other p (h.resolve_left (by simp [Subsingleton.elim i 0]))
  obtain ⟨fire⟩ := first_mid_learned_fire_exists (route := fun _ _ => []) s box physical valid
    0 1 (fun i => by rw [Subsingleton.elim i 0]; exact ready) ignitionGain active otherAll
    (by simp [empty])
  obtain ⟨fast⟩ := fire.mid_learned_fast_end_exists box ready ignitionGain.2 other (by simp [empty])
  let F := fire.final.time
  let token := cycleWork delay F
  let readToken := cycleRead delay F
  let pending := [readToken, token]
  let T := token.due
  let route := cappedCycleRouter s.time delay
  have fireWindow : s.time + 3 / 10 < F ∧ F < s.time + 9 / 10 := by
    change _ ∧ fire.final.time < _
    rw [show F = fire.final.time from rfl, fire.date]
    constructor <;> linarith [fire.early, fire.deadline]
  have fireRoutes : route 0 F = pending := by
    simp [route, cappedCycleRouter, pending, token, readToken, show F < s.time + 1 by linarith [fireWindow.2]]
  have fireQueue : fire.final.pending = [] := by rw [fire.pending, empty]; rfl
  have fastQueue : fast.final.pending = [] := fast.pending.trans fireQueue
  have delayPositive := cycle_delay_gt_one budget (wire F)
  have wait : fast.final.time < T := by
    rw [fast.date]
    change F + 1 < F + delay F
    linarith
  have readAfter : T < readToken.due := by change T < T + 7 / 5; linarith
  have future : ∀ d ∈ pending, fast.final.time ≤ d.due := by
    intro d hd
    simp only [pending, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact (wait.trans readAfter).le
    · exact wait.le
  let prior : Execution θ (fun _ _ => []) s (fire.firstSilent.learnedFireBefore fire.latency) :=
    (fire.firstSilent.execution _).append (.cons (.flow fire.flow) (.nil _))
  have priorSilent : prior.ledger.emissions = [] := by
    simp [prior, FirstInputSilent.execution, FirstInputSilent.continuation, FirstInputMark.execution,
      Execution.emissions_append, Execution.ledger, Move.ledger, Flow.ledger, Jump.ledger, Ledger.add, Ledger.zero]
  have priorTransverse : prior.ContactsTransversal :=
    (Execution.contactsTransversal_append _ _).2 ⟨fire.firstSilent.contacts_transversal _, trivial⟩
  have priorDeliveries : prior.deliveries = [] := by
    simp [prior, FirstInputSilent.execution, FirstInputSilent.continuation, FirstInputMark.execution,
      Execution.deliveries_append, Execution.deliveries, Move.deliveries, Jump.deliveries]
  obtain ⟨routedPrior, priorLedger, priorDeliveryEq, priorContact⟩ :=
    prior.retarget_router_transversal route (by simp [priorSilent])
  let fireJump : Jump route (fire.firstSilent.learnedFireBefore fire.latency)
      (fire.firstSilent.learnedFireFinal route fire.latency) :=
    .fire _ 0 (fire.firstSilent.main_ready 0) fire.threshold
  have fireEmission : fireJump.ledger.emissions = [(0,F)] := rfl
  have fireContact : fireJump.ContactTransversal θ := fire.contact_field_positive
  have fireEndpoint : fire.firstSilent.learnedFireFinal route fire.latency = withFuture fire.final pending := by
    have queue : (fire.firstSilent.learnedFireBefore fire.latency).pending = [] :=
      fire.firstSilent.queue_preserved.trans empty
    simp only [FirstInputSilent.learnedFireFinal, FirstLearnedFire.final, withFuture, queue,
      List.nil_append, List.append_nil]
    exact congrArg (fun q => { (setMain (fire.firstSilent.learnedFireBefore fire.latency) 0 .fast) with pending := q }) fireRoutes
  let fastFuture := fast.execution.withFuture pending future
  have fastSilent : fastFuture.ledger.emissions = [] := by
    rw [Execution.withFuture_ledger, fast.emissions]
  have fastDeliveries : fastFuture.deliveries = [] := by
    rw [cycle_future_deliveries, fast.deliveries]
  obtain ⟨routedFast, fastLedger, fastDeliveryEq, fastContact⟩ :=
    fastFuture.retarget_router_transversal route (by simp [fastSilent])
  have routedFastContact : routedFast.ContactsTransversal :=
    fastContact.mpr (cycle_future_transverse fast.execution pending future fast.contacts_transversal)
  let start := withFuture fast.final pending
  have startB : start.x 0 .b = 11 / 10 :=
    (fast.recovery 0).trans ((fire.recovery_preserved 0).trans recovery)
  let age := cappedTeacherPeriod - delay F
  have timing := capped_teacher_work_timing nonnegative budget (wire F) ε
  have agePositive : 0 < age := by
    have bounds := (capped_teacher_jitter_iff nonnegative).2 budget (delay F) (wire F)
    change 0 < cappedTeacherPeriod - delay F
    linarith [bounds.1]
  have chargeAtT :
      start.x 0 .q * Real.exp (-start.x 0 .b * (T - start.time)) =
        (1 / 10 : ℝ) * Real.exp ((11 / 10) * age) := by
    change fast.final.x 0 .q * Real.exp (-start.x 0 .b * (T - fast.final.time)) = _
    rw [fast.charge, startB, fast.date]
    change (1 / 4 : ℝ) * Real.exp (-(11 / 10) * (F + delay F - (F + 1))) = _
    rw [show F + delay F - (F + 1) = delay F - 1 by ring]
    exact capped_work_admission_charge (delay F)
  have lower : (1 / 10 : ℝ) < start.x 0 .q * Real.exp (-start.x 0 .b * (T - start.time)) := by
    rw [chargeAtT]
    linarith only [Real.one_lt_exp_iff.mpr (by linarith : (0 : ℝ) < 11 / 10 * age)]
  let beforeWork := protectedMainEnd θ start 0 work .slow .ready none T
  let quiet : Flow θ start beforeWork :=
    protectedMainFlow start 0 work .slow .ready none wait (Or.inr rfl) (Or.inl rfl)
      fast.main_slow (fun i h => (h (Subsingleton.elim i 0)).elim)
      (fast.auxiliary 0 work) (fun i p _ => fast.auxiliary i p)
      (fast.raw_none 0 work) (fun i p _ => fast.raw_none i p)
      (by intro o h; contradiction) (fun i h => (h (Subsingleton.elim i 0)).elim)
      (fun i p _ => by
        rw [Subsingleton.elim i 0]
        change fast.final.x 0 (.m p) < 1
        linarith [(fast.rest p).2])
      (by
        intro t ht
        change (1 / 10 : ℝ) < start.x 0 .q * Real.exp (-start.x 0 .b * (t - start.time))
        apply lower.trans_le (mul_le_mul_of_nonneg_left _ (by change 0 ≤ fast.final.x 0 .q; rw [fast.charge]; norm_num))
        apply Real.exp_le_exp.mpr
        rw [startB]
        linarith [ht.2])
      (by
        intro t ht
        simp only [ite_true, rawInputScale, mul_zero, auxPulse_zero_eq_relax]
        exact relax_lt (by norm_num) ht.1 (by
          change fast.final.x 0 (.m work) < 1
          linarith [(fast.rest work).2]) (by norm_num))
      (by
        intro d hd
        change d ∈ pending ++ fast.final.pending at hd
        simp only [fastQueue, List.append_nil, pending, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact readAfter.le
        · exact le_rfl)
  let admitted : Snapshot 1 := { (setRaw beforeWork token.cell token.port (some beforeWork.time)) with pending := [] }
  let arrive : Jump route beforeWork (withFuture admitted [readToken]) :=
    .arrive _ token [readToken] [] (by simp [beforeWork, protectedMainEnd, start, withFuture, fastQueue, pending])
      rfl (fast.raw_none 0 work)
  let handoff : Execution θ route start (withFuture admitted [readToken]) :=
    .cons (.flow quiet) (.cons (.jump arrive) (.nil _))
  have workSensor (p : Port) : admitted.aux 0 p = .ready ∧ RestBand (admitted.x 0 (.m p)) := by
    refine ⟨fast.auxiliary 0 p, ?_⟩
    have band := relax_mem_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) wait.le (fast.rest p)
      (by constructor <;> norm_num : (1 / 40 : ℝ) ∈ Icc (1 / 40 - 1 / 100000) (1 / 40 + 1 / 100000))
    by_cases eq : p = work
    · subst p
      simpa [admitted, setRaw, beforeWork, protectedMainEnd, protectedMainValues, rawInputScale,
        auxPulse_zero_eq_relax, RestBand, start, withFuture] using band
    · simpa [admitted, setRaw, beforeWork, protectedMainEnd, protectedMainValues, eq, RestBand, start, withFuture] using band
  have workOther (q : Port) (ne : q ≠ work) : admitted.raw 0 q = none := by
    simpa [admitted, token, cycleWork, setRaw, beforeWork, protectedMainEnd, start, work,
      withFuture, ne] using fast.raw_none 0 q
  have workGains (q : Port) : admitted.x 0 (.z q) = s.x 0 (.z q) :=
    (fast.gains 0 q).trans (fire.gain_preserved 0 q)
  have frame : CappedWorkFrame θ admitted work :=
    ⟨startB, (workGains 0).trans workGain, fun q ne => ⟨(workSensor q).1, (workSensor q).2, workOther q ne⟩, rfl⟩
  obtain ⟨read⟩ := capped_work_read_exists (high := high) box frame fast.main_slow chargeAtT timing
    (by simp [admitted, token, cycleWork, work, setRaw]) (workSensor work).1 (workSensor work).2
    ((workGains 2).trans readGain)
  let finish := routedFast.append handoff
  have finishSilent : finish.ledger.emissions = [] := by
    rw [Execution.emissions_append, fastLedger, fastSilent]
    rfl
  have finishDelivery : finish.deliveries = [token] := by
    rw [Execution.deliveries_append, fastDeliveryEq, fastDeliveries]
    rfl
  have finishTransverse : finish.ContactsTransversal :=
    (Execution.contactsTransversal_append _ _).2 ⟨routedFastContact, ⟨trivial, trivial⟩⟩
  have transport {a b c d : Snapshot 1} (same : b = c) (jump : Jump route a b)
      (tail : Execution θ route c d) :
      ∃ trace : Execution θ route a d,
        trace.ledger.emissions = jump.ledger.emissions ++ tail.ledger.emissions ∧
        trace.deliveries = jump.deliveries ++ tail.deliveries ∧
        (trace.ContactsTransversal ↔ jump.ContactTransversal θ ∧ tail.ContactsTransversal) := by
    cases same
    exact ⟨.cons (.jump jump) tail, rfl, rfl, Iff.rfl⟩
  obtain ⟨routedWork, workLedger, workDelivery, workContacts⟩ := transport fireEndpoint fireJump finish
  let lead := routedPrior.append routedWork
  have leadEmission : lead.ledger.emissions = [(0,F)] := by
    rw [Execution.emissions_append, priorLedger, priorSilent, workLedger, fireEmission, finishSilent]
    rfl
  have leadTransverse : lead.ContactsTransversal :=
    (Execution.contactsTransversal_append _ _).2
      ⟨priorContact.mpr priorTransverse, workContacts.mpr ⟨fireContact, finishTransverse⟩⟩
  have leadDelivery : lead.deliveries = [token] := by
    rw [Execution.deliveries_append, priorDeliveryEq, priorDeliveries, workDelivery, finishDelivery]
    rfl
  have tokenEq : cappedWorkReadToken admitted = readToken := rfl
  have afterWindow : ¬ readToken.due + read.read.latency < s.time + 1 := by
    have latency := read.read.window
    cases high <;> simp at latency <;>
      (change ¬ F + delay F + 7 / 5 + read.read.latency < s.time + 1; linarith [latency.1, fireWindow.1])
  have readFires : read.execution.ledger.emissions = [(0, readToken.due + read.read.latency)] :=
    read.only_fire
  obtain ⟨tail, tailFires, _, tailContacts⟩ := read.execution.retarget_router_transversal route
    (by simp [readFires, route, cappedCycleRouter, not_lt.mp afterWindow])
  have tailComplete : CompleteThrough tail read.read.horizon := by
    exact ⟨read.read.complete.1, no_jump_retarget_router read.read.complete.2.1 route, read.read.complete.2.2⟩
  have tailPositive : tail.ContactsTransversal := tailContacts.mpr
    ((Execution.contactsTransversal_append _ _).2 ⟨read.transverse, read.read.transversal⟩)
  refine ⟨⟨F, admitted, rfl, lead, leadEmission, leadDelivery, fireWindow, fire.response_root, read,
    read.admission.trans (congrArg Delivery.due tokenEq), tail, tailComplete,
    (Execution.contactsTransversal_append _ _).2 ⟨leadTransverse, tailPositive⟩,
    (congrArg Ledger.emissions tailFires).trans readFires, fun q => (read.preserves_gains q).trans (workGains q), ?_⟩⟩
  exact teacher_recovery_stays_at_cap (lead.append tail) box 0 recovery

noncomputable def CappedTeacherCycle.execution {θ s delay high}
    (run : CappedTeacherCycle θ s delay high) :
    Execution θ (cappedCycleRouter s.time delay) s run.read.read.final :=
  run.lead.append run.continuation

theorem CappedTeacherCycle.emissions {θ s delay high} (run : CappedTeacherCycle θ s delay high) :
    run.execution.ledger.emissions =
      [(0, run.ignition), (0, (cycleRead delay run.ignition).due + run.read.read.latency)] := by
  rw [execution, Execution.emissions_append, run.leadFires, run.fires]
  rfl

theorem CappedTeacherCycle.crossing_exists {θ ε s delay high} (run : CappedTeacherCycle θ s delay high)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s) (initial : InitiallyBelowReady s) :
    ∃ crossing : CrossingExecution θ (cappedCycleRouter s.time delay) s run.read.read.final,
      crossing.execution = run.execution.toWeak ∧ CrossingCompleteThrough crossing run.read.read.horizon :=
  ⟨run.execution.toCrossing initial box physical run.transverse, rfl,
    run.complete.toCrossing run.execution initial box physical run.transverse⟩

theorem CappedTeacherCycle.every_complete {θ ε s delay high final} (run : CappedTeacherCycle θ s delay high)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s)
    (e : Execution θ (cappedCycleRouter s.time delay) s final)
    (complete : CompleteThrough e run.read.read.horizon) :
    final.ObservationalEq run.read.read.final ∧
      e.emissionTimes 0 = [run.ignition, (cycleRead delay run.ignition).due + run.read.read.latency] := by
  refine ⟨(e.observational_unique run.execution box physical complete run.complete).1, ?_⟩
  rw [e.emissionTimes_unique run.execution box physical complete run.complete]
  simp [Execution.emissionTimes, run.emissions]

theorem CappedTeacherCycle.every_crossing_complete {θ ε s delay high final σ}
    (run : CappedTeacherCycle θ s delay high)
    (box : PhysicalBox θ ε) (physical : PhysicalInvariant θ s) (initial : InitiallyBelowReady s)
    (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : ∀ fire, delay fire ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ))
    (crossing : CrossingExecution θ (cappedCycleRouter s.time delay) s final)
    (complete : CrossingCompleteThrough crossing run.read.read.horizon) :
    final.ObservationalEq run.read.read.final ∧ crossing.execution.emissionTimes 0 =
      [run.ignition, (cycleRead delay run.ignition).due + run.read.read.latency] := by
  obtain ⟨native, same⟩ := crossing.execution.toNative_of_transverse_completion run.execution
    (capped_cycle_router_causal budget wire) box physical run.complete run.transverse (le_of_eq complete.1)
  have weak := complete.toWeak_of_native crossing native same initial box physical
  refine ⟨(run.execution.observational_unique_weak box crossing.execution physical
    run.complete run.transverse weak).1.symm, ?_⟩
  rw [← run.execution.emissionTimes_unique_weak crossing.execution box physical
    run.complete run.transverse weak]
  simp [Execution.emissionTimes, run.emissions]

end RecursiveLearning.Native
