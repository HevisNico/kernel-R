import Teaching.SelectorReturn
import Teaching.TeacherCappedCycle

/-! One finite re-preparation programme, with an explicit initial ignition
source, two routed pulses, and an exact delivery count. This is not an
autonomous multi-round scheduler. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

private theorem cast_source_transverse {n θ route s v u} (e : @Execution n θ route s u)
    (same : v = s) (positive : e.ContactsTransversal) :
    (e.cast_source same).ContactsTransversal := by
  cases same
  exact positive

/-- Restrict the existing ignition router to its declared finite window.
Earlier read FIREs therefore cannot start the next work/read timers. -/
noncomputable def reprepareRouter (origin : ℝ) (delay : ℝ → ℝ) : Router 1 :=
  fun i fire => if origin ≤ fire then cappedCycleRouter origin delay i fire else []

theorem reprepare_router_causal {origin delay σ} (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : ∀ fire, delay fire ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ)) :
    StrictCausalRouter (reprepareRouter origin delay) := by
  intro i fire d member
  unfold reprepareRouter at member
  split at member
  · exact capped_cycle_router_causal budget wire i fire d member
  · simp at member

theorem SelectorReadPrepared.complete_at_admission {θ route source s high}
    (prepared : SelectorReadPrepared s high) (e : Execution θ route source s) :
    CompleteThrough e s.time := by
  refine ⟨rfl, ?_, by simp [prepared.empty]⟩
  intro v
  apply BeforeGuards.no_jump
  · constructor
    · intro i
      rw [Subsingleton.elim i 0, prepared.ready]
      linarith [prepared.charge.2]
    · intro i p
      rw [Subsingleton.elim i 0, (prepared.auxiliary p).1]
      linarith [(prepared.auxiliary p).2.2]
  · intro i p origin raw
    rw [Subsingleton.elim i 0] at raw
    by_cases same : p = 2
    · subst p
      rw [prepared.raw] at raw
      have eq := Option.some.inj raw
      linarith
    · rw [prepared.other p same] at raw
      contradiction
  · simp [prepared.empty]

structure IgnitionPreparation (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (delay : ℝ → ℝ) (high : Bool) where
  final : Snapshot 1
  execution : Execution θ (reprepareRouter s.time delay) s final
  ignition : ℝ
  ignitionWindow : s.time + 3 / 10 < ignition ∧ ignition < s.time + 9 / 10
  prepared : SelectorReadPrepared final high
  transverse : execution.ContactsTransversal
  complete : CompleteThrough execution final.time
  emissions : execution.ledger.emissions = [(0, ignition)]
  deliveries : execution.deliveries = [cycleWork delay ignition, cycleRead delay ignition]
  date : final.time = (cycleRead delay ignition).due
  gains : ∀ p, final.x 0 (.z p) = s.x 0 (.z p)

/-- Extract the actual prefix ending at read admission, not at the later FIRE.
The router transport is justified at every emitted event and changes no queue. -/
theorem CappedTeacherCycle.preparation_exists {θ s delay high}
    (run : CappedTeacherCycle θ s delay high) :
    Nonempty (IgnitionPreparation θ s delay high) := by
  let route := reprepareRouter s.time delay
  obtain ⟨head, headLedger, headDeliveries, headContacts⟩ :=
    run.lead.retarget_router_transversal route (by
      intro event member
      rw [run.leadFires] at member
      obtain rfl := List.mem_singleton.mp member
      simp [route, reprepareRouter, show s.time ≤ run.ignition by linarith [run.ignitionWindow.1]])
  obtain ⟨tail, tailLedger, tailDeliveries, tailContacts⟩ :=
    run.read.lead.retarget_router_transversal route (by simp [run.read.silent])
  have token : cappedWorkReadToken run.work = cycleRead delay run.ignition := by
    simp [cappedWorkReadToken, cycleRead, run.workDate]
  have source : withFuture run.work [cycleRead delay run.ignition] =
      withFuture run.work [cappedWorkReadToken run.work] := by rw [token]
  let tail' := tail.cast_source source
  have tailPositive : tail'.ContactsTransversal :=
    cast_source_transverse tail source (tailContacts.mpr run.read.transverse)
  let e := head.append tail'
  have headPositive : head.ContactsTransversal := headContacts.mpr
    ((Execution.contactsTransversal_append _ _).1 run.transverse).1
  refine ⟨{
    final := run.read.admitted, execution := e, ignition := run.ignition
    ignitionWindow := run.ignitionWindow, prepared := run.read.prepared
    transverse := (Execution.contactsTransversal_append _ _).2 ⟨headPositive, tailPositive⟩
    complete := run.read.prepared.complete_at_admission e
    emissions := ?_, deliveries := ?_, date := run.readDate
    gains := fun p => (run.read.read.gains p).symm.trans (run.gains p) }⟩
  · rw [Execution.emissions_append]
    have first := congrArg Ledger.emissions headLedger
    have second := congrArg Ledger.emissions (tail.cast_source_ledger source)
    rw [first, run.leadFires, second, tailLedger, run.read.silent]
    rfl
  · rw [Execution.deliveries_append, headDeliveries, run.leadDeliveries,
      Execution.cast_source_deliveries, tailDeliveries, run.read.deliveries, token]
    rfl

noncomputable def reprepareIgnition (time : ℝ) : Delivery 1 := ⟨0, 1, time⟩

structure RestPreparation (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (time : ℝ) (delay : ℝ → ℝ) (high : Bool) where
  final : Snapshot 1
  execution : Execution θ (reprepareRouter time delay)
    (withFuture s [reprepareIgnition time]) final
  ignition : ℝ
  ignitionWindow : time + 3 / 10 < ignition ∧ ignition < time + 9 / 10
  prepared : SelectorReadPrepared final high
  transverse : execution.ContactsTransversal
  complete : CompleteThrough execution final.time
  emissions : execution.ledger.emissions = [(0, ignition)]
  deliveries : execution.deliveries =
    [reprepareIgnition time, cycleWork delay ignition, cycleRead delay ignition]
  date : final.time = (cycleRead delay ignition).due
  gains : ∀ p, final.x 0 (.z p) = s.x 0 (.z p)
  recovery : final.x 0 .b = s.x 0 .b
  physical : PhysicalInvariant θ final

/-- Re-prepare a resting cell with one initially queued external ignition
pulse and two pulses routed by its own ignition FIRE. Every delivery is counted. -/
theorem rest_preparation_exists {θ ε s time delay high σ} (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s) (ready : ReadyCoordinates s 0) (quiet : QuietSensors s)
    (later : s.time < time)
    (ignitionGain : 9 / 5 ≤ Real.exp (s.x 0 (.z 1)) ∧ Real.exp (s.x 0 (.z 1)) ≤ 11 / 5)
    (recovery : s.x 0 .b = 11 / 10) (workGain : s.x 0 (.z 0) = Real.log ((θ 0).cap 0))
    (readGain : s.x 0 (.z 2) = selectorReadLogGain high)
    (nonnegative : 0 ≤ σ) (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : ∀ fire, delay fire ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ)) :
    Nonempty (RestPreparation θ s time delay high) := by
  let route := reprepareRouter time delay
  let start := withFuture s [reprepareIgnition time]
  have initialPhysical : PhysicalInvariant θ start :=
    ⟨physical.region, physical.gain_cap, physical.recovery_cap, physical.reserve⟩
  have noRaw (i : Fin 1) (p : Port) : start.raw i p = none := by
    rw [Subsingleton.elim i 0]
    exact quiet.raw p
  have valid : RawValid start := by
    intro i p origin raw
    rw [noRaw] at raw
    contradiction
  obtain ⟨arrival⟩ := quiet_source_arrival_exists (route := route) box start
    (reprepareIgnition time) [] initialPhysical valid
    (fun i => by rw [Subsingleton.elim i 0]; exact ⟨ready.ready, ready.charge, ready.auxiliary⟩) noRaw later
    (by simp [start, withFuture, quiet.empty]) (by simp)
  have arrivalGain (p : Port) : arrival.final.x 0 (.z p) = s.x 0 (.z p) :=
    arrival.gain_preserved 0 p
  have arrivalRecovery : arrival.final.x 0 .b = 11 / 10 :=
    (arrival.recovery_preserved 0).trans recovery
  obtain ⟨cycle⟩ := capped_teacher_cycle_exists box arrival.physical arrival.raw_valid (arrival.ready 0)
    (by rw [arrivalGain]; exact ignitionGain) arrival.raw_active
    (fun p different => arrival.raw_other 0 p (Or.inr different)) arrivalRecovery
    ((arrivalGain 0).trans workGain) ((arrivalGain 2).trans readGain) arrival.pending
    nonnegative budget wire
  obtain ⟨prep⟩ := cycle.preparation_exists
  have routeEq : reprepareRouter arrival.final.time delay = route := by
    rw [arrival.date]; rfl
  obtain ⟨tail, tailLedger, tailDeliveries, tailContacts⟩ :=
    prep.execution.retarget_router_transversal route (by intro event member; rw [routeEq])
  let e := arrival.execution.append tail
  refine ⟨{
    final := prep.final, execution := e, ignition := prep.ignition
    ignitionWindow := ?_, prepared := prep.prepared
    transverse := (Execution.contactsTransversal_append _ _).2
      ⟨arrival.contacts_transversal, tailContacts.mpr prep.transverse⟩
    complete := prep.prepared.complete_at_admission e
    emissions := ?_, deliveries := ?_, date := prep.date
    gains := fun p => (prep.gains p).trans (arrivalGain p)
    recovery := ?_, physical := e.physical_invariant box initialPhysical }⟩
  · simpa [arrival.date, reprepareIgnition] using prep.ignitionWindow
  · rw [Execution.emissions_append, arrival.emissions, tailLedger, prep.emissions]
    rfl
  · rw [Execution.deliveries_append, arrival.deliveries, tailDeliveries, prep.deliveries]
    rfl
  · exact (teacher_recovery_stays_at_cap e box 0 recovery).trans recovery.symm

theorem RestPreparation.pulse_cost {θ s time delay high}
    (run : RestPreparation θ s time delay high) : run.execution.deliveries.length = 3 := by
  rw [run.deliveries]; rfl

structure ReadReprepared (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (delay : ℝ → ℝ) (high : Bool) where
  returned : RestedSelectorRead θ s high
  time : ℝ
  later : returned.tail.final.time < time
  preparation : RestPreparation θ returned.tail.final time delay high
  execution : Execution θ (reprepareRouter time delay)
    (withFuture s [reprepareIgnition time]) preparation.final
  transverse : execution.ContactsTransversal
  complete : CompleteThrough execution preparation.final.time
  emissions : execution.ledger.emissions =
    [(0, s.time + returned.read.latency), (0, preparation.ignition)]
  deliveries : execution.deliveries =
    [reprepareIgnition time, cycleWork delay preparation.ignition, cycleRead delay preparation.ignition]

/-- End-to-end witness: the next ignition token is present in the initial
queue, before the first read. The same finite router governs every fragment.
The scheduling time is an existential programme parameter, not a proved
autonomous timing mechanism. -/
theorem read_reprepared_exists {θ ε s delay high σ} (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s) (prepared : SelectorReadPrepared s high)
    (recovery : s.x 0 .b = 11 / 10)
    (ignitionGain : 9 / 5 ≤ Real.exp (s.x 0 (.z 1)) ∧ Real.exp (s.x 0 (.z 1)) ≤ 11 / 5)
    (workGain : s.x 0 (.z 0) = Real.log ((θ 0).cap 0))
    (nonnegative : 0 ≤ σ) (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : ∀ fire, delay fire ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ)) :
    Nonempty (ReadReprepared θ s delay high) := by
  obtain ⟨returned⟩ := selector_read_return_exists box prepared (by rw [recovery]; norm_num)
  let time := returned.tail.final.time + 1
  let token := reprepareIgnition time
  have later : returned.tail.final.time < time := by dsimp [time]; linarith
  obtain ⟨prep⟩ := rest_preparation_exists box (returned.physical box physical)
    returned.tail.ready returned.tail.quiet later
    (by rw [returned.gains]; exact ignitionGain) (returned.recovery.trans recovery)
    ((returned.gains 0).trans workGain) ((returned.gains 2).trans prepared.gain)
    nonnegative budget wire
  let route := reprepareRouter time delay
  have future : ∀ d ∈ [token], returned.tail.final.time ≤ d.due := by
    intro d member
    obtain rfl := List.mem_singleton.mp member
    exact later.le
  let first := returned.execution.withFuture [token] future
  have firstFires : first.ledger.emissions = [(0, s.time + returned.read.latency)] := by
    rw [Execution.withFuture_ledger, returned.only_fire]
  have readBefore : s.time + returned.read.latency < time := by
    have latency : returned.read.latency < 4 / 5 := by
      cases high
      · exact returned.read.window.2
      · have h := returned.read.window.2; linarith
    have readEnd := returned.read.horizonBounds.1
    have restAfter := returned.tail.later
    rw [returned.read.complete.1] at restAfter
    linarith
  obtain ⟨lead, leadLedger, leadDeliveries, leadContacts⟩ :=
    first.retarget_router_transversal route (by
      intro event member
      rw [firstFires] at member
      obtain rfl := List.mem_singleton.mp member
      simp [route, reprepareRouter, not_le.mpr readBefore])
  have leadPositive : lead.ContactsTransversal := leadContacts.mpr
    (teacher_future_transverse returned.execution token later.le returned.transverse)
  let e := lead.append prep.execution
  refine ⟨{
    returned := returned, time := time, later := later, preparation := prep
    execution := e
    transverse := (Execution.contactsTransversal_append _ _).2 ⟨leadPositive, prep.transverse⟩
    complete := prep.prepared.complete_at_admission e
    emissions := ?_, deliveries := ?_ }⟩
  · rw [Execution.emissions_append, leadLedger, firstFires, prep.emissions]
    rfl
  · rw [Execution.deliveries_append, leadDeliveries, teacher_future_deliveries,
      returned.no_deliveries, prep.deliveries]
    rfl

theorem ReadReprepared.pulse_cost {θ s delay high} (run : ReadReprepared θ s delay high) :
    run.execution.deliveries.length = 3 := by rw [run.deliveries]; rfl

theorem ReadReprepared.gains {θ s delay high} (run : ReadReprepared θ s delay high) (p : Port) :
    run.preparation.final.x 0 (.z p) = s.x 0 (.z p) :=
  (run.preparation.gains p).trans (run.returned.gains p)

theorem ReadReprepared.recovery {θ s delay high} (run : ReadReprepared θ s delay high) :
    run.preparation.final.x 0 .b = s.x 0 .b :=
  run.preparation.recovery.trans run.returned.recovery

/-- The prepared endpoint really supports another complete selector read. -/
theorem ReadReprepared.next_read_exists {θ ε s delay high}
    (run : ReadReprepared θ s delay high) (box : @PhysicalBox 1 θ ε) :
    ∃ (read : SelectorReadRun θ run.preparation.final high)
      (crossing : CrossingExecution θ (fun _ _ => []) run.preparation.final read.final),
      crossing.execution = read.execution.toWeak ∧ CrossingCompleteThrough crossing read.horizon :=
  selector_read_crossing_exists box run.preparation.physical run.preparation.prepared

theorem ReadReprepared.crossing_exists {θ ε s delay high}
    (run : ReadReprepared θ s delay high) (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s) (prepared : SelectorReadPrepared s high) :
    ∃ crossing : CrossingExecution θ (reprepareRouter run.time delay)
        (withFuture s [reprepareIgnition run.time]) run.preparation.final,
      crossing.execution = run.execution.toWeak ∧
        CrossingCompleteThrough crossing run.preparation.final.time := by
  have initial : InitiallyBelowReady (withFuture s [reprepareIgnition run.time]) := by
    intro i c ready
    rw [Subsingleton.elim i 0]
    cases c with
    | q => exact lt_of_le_of_lt prepared.charge.2 (by norm_num)
    | m p => exact lt_of_le_of_lt (prepared.auxiliary p).2.2 (by norm_num)
    | z _ => exact False.elim ready
    | b => exact False.elim ready
    | energy => exact False.elim ready
  have pf : PhysicalInvariant θ (withFuture s [reprepareIgnition run.time]) :=
    ⟨physical.region, physical.gain_cap, physical.recovery_cap, physical.reserve⟩
  exact ⟨run.execution.toCrossing initial box pf run.transverse, rfl,
    run.complete.toCrossing run.execution initial box pf run.transverse⟩

/-- Explicit prepared resources, not a reachability-from-birth theorem. -/
noncomputable def reprepareReadStart (θ : Fin 1 → Parameters) (high : Bool) (time : ℝ) :
    Snapshot 1 where
  time := time
  x := fun i c => match c with
    | .q => 7 / 10
    | .m _ => 1 / 40
    | .z p => if p = 0 then Real.log ((θ i).cap 0)
        else if p = 2 then selectorReadLogGain high else Real.log 2
    | .b => 11 / 10
    | .energy => 100
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun _ p => if p = 2 then some time else none
  pending := []

theorem reprepareReadStart.prepared (θ high time) :
    SelectorReadPrepared (reprepareReadStart θ high time) high := by
  exact ⟨rfl, by norm_num [reprepareReadStart], rfl, by norm_num [reprepareReadStart],
    fun _ => ⟨rfl, by norm_num [reprepareReadStart, RestBand]⟩, rfl,
    fun p other => by simp [reprepareReadStart, other], rfl⟩

theorem reprepareReadStart.physical {θ ε} (box : @PhysicalBox 1 θ ε) (high time) :
    PhysicalInvariant θ (reprepareReadStart θ high time) := by
  refine ⟨fun i => by norm_num [UpperRegion, reprepareReadStart, auxUpper], ?_,
    fun i => by norm_num [reprepareReadStart], fun i => by norm_num [reprepareReadStart]⟩
  intro i p
  have cap : 2 ≤ (θ i).cap p := by
    have lower := (box.2 i p).1.1
    linarith [box.epsilon_bounds.2]
  have logCap := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) cap
  change (if p = 0 then Real.log ((θ i).cap 0)
    else if p = 2 then selectorReadLogGain high else Real.log 2) ≤ _
  split
  · rename_i equal; subst p; exact le_rfl
  · split
    · have logTwo := Real.log_two_gt_d9
      cases high <;> simp [selectorReadLogGain] <;> linarith
    · exact logCap

/-- A non-vacuous family for either selector value, with constant work delay. -/
theorem prepared_read_reprepared_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (high : Bool) (time : ℝ) :
    Nonempty (ReadReprepared θ (reprepareReadStart θ high time)
      (fun _ => cappedTeacherWorkOffset) high) := by
  apply read_reprepared_exists (σ := 0) box (reprepareReadStart.physical box high time)
    (reprepareReadStart.prepared θ high time) rfl
  · norm_num [reprepareReadStart, Real.exp_log]
  · rfl
  · norm_num
  · norm_num [cappedTeacherWorkJitter]
  · intro fire; simp

end RecursiveLearning.Native
