import Teaching.SelectorRounds

/-! The first selector read precedes the fixed recurrent calendar. Its
return is padded to a date chosen before any trajectory is constructed. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

structure CalendarBootstrap (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (delay : ℝ → ℝ) (high : Bool) where
  final : Snapshot 1
  execution : Execution θ (roundRouter (s.time + 32) delay) s final
  date : final.time = s.time + 32
  ready : RoundReady θ final high
  transverse : execution.ContactsTransversal
  complete : CompleteThrough execution (s.time + 32)
  readFire : ℝ
  emissions : execution.ledger.emissions = [(0, readFire)]
  deliveries : execution.deliveries = []
  gains : ∀ p, final.x 0 (.z p) = s.x 0 (.z p)
  recovery : final.x 0 .b = s.x 0 .b

theorem calendar_bootstrap_exists {θ ε s delay high} (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s) (prepared : SelectorReadPrepared s high)
    (recovery : s.x 0 .b = 11 / 10)
    (ignition : 9 / 5 ≤ Real.exp (s.x 0 (.z 1)) ∧ Real.exp (s.x 0 (.z 1)) ≤ 11 / 5)
    (work : s.x 0 (.z 0) = Real.log ((θ 0).cap 0)) :
    Nonempty (CalendarBootstrap θ s delay high) := by
  obtain ⟨read⟩ := selector_read_return_exists box prepared (by rw [recovery]; norm_num)
  have later : read.tail.final.time < s.time + 32 := by
    linarith [read.capped_time_bound box physical recovery]
  obtain ⟨wait, _, waitPositive, waitSilent, waitDeliveries⟩ := quiet_ready_tail_exists (θ := θ) later
    (fun i => by rw [Subsingleton.elim i 0]; exact read.tail.ready)
    (fun i p => by rw [Subsingleton.elim i 0]; exact read.tail.quiet.raw p) read.tail.quiet.empty
  let route := roundRouter (s.time + 32) delay
  have latencyBound : read.read.latency < 1 := by
    cases high <;> have h := read.read.window.2 <;> linarith
  obtain ⟨head, headLedger, headDeliveries, headContacts⟩ :=
    read.execution.retarget_router_transversal route (by
      intro event member
      rw [read.only_fire] at member
      obtain rfl := List.mem_singleton.mp member
      exact (round_router_before (by linarith)).symm)
  obtain ⟨tail, tailLedger, tailDeliveries, tailContacts⟩ :=
    wait.retarget_router_transversal route (by simp [waitSilent])
  let e := head.append tail
  let final := quietAt read.tail.final (s.time + 32)
  have ready := quietAt_ready_coordinates read.tail.final 0 read.tail.ready later.le
  have ignitionFinal : 9 / 5 ≤ Real.exp (final.x 0 (.z 1)) ∧
      Real.exp (final.x 0 (.z 1)) ≤ 11 / 5 := by
    change 9 / 5 ≤ Real.exp (read.tail.final.x 0 (.z 1)) ∧
      Real.exp (read.tail.final.x 0 (.z 1)) ≤ 11 / 5
    rw [read.gains]
    exact ignition
  have finalReady : RoundReady θ final high :=
    ⟨e.physical_invariant box physical, ready,
      ⟨ready.auxiliary, read.tail.quiet.raw, read.tail.quiet.empty⟩,
      read.recovery.trans recovery, ignitionFinal,
      (read.gains 0).trans work, (read.gains 2).trans prepared.gain⟩
  refine ⟨{
    final := final, execution := e, date := rfl, ready := finalReady
    transverse := (Execution.contactsTransversal_append _ _).2
      ⟨headContacts.mpr read.transverse, tailContacts.mpr waitPositive⟩
    complete := finalReady.complete e
    readFire := s.time + read.read.latency, emissions := ?_, deliveries := ?_
    gains := read.gains, recovery := read.recovery }⟩
  · rw [Execution.emissions_append, headLedger, tailLedger, read.only_fire, waitSilent]
    rfl
  · rw [Execution.deliveries_append, headDeliveries, tailDeliveries, read.no_deliveries, waitDeliveries]
    rfl


structure CalendarProgram (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (delay : ℝ → ℝ) (n : ℕ) (high : Bool) where
  final : Snapshot 1
  execution : Execution θ (roundRouter (s.time + 32) delay)
    (withFuture s (roundInputs (s.time + 32) 0 n)) final
  date : final.time = roundDate (s.time + 32) n
  ready : RoundReady θ final high
  transverse : execution.ContactsTransversal
  complete : CompleteThrough execution (roundDate (s.time + 32) n)
  cost : execution.deliveries.length = 3 * n
  fires : execution.ledger.emissions.length = 2 * n + 1
  gains : ∀ p, final.x 0 (.z p) = s.x 0 (.z p)
  recovery : final.x 0 .b = s.x 0 .b

theorem calendar_program_exists {θ ε s delay high σ} (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s) (prepared : SelectorReadPrepared s high)
    (recovery : s.x 0 .b = 11 / 10)
    (ignition : 9 / 5 ≤ Real.exp (s.x 0 (.z 1)) ∧ Real.exp (s.x 0 (.z 1)) ≤ 11 / 5)
    (work : s.x 0 (.z 0) = Real.log ((θ 0).cap 0))
    (nonnegative : 0 ≤ σ) (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : ∀ fire, delay fire ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ))
    (n : ℕ) : Nonempty (CalendarProgram θ s delay n high) := by
  obtain ⟨boot⟩ := calendar_bootstrap_exists (delay := delay) box physical prepared recovery ignition work
  obtain ⟨rounds⟩ := calendar_rounds_exists box boot.ready
    (show boot.final.time = roundDate (s.time + 32) 0 by simpa [roundDate] using boot.date)
    nonnegative budget wire n
  let future := roundInputs (s.time + 32) 0 n
  have later : ∀ d ∈ future, boot.final.time ≤ d.due := by
    intro d member
    rw [boot.date]
    simpa [roundDate] using (round_inputs_after member).le
  let lead := boot.execution.withFuture future later
  let e := lead.append rounds.execution
  refine ⟨{
    final := rounds.final, execution := e, date := by simpa using rounds.date
    ready := rounds.ready
    transverse := (Execution.contactsTransversal_append _ _).2
      ⟨rounds_future_transverse boot.execution future later boot.transverse, rounds.transverse⟩
    complete := by simpa only [CompleteThrough, Nat.zero_add] using rounds.complete
    cost := ?_, fires := ?_
    gains := fun p => (rounds.gains p).trans (boot.gains p)
    recovery := rounds.recovery.trans boot.recovery }⟩
  · rw [Execution.deliveries_append, rounds_future_deliveries, boot.deliveries]
    exact rounds.cost
  · rw [Execution.emissions_append, Execution.withFuture_ledger, boot.emissions,
      List.length_append, rounds.fireCount]
    simp; omega

def initialReadToken (time : ℝ) : Delivery 1 := ⟨0, 2, time⟩

/-- The actual initial state, before the first read delivery. The complete
finite source calendar is declared here, never inserted during the run. -/
def calendarReadSource (s : Snapshot 1) (future : List (Delivery 1)) : Snapshot 1 :=
  { s with raw := fun _ _ => none, pending := future ++ [initialReadToken s.time] }

private theorem round_cast_target {n θ route s u v} (e : @Execution n θ route s u)
    (same : u = v) : ∃ out : Execution θ route s v,
      out.ledger = e.ledger ∧ out.deliveries = e.deliveries ∧
      (out.ContactsTransversal ↔ e.ContactsTransversal) := by
  cases same
  exact ⟨e, rfl, rfl, Iff.rfl⟩

/-- Even the first read is an actual arrival, charged once. -/
theorem initial_read_admission {θ route s high} (prepared : SelectorReadPrepared s high)
    (future : List (Delivery 1)) :
    ∃ e : Execution θ route (calendarReadSource s future) (withFuture s future),
      e.ledger.emissions = [] ∧ e.deliveries = [initialReadToken s.time] ∧ e.ContactsTransversal := by
  let source := calendarReadSource s future
  let target := { (setRaw source 0 2 (some source.time)) with pending := future ++ [] }
  let jump : Jump route source target := .arrive source (initialReadToken s.time) future [] rfl rfl rfl
  have same : target = withFuture s future := by
    apply snapshot_eq_of_observational_pending
    · refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
      · funext i p
        rw [Subsingleton.elim i 0]
        by_cases equal : p = 2
        · subst p
          simpa [target, source, calendarReadSource, setRaw, withFuture] using prepared.raw.symm
        · simpa [target, source, calendarReadSource, setRaw, withFuture, equal] using
            (prepared.other p equal).symm
      · simp [target, withFuture, prepared.empty]
    · simp [target, withFuture, prepared.empty]
  let original : Execution θ route source target := .cons (.jump jump) (.nil _)
  obtain ⟨e, ledger, deliveries, contacts⟩ := round_cast_target original same
  exact ⟨e, by rw [ledger]; rfl, by rw [deliveries]; rfl, contacts.mpr (by trivial)⟩

structure DeliveredCalendarProgram (θ : Fin 1 → Parameters) (s : Snapshot 1)
    (delay : ℝ → ℝ) (n : ℕ) (high : Bool) where
  final : Snapshot 1
  execution : Execution θ (roundRouter (s.time + 32) delay)
    (calendarReadSource s (roundInputs (s.time + 32) 0 n)) final
  date : final.time = roundDate (s.time + 32) n
  ready : RoundReady θ final high
  transverse : execution.ContactsTransversal
  complete : CompleteThrough execution (roundDate (s.time + 32) n)
  cost : execution.deliveries.length = 3 * n + 1
  fires : execution.ledger.emissions.length = 2 * n + 1
  gains : ∀ p, final.x 0 (.z p) = s.x 0 (.z p)
  recovery : final.x 0 .b = s.x 0 .b

theorem delivered_calendar_program_exists {θ ε s delay high σ} (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s) (prepared : SelectorReadPrepared s high)
    (recovery : s.x 0 .b = 11 / 10)
    (ignition : 9 / 5 ≤ Real.exp (s.x 0 (.z 1)) ∧ Real.exp (s.x 0 (.z 1)) ≤ 11 / 5)
    (work : s.x 0 (.z 0) = Real.log ((θ 0).cap 0))
    (nonnegative : 0 ≤ σ) (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : ∀ fire, delay fire ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ))
    (n : ℕ) : Nonempty (DeliveredCalendarProgram θ s delay n high) := by
  obtain ⟨run⟩ := calendar_program_exists box physical prepared recovery ignition work
    nonnegative budget wire n
  obtain ⟨arrival, silent, delivered, positive⟩ := initial_read_admission (θ := θ)
    (route := roundRouter (s.time + 32) delay) prepared (roundInputs (s.time + 32) 0 n)
  let e := arrival.append run.execution
  refine ⟨{
    final := run.final, execution := e, date := run.date, ready := run.ready
    transverse := (Execution.contactsTransversal_append _ _).2 ⟨positive, run.transverse⟩
    complete := run.complete
    cost := ?_, fires := ?_, gains := run.gains, recovery := run.recovery }⟩
  · rw [Execution.deliveries_append, delivered, List.length_append, run.cost]
    simp; omega
  · rw [Execution.emissions_append, silent]
    exact run.fires

/-- Concrete prepared resources instantiate all finite counts and both stored
values. This does not claim to manufacture those resources from birth. -/
theorem prepared_delivered_calendar_program_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (high : Bool) (time : ℝ) (n : ℕ) :
    Nonempty (DeliveredCalendarProgram θ (reprepareReadStart θ high time)
      (fun _ => cappedTeacherWorkOffset) n high) := by
  apply delivered_calendar_program_exists (σ := 0) box (reprepareReadStart.physical box high time)
    (reprepareReadStart.prepared θ high time) rfl
  · norm_num [reprepareReadStart, Real.exp_log]
  · rfl
  · norm_num
  · norm_num [cappedTeacherWorkJitter]
  · intro fire; simp


/-- The initial full programme has no active RAW and the first real delivery
is already included in the universal cost, not supplied as an uncharged event. -/
theorem DeliveredCalendarProgram.every_complete {θ ε s delay n high final}
    (run : DeliveredCalendarProgram θ s delay n high) (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s)
    (candidate : Execution θ (roundRouter (s.time + 32) delay)
      (calendarReadSource s (roundInputs (s.time + 32) 0 n)) final)
    (done : CompleteThrough candidate (roundDate (s.time + 32) n)) :
    final = run.final ∧ RoundReady θ final high ∧
      candidate.emissionTimes 0 = run.execution.emissionTimes 0 ∧
      candidate.deliveries.Perm run.execution.deliveries ∧
      candidate.deliveries.length = 3 * n + 1 ∧ candidate.ledger.emissions.length = 2 * n + 1 := by
  have initial : PhysicalInvariant θ (calendarReadSource s (roundInputs (s.time + 32) 0 n)) :=
    ⟨physical.region, physical.gain_cap, physical.recovery_cap, physical.reserve⟩
  obtain ⟨state, fires, inputs, cost⟩ :=
    complete_round_behavior run.execution candidate box initial run.complete done
  have equal := snapshot_eq_of_observational_empty state run.ready.quiet.empty
  have ledger := (candidate.observational_unique run.execution box initial done run.complete).2
  exact ⟨equal, equal ▸ run.ready, fires 0, inputs, cost.trans run.cost,
    ledger.length_eq.trans run.fires⟩

theorem calendar_read_source_initial {s high future} (prepared : SelectorReadPrepared s high) :
    InitiallyBelowReady (calendarReadSource s future) := by
  intro i c active
  rw [Subsingleton.elim i 0]
  cases c with
  | q => exact lt_of_le_of_lt prepared.charge.2 (by norm_num)
  | m p => exact lt_of_le_of_lt (prepared.auxiliary p).2.2 (by norm_num)
  | z _ => exact False.elim active
  | b => exact False.elim active
  | energy => exact False.elim active

theorem DeliveredCalendarProgram.crossing_exists {θ ε s delay n high}
    (run : DeliveredCalendarProgram θ s delay n high) (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s) (prepared : SelectorReadPrepared s high) :
    ∃ crossing : CrossingExecution θ (roundRouter (s.time + 32) delay)
        (calendarReadSource s (roundInputs (s.time + 32) 0 n)) run.final,
      crossing.execution = run.execution.toWeak ∧
        CrossingCompleteThrough crossing (roundDate (s.time + 32) n) := by
  have initial := calendar_read_source_initial (future := roundInputs (s.time + 32) 0 n) prepared
  have pf : PhysicalInvariant θ (calendarReadSource s (roundInputs (s.time + 32) 0 n)) :=
    ⟨physical.region, physical.gain_cap, physical.recovery_cap, physical.reserve⟩
  exact ⟨run.execution.toCrossing initial box pf run.transverse, rfl,
    run.complete.toCrossing run.execution initial box pf run.transverse⟩

theorem DeliveredCalendarProgram.every_crossing_complete {θ ε s delay n high final}
    (run : DeliveredCalendarProgram θ s delay n high) (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s) (prepared : SelectorReadPrepared s high)
    (causal : StrictCausalRouter (roundRouter (s.time + 32) delay))
    (candidate : CrossingExecution θ (roundRouter (s.time + 32) delay)
      (calendarReadSource s (roundInputs (s.time + 32) 0 n)) final)
    (done : CrossingCompleteThrough candidate (roundDate (s.time + 32) n)) :
    ∃ native : Execution θ (roundRouter (s.time + 32) delay)
        (calendarReadSource s (roundInputs (s.time + 32) 0 n)) final,
      native.toWeak = candidate.execution ∧ final = run.final ∧ RoundReady θ final high ∧
      candidate.execution.emissionTimes 0 = run.execution.emissionTimes 0 ∧
      native.deliveries.Perm run.execution.deliveries ∧ native.deliveries.length = 3 * n + 1 := by
  have initial := calendar_read_source_initial (future := roundInputs (s.time + 32) 0 n) prepared
  have pf : PhysicalInvariant θ (calendarReadSource s (roundInputs (s.time + 32) 0 n)) :=
    ⟨physical.region, physical.gain_cap, physical.recovery_cap, physical.reserve⟩
  obtain ⟨native, same, state, fires, inputs, cost⟩ :=
    complete_round_crossing_behavior run.execution candidate box pf initial causal
      run.complete run.transverse done
  have equal := snapshot_eq_of_observational_empty state run.ready.quiet.empty
  exact ⟨native, same, equal, equal ▸ run.ready, fires 0, inputs, cost.trans run.cost⟩

end RecursiveLearning.Native
