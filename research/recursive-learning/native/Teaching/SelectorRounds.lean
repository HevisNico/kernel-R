import Teaching.SelectorRound

/-! Any prescribed finite number of native rounds, under one fixed periodic
router and with the entire ignition calendar present at the initial state.
List order is operational presentation; no token is inserted between rounds. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- Reverse chronological presentation matches `withFuture`, which prepends
future sources. The delivery semantics does not require a sorted queue. -/
noncomputable def roundInputs (origin : ℝ) : ℕ → ℕ → List (Delivery 1)
  | _, 0 => []
  | k, n + 1 => roundInputs origin (k + 1) n ++ [roundIgnition origin k]

theorem round_inputs_length (origin : ℝ) (k n : ℕ) :
    (roundInputs origin k n).length = n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [roundInputs, ih]

/-- Every source date is fixed by its integer round number before execution. -/
theorem round_inputs_member {origin k n d} : d ∈ roundInputs origin k n ↔
    ∃ j, k ≤ j ∧ j < k + n ∧ d = roundIgnition origin j := by
  induction n generalizing k with
  | zero => simp [roundInputs]; omega
  | succ n ih =>
    simp only [roundInputs, List.mem_append, List.mem_singleton, ih]
    constructor
    · rintro (⟨j, lo, hi, same⟩ | same)
      · exact ⟨j, by omega, by omega, same⟩
      · exact ⟨k, le_rfl, by omega, same⟩
    · rintro ⟨j, lo, hi, same⟩
      by_cases equal : j = k
      · right; simpa [equal] using same
      · left; exact ⟨j, by omega, by omega, same⟩

theorem round_inputs_after {origin k n} {d : Delivery 1}
    (member : d ∈ roundInputs origin k n) : roundDate origin k < d.due := by
  obtain ⟨j, lo, _, rfl⟩ := round_inputs_member.mp member
  have lower : (k : ℝ) ≤ j := by exact_mod_cast lo
  dsimp [roundIgnition, reprepareIgnition, roundDate]
  linarith

/-- Actual recurrent boundary with its remaining prescribed input calendar.
Queue order is presentation only; multiplicities and dates must agree.
Erasing pending tokens here is only a resource predicate's projection:
the constructed executions retain and account for the full actual queue. -/
structure ScheduledRoundReady (θ : Fin 1 → Parameters) (origin : ℝ) (k n : ℕ)
    (s : Snapshot 1) (high : Bool) : Prop where
  resources : RoundReady θ {s with pending := []} high
  date : s.time = roundDate origin k
  pending : s.pending.Perm (roundInputs origin k n)

theorem RoundReady.withFuture_scheduled {θ origin k n s high} (ready : RoundReady θ s high)
    (date : s.time = roundDate origin k) :
    ScheduledRoundReady θ origin k n (withFuture s (roundInputs origin k n)) high := by
  have cleared : {withFuture s (roundInputs origin k n) with pending := []} = s := by
    change {s with pending := []} = s
    rw [← ready.quiet.empty]
  refine ⟨by simpa only [cleared] using ready, date, ?_⟩
  change (roundInputs origin k n ++ s.pending).Perm (roundInputs origin k n)
  simp [ready.quiet.empty]

theorem RoundReady.of_observational {θ s u high} (ready : RoundReady θ s high)
    (same : s.ObservationalEq u) : RoundReady θ u high := by
  have empty : u.pending = [] := List.perm_nil.mp (by simpa [ready.quiet.empty] using same.pending.symm)
  refine ⟨same.physical_invariant ready.physical, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [← same.main]; exact ready.ready.ready
    · rw [← same.values]; exact ready.ready.charge
    · intro p
      rw [← same.aux, ← same.values]
      exact ready.ready.auxiliary p
  · refine ⟨?_, ?_, empty⟩
    · intro p
      rw [← same.aux, ← same.values]
      exact ready.quiet.auxiliary p
    · intro p; rw [← same.raw]; exact ready.quiet.raw p
  · rw [← same.values]; exact ready.recovery
  · rw [← same.values]; exact ready.ignition
  · rw [← same.values]; exact ready.work
  · rw [← same.values]; exact ready.selector

theorem ScheduledRoundReady.of_observational {θ origin k n s u high}
    (ready : ScheduledRoundReady θ origin k n s high) (same : s.ObservationalEq u) :
    ScheduledRoundReady θ origin k n u high := by
  have cleared : Snapshot.ObservationalEq {s with pending := []} {u with pending := []} :=
    ⟨same.time, same.values, same.main, same.aux, same.raw, .refl _⟩
  exact ⟨ready.resources.of_observational cleared, same.time.symm.trans ready.date,
    same.pending.symm.trans ready.pending⟩

/-- A scheduled quiet boundary is saturated through its fixed date even
though its queue still contains the future rounds' ignition tokens. -/
theorem ScheduledRoundReady.complete {θ origin k n s high route source}
    (ready : ScheduledRoundReady θ origin k n s high) (e : Execution θ route source s) :
    CompleteThrough e (roundDate origin k) := by
  have future : ∀ d ∈ s.pending, s.time < d.due := by
    intro d member
    rw [ready.date]
    exact round_inputs_after (ready.pending.mem_iff.mp member)
  refine ⟨ready.date, ?_, ?_⟩
  · exact ready_no_jump s
      (fun i => by rw [Subsingleton.elim i 0]; exact ready.resources.ready.ready)
      (fun i p => by rw [Subsingleton.elim i 0]; exact (ready.resources.quiet.auxiliary p).1)
      (fun i p => by rw [Subsingleton.elim i 0]; exact ready.resources.quiet.raw p)
      (fun i => by rw [Subsingleton.elim i 0]; linarith [ready.resources.ready.charge.2])
      (fun i p => by rw [Subsingleton.elim i 0]; linarith [(ready.resources.quiet.auxiliary p).2.2])
      future
  · simpa [ready.date] using future

theorem rounds_future_transverse {n θ route s u} (e : @Execution n θ route s u)
    (future : List (Delivery n)) (later : ∀ d ∈ future, u.time ≤ d.due)
    (positive : e.ContactsTransversal) : (e.withFuture future later).ContactsTransversal := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow f => exact ih later positive
    | jump j => exact ⟨(j.contactTransversal_requeue (j.withFuture future)).1 positive.1,
        ih later positive.2⟩

private theorem rounds_jump_future_deliveries {n route s u} (j : @Jump n route s u)
    (future : List (Delivery n)) : (j.withFuture future).deliveries = j.deliveries := by
  have one {a b : Snapshot n} (step : Jump route a b) (d : Delivery n) :
      (step.withOneFuture d).deliveries = step.deliveries := by cases step <;> rfl
  induction future with
  | nil => rfl
  | cons d ds ih => exact (one _ d).trans ih

theorem rounds_future_deliveries {n θ route s u} (e : @Execution n θ route s u)
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
      rw [rounds_jump_future_deliveries, ih later]

private theorem rounds_cast_transverse {n θ route s v u} (e : @Execution n θ route s u)
    (same : v = s) (positive : e.ContactsTransversal) :
    (e.cast_source same).ContactsTransversal := by
  cases same
  exact positive

/-- A physical round carrying the rest of the already present calendar. -/
structure CarriedCalendarRound {θ origin delay k s high}
    (run : CalendarRound θ origin delay k s high) (n : ℕ) where
  execution : Execution θ (roundRouter origin delay)
    (withFuture s (roundInputs origin k (n + 1)))
    (withFuture run.final (roundInputs origin (k + 1) n))
  initial : ScheduledRoundReady θ origin k (n + 1)
    (withFuture s (roundInputs origin k (n + 1))) high
  finalReady : ScheduledRoundReady θ origin (k + 1) n
    (withFuture run.final (roundInputs origin (k + 1) n)) high
  transverse : execution.ContactsTransversal
  complete : CompleteThrough execution (roundDate origin (k + 1))
  emissions : execution.ledger.emissions = [(0, run.ignition), (0, run.readFire)]
  cost : execution.deliveries.length = 3

/-- This is an actual lifted execution from the original source queue to
the remaining queue, not insertion of a source at the intermediate boundary. -/
theorem CalendarRound.carry_future {θ origin delay k s high}
    (run : CalendarRound θ origin delay k s high) (ready : RoundReady θ s high)
    (date : s.time = roundDate origin k) (n : ℕ) : Nonempty (CarriedCalendarRound run n) := by
  let future := roundInputs origin (k + 1) n
  have later : ∀ d ∈ future, run.final.time ≤ d.due := by
    intro d member
    rw [run.date]
    exact (round_inputs_after member).le
  let framed := run.execution.withFuture future later
  have source : withFuture s (roundInputs origin k (n + 1)) =
      withFuture (withFuture s [roundIgnition origin k]) future := by
    simp [roundInputs, withFuture, future, List.append_assoc]
  let e := framed.cast_source source
  have finalReady := run.ready.withFuture_scheduled (n := n) run.date
  exact ⟨{
    execution := e, initial := ready.withFuture_scheduled date, finalReady := finalReady
    transverse := rounds_cast_transverse framed source
      (rounds_future_transverse run.execution future later run.transverse)
    complete := finalReady.complete e
    emissions := by simp only [e, framed, Execution.cast_source_ledger,
      Execution.withFuture_ledger, run.emissions]
    cost := by simp only [e, framed, Execution.cast_source_deliveries,
      rounds_future_deliveries, run.cost] }⟩

/-- Every complete competitor at an actual intermediate boundary retains
the resources and exactly the remaining calendar, up to queue presentation. -/
theorem CarriedCalendarRound.every_complete {θ ε origin delay k s high n final}
    {run : CalendarRound θ origin delay k s high} (carried : CarriedCalendarRound run n)
    (box : @PhysicalBox 1 θ ε) (physical : PhysicalInvariant θ s)
    (candidate : Execution θ (roundRouter origin delay)
      (withFuture s (roundInputs origin k (n + 1))) final)
    (done : CompleteThrough candidate (roundDate origin (k + 1))) :
    ScheduledRoundReady θ origin (k + 1) n final high ∧
      final.ObservationalEq (withFuture run.final (roundInputs origin (k + 1) n)) ∧
      candidate.emissionTimes 0 = [run.ignition, run.readFire] ∧
      candidate.deliveries.Perm carried.execution.deliveries ∧ candidate.deliveries.length = 3 := by
  have initial : PhysicalInvariant θ (withFuture s (roundInputs origin k (n + 1))) :=
    ⟨physical.region, physical.gain_cap, physical.recovery_cap, physical.reserve⟩
  obtain ⟨state, fires, inputs, cost⟩ :=
    complete_round_behavior carried.execution candidate box initial carried.complete done
  refine ⟨carried.finalReady.of_observational state.symm, state, ?_, inputs, cost.trans carried.cost⟩
  simpa [Execution.emissionTimes, carried.emissions] using fires 0

structure CalendarRounds (θ : Fin 1 → Parameters) (origin : ℝ) (delay : ℝ → ℝ)
    (k n : ℕ) (s : Snapshot 1) (high : Bool) where
  final : Snapshot 1
  execution : Execution θ (roundRouter origin delay) (withFuture s (roundInputs origin k n)) final
  date : final.time = roundDate origin (k + n)
  ready : RoundReady θ final high
  transverse : execution.ContactsTransversal
  complete : CompleteThrough execution (roundDate origin (k + n))
  cost : execution.deliveries.length = 3 * n
  fireCount : execution.ledger.emissions.length = 2 * n
  gains : ∀ p, final.x 0 (.z p) = s.x 0 (.z p)
  recovery : final.x 0 .b = s.x 0 .b

/-- The induction threads the actual final state into the next construction.
Future source tokens are carried through the whole preceding execution. -/
theorem calendar_rounds_of_step {θ origin delay high}
    (step : ∀ (k : ℕ) (s : Snapshot 1), RoundReady θ s high →
      s.time = roundDate origin k → Nonempty (CalendarRound θ origin delay k s high))
    (n : ℕ) {k s} (ready : RoundReady θ s high) (date : s.time = roundDate origin k) :
    Nonempty (CalendarRounds θ origin delay k n s high) := by
  induction n generalizing k s with
  | zero =>
    let e : Execution θ (roundRouter origin delay) (withFuture s (roundInputs origin k 0)) s := .nil s
    exact ⟨{
      final := s, execution := e, date := by simpa using date, ready := ready
      transverse := by trivial, complete := by simpa [date] using ready.complete e
      cost := rfl, fireCount := rfl, gains := fun _ => rfl, recovery := rfl }⟩
  | succ n ih =>
    obtain ⟨head⟩ := step k s ready date
    obtain ⟨tail⟩ := ih head.ready head.date
    obtain ⟨carried⟩ := head.carry_future ready date n
    let e := carried.execution.append tail.execution
    have indices : (k + 1) + n = k + (n + 1) := by omega
    refine ⟨{
      final := tail.final, execution := e
      date := by simpa [indices] using tail.date
      ready := tail.ready
      transverse := (Execution.contactsTransversal_append _ _).2
        ⟨carried.transverse, tail.transverse⟩
      complete := by simpa only [CompleteThrough, indices] using tail.complete
      cost := ?_, fireCount := ?_
      gains := fun p => (tail.gains p).trans (head.gains p)
      recovery := tail.recovery.trans head.recovery }⟩
    · dsimp only [e]
      rw [Execution.deliveries_append]
      simp only [List.length_append, carried.cost, tail.cost]
      omega
    · dsimp only [e]
      rw [Execution.emissions_append]
      simp only [List.length_append, carried.emissions, List.length_cons, List.length_nil, tail.fireCount]
      omega

/-- For every finite count and every supplied admissible delay function,
the same periodic router executes all rounds from the fixed initial calendar. -/
theorem calendar_rounds_exists {θ ε origin delay k s high σ} (box : @PhysicalBox 1 θ ε)
    (ready : RoundReady θ s high) (date : s.time = roundDate origin k)
    (nonnegative : 0 ≤ σ) (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : ∀ fire, delay fire ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ))
    (n : ℕ) : Nonempty (CalendarRounds θ origin delay k n s high) :=
  calendar_rounds_of_step (fun _ _ ready date =>
    calendar_round_exists box ready date nonnegative budget wire) n ready date

/-- Empty terminal queues upgrade observational uniqueness to literal state
equality. Every complete competing execution has the same actual input cost. -/
theorem CalendarRounds.every_complete {θ ε origin delay k n s high final}
    (run : CalendarRounds θ origin delay k n s high) (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s)
    (candidate : Execution θ (roundRouter origin delay) (withFuture s (roundInputs origin k n)) final)
    (done : CompleteThrough candidate (roundDate origin (k + n))) :
    final = run.final ∧ RoundReady θ final high ∧
      candidate.emissionTimes 0 = run.execution.emissionTimes 0 ∧
      candidate.deliveries.Perm run.execution.deliveries ∧
      candidate.deliveries.length = 3 * n ∧ candidate.ledger.emissions.length = 2 * n := by
  have initial : PhysicalInvariant θ (withFuture s (roundInputs origin k n)) :=
    ⟨physical.region, physical.gain_cap, physical.recovery_cap, physical.reserve⟩
  obtain ⟨state, fires, inputs, cost⟩ :=
    complete_round_behavior run.execution candidate box initial run.complete done
  have equal := snapshot_eq_of_observational_empty state run.ready.quiet.empty
  have ledger := (candidate.observational_unique run.execution box initial done run.complete).2
  exact ⟨equal, equal ▸ run.ready, fires 0, inputs, cost.trans run.cost,
    ledger.length_eq.trans run.fireCount⟩

/-- The single-round contract holds for every complete native execution,
including the actual ignition/read FIRE dates and all three input deliveries. -/
theorem CalendarRound.every_complete {θ ε origin delay k s high final}
    (run : CalendarRound θ origin delay k s high) (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s)
    (candidate : Execution θ (roundRouter origin delay) (withFuture s [roundIgnition origin k]) final)
    (done : CompleteThrough candidate (roundDate origin (k + 1))) :
    final = run.final ∧ RoundReady θ final high ∧
      candidate.emissionTimes 0 = [run.ignition, run.readFire] ∧
      candidate.deliveries.Perm run.execution.deliveries ∧ candidate.deliveries.length = 3 := by
  have initial : PhysicalInvariant θ (withFuture s [roundIgnition origin k]) :=
    ⟨physical.region, physical.gain_cap, physical.recovery_cap, physical.reserve⟩
  obtain ⟨state, fires, inputs, cost⟩ :=
    complete_round_behavior run.execution candidate box initial run.complete done
  have equal := snapshot_eq_of_observational_empty state run.ready.quiet.empty
  refine ⟨equal, equal ▸ run.ready, ?_, inputs, cost.trans run.cost⟩
  simpa [Execution.emissionTimes, run.emissions] using fires 0

theorem RoundReady.initially_below_ready {θ s high} (ready : RoundReady θ s high) :
    InitiallyBelowReady s := by
  intro i c active
  rw [Subsingleton.elim i 0]
  cases c with
  | q => linarith [ready.ready.charge.2]
  | m p => linarith [(ready.quiet.auxiliary p).2.2]
  | z _ => exact False.elim active
  | b => exact False.elim active
  | energy => exact False.elim active

/-- The finite recurrence is a complete geometric-crossing witness, not
only a threshold-contact trace. Future sources preserve the initial bounds. -/
theorem CalendarRounds.crossing_exists {θ ε origin delay k n s high}
    (run : CalendarRounds θ origin delay k n s high) (box : @PhysicalBox 1 θ ε)
    (ready : RoundReady θ s high) :
    ∃ crossing : CrossingExecution θ (roundRouter origin delay)
        (withFuture s (roundInputs origin k n)) run.final,
      crossing.execution = run.execution.toWeak ∧
        CrossingCompleteThrough crossing (roundDate origin (k + n)) := by
  have initial : InitiallyBelowReady (withFuture s (roundInputs origin k n)) :=
    ready.initially_below_ready
  have physical : PhysicalInvariant θ (withFuture s (roundInputs origin k n)) :=
    ⟨ready.physical.region, ready.physical.gain_cap, ready.physical.recovery_cap, ready.physical.reserve⟩
  exact ⟨run.execution.toCrossing initial box physical run.transverse, rfl,
    run.complete.toCrossing run.execution initial box physical run.transverse⟩

/-- Complete geometric competitors also preserve the recurrent boundary
and exact cost. No trace or contact certificate is required from them. -/
theorem CalendarRounds.every_crossing_complete {θ ε origin delay k n s high final}
    (run : CalendarRounds θ origin delay k n s high) (box : @PhysicalBox 1 θ ε)
    (ready : RoundReady θ s high) (causal : StrictCausalRouter (roundRouter origin delay))
    (candidate : CrossingExecution θ (roundRouter origin delay)
      (withFuture s (roundInputs origin k n)) final)
    (done : CrossingCompleteThrough candidate (roundDate origin (k + n))) :
    ∃ native : Execution θ (roundRouter origin delay) (withFuture s (roundInputs origin k n)) final,
      native.toWeak = candidate.execution ∧ final = run.final ∧ RoundReady θ final high ∧
      candidate.execution.emissionTimes 0 = run.execution.emissionTimes 0 ∧
      native.deliveries.Perm run.execution.deliveries ∧ native.deliveries.length = 3 * n := by
  have initial : InitiallyBelowReady (withFuture s (roundInputs origin k n)) :=
    ready.initially_below_ready
  have physical : PhysicalInvariant θ (withFuture s (roundInputs origin k n)) :=
    ⟨ready.physical.region, ready.physical.gain_cap, ready.physical.recovery_cap, ready.physical.reserve⟩
  obtain ⟨native, same, state, fires, inputs, cost⟩ :=
    complete_round_crossing_behavior run.execution candidate box physical initial causal
      run.complete run.transverse done
  have equal := snapshot_eq_of_observational_empty state run.ready.quiet.empty
  exact ⟨native, same, equal, equal ▸ run.ready, fires 0, inputs, cost.trans run.cost⟩

end RecursiveLearning.Native
