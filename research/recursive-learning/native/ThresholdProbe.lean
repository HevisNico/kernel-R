import ScheduledCommit

/-! A physical count threshold with excess pulses. A pulse delivered
after the gain reaches the read level can fire, but it cannot increase
the learned gain or change the recovery rate. A final read is reported
in a separate window. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid

private noncomputable def thresholdGain (remaining : ℕ) : ℝ :=
  (3 / 5 : ℝ) * (1 - (remaining : ℝ))

private structure ThresholdSlot (θ : Fin 1 → Parameters) (start : Snapshot 1) (due : ℝ)
    (later : List (Delivery 1)) (remaining : ℕ) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) start final
  transverse : execution.ContactsTransversal
  ready : ReadyCoordinates final 0
  rawNone : ∀ p, final.raw 0 p = none
  pending : final.pending = later
  date : final.time ≤ due + 23
  gain : final.x 0 (.z 0) = thresholdGain (remaining - 1)
  recovery : final.x 0 .b = 2 / 25
  deliveries : execution.deliveries = [⟨0, 0, due⟩]
  fires : ∃ fire : Option ℝ, fire.isSome = decide (remaining = 0) ∧
    execution.emissionTimes 0 = fire.toList ∧
    ∀ F, fire = some F → due < F ∧ F < due + 1

private theorem raw_valid_of_rest {s : Snapshot 1} (raw : ∀ p, s.raw 0 p = none) : RawValid s := by
  intro i p t h
  rw [Subsingleton.elim i 0, raw p] at h
  contradiction

private theorem no_deliveries_of_pending_eq {θ s u} (e : @Execution 1 θ (fun _ _ => []) s u)
    (queue : u.pending = s.pending) : e.deliveries = [] := by
  have balance := e.token_balance
  have emptyRoute : e.ledger.emissions.flatMap (fun (_ : Fin 1 × ℝ) => ([] : List (Delivery 1))) = [] := by simp
  change (u.pending : Multiset (Delivery 1)) + (e.deliveries : Multiset (Delivery 1)) =
    (s.pending : Multiset (Delivery 1)) +
      ((e.ledger.emissions.flatMap (fun _ => []) : List (Delivery 1)) : Multiset (Delivery 1)) at balance
  simp only [emptyRoute, queue, Multiset.coe_nil, add_zero] at balance
  have cancelled : (e.deliveries : Multiset (Delivery 1)) = 0 :=
    add_left_cancel (balance.trans (add_zero _).symm)
  exact (Multiset.coe_eq_coe.mp cancelled : e.deliveries.Perm []).eq_nil

private theorem threshold_slot_exists {θ ε start due later remaining}
    (box : @PhysicalBox 1 θ ε) (physical : PhysicalInvariant θ start)
    (ready : ReadyCoordinates start 0) (rawNone : ∀ p, start.raw 0 p = none)
    (before : start.time < due) (queue : start.pending = ⟨0, 0, due⟩ :: later)
    (spacing : ∀ d ∈ later, due + 24 ≤ d.due)
    (gain : start.x 0 (.z 0) = thresholdGain remaining) (recovery : start.x 0 .b = 2 / 25) :
    Nonempty (ThresholdSlot θ start due later remaining) := by
  cases remaining with
  | succ m =>
    have le : start.x 0 (.z 0) ≤ 0 := by rw [gain]; simp [thresholdGain]
    obtain ⟨dose⟩ := port_dose_exists (route := fun _ _ => []) box physical (raw_valid_of_rest rawNone)
      ready rawNone before queue (fun d hd => by linarith [spacing d hd])
      (by
        have h := Real.exp_le_exp.mpr le
        rw [Real.exp_zero] at h
        linarith)
      (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 6 / 5 by norm_num)])
    refine ⟨⟨dose.final, dose.execution, dose.transversal, dose.ready, dose.rawNone,
      dose.pending, ?_, ?_, dose.recovery.trans recovery, dose.deliveries, none, rfl, ?_, by simp⟩⟩
    · rw [dose.complete.1]
      linarith
    · rw [dose.gain, gain]
      simp [thresholdGain]
      ring
    · simp [Execution.emissionTimes, dose.emissions]
  | zero =>
    let token : Delivery 1 := ⟨0, 0, due⟩
    have localReady (i : Fin 1) : ReadyCoordinates start i := by rw [Subsingleton.elim i 0]; exact ready
    have localRaw (i : Fin 1) (p : Port) : start.raw i p = none := by
      rw [Subsingleton.elim i 0]
      exact rawNone p
    obtain ⟨arrival⟩ := quiet_source_arrival_exists (route := fun _ _ => []) box start token later
      physical (raw_valid_of_rest rawNone) localReady localRaw before queue
      (fun d hd => by change due ≤ d.due; linarith [spacing d hd])
    have date : arrival.final.time = due := arrival.date
    have readGain : arrival.final.x 0 (.z 0) = 3 / 5 := by
      rw [arrival.gain_preserved, gain]
      norm_num [thresholdGain]
    have strong : 9 / 5 ≤ Real.exp (arrival.final.x 0 (.z 0)) ∧
        Real.exp (arrival.final.x 0 (.z 0)) ≤ 11 / 5 := by rw [readGain]; exact learnedProbe_gain
    have late : ∀ d ∈ arrival.final.pending, arrival.final.time + 31 / 4 ≤ d.due := by
      rw [arrival.pending, date]
      intro d h
      linarith [spacing d h]
    obtain ⟨fire⟩ := first_mid_learned_fire_exists arrival.final box arrival.physical arrival.raw_valid
      0 0 arrival.ready strong arrival.raw_active arrival.raw_other late
    obtain ⟨fast⟩ := fire.mid_learned_fast_end_exists box (arrival.ready 0) strong.2
      (fun p ne => arrival.raw_other 0 p (Or.inr ne)) late
    let empty := fast.final.requeue []
    have b : empty.x 0 .b = 2 / 25 := by
      change fast.final.x 0 .b = _
      rw [fast.recovery, fire.recovery_preserved, arrival.recovery_preserved, recovery]
    have dispatch : LearnerDispatchState empty :=
      ⟨fast.raw_none, fun p => ⟨fast.auxiliary 0 p, fast.rest p⟩,
        Or.inr ⟨fast.main_slow, by rw [show empty.x 0 .q = 1 / 4 from fast.charge]; norm_num,
          fast.charge.le, b⟩⟩
    have wait : empty.time + 19 < due + 23 := by
      change fast.final.time + 19 < _
      rw [fast.date, fire.date, date]
      linarith [fire.deadline]
    obtain ⟨tail⟩ := learner_wait_exists (θ := θ) (T := due + 23) dispatch rfl wait
    have tailFuture (d : Delivery 1) (hd : d ∈ later) : tail.final.time ≤ d.due := by
      rw [tail.complete.1]
      linarith [spacing d hd]
    have startQueue : fast.final.pending = later := by
      rw [fast.pending, fire.pending, arrival.pending, List.append_nil]
    have startEq : withFuture empty later = fast.final := by
      have eta (s : Snapshot 1) : s.requeue s.pending = s := by cases s; rfl
      change fast.final.requeue (later ++ []) = fast.final
      rw [List.append_nil]
      exact (congrArg fast.final.requeue startQueue.symm).trans (eta fast.final)
    let framed := tail.execution.withFuture later tailFuture
    have framedSilent : framed.ledger.emissions = [] := by rw [Execution.withFuture_ledger, tail.silent]
    have framedPending : (withFuture tail.final later).pending = later := by simp [withFuture, tail.empty]
    have framedDeliveries : framed.deliveries = [] := no_deliveries_of_pending_eq framed
      (framedPending.trans (by simp [empty, withFuture, Snapshot.requeue]))
    obtain ⟨ending, endingPositive, endingSilent, endingDeliveries⟩ :
        ∃ ending : Execution θ (fun _ _ => []) fast.final (withFuture tail.final later),
          ending.ContactsTransversal ∧ ending.ledger.emissions = [] ∧ ending.deliveries = [] := by
      rw [← startEq]
      exact ⟨framed, future_transverse tail.execution later tailFuture tail.transverse,
        framedSilent, framedDeliveries⟩
    let lead := (arrival.execution.append fire.execution).append fast.execution
    let e := lead.append ending
    have emissions : e.ledger.emissions = [(0, fire.final.time)] := by
      change (lead.append ending).ledger.emissions = _
      rw [Execution.emissions_append, endingSilent]
      change (((arrival.execution.append fire.execution).append fast.execution).ledger.emissions ++ []) = _
      rw [Execution.emissions_append, Execution.emissions_append, arrival.emissions,
        fire.emissions, fast.emissions, fire.date]
      rfl
    have finalReady : ReadyCoordinates (withFuture tail.final later) 0 :=
      ⟨(tail.ready 0).ready, (tail.ready 0).charge, (tail.ready 0).auxiliary⟩
    refine ⟨⟨_, e, ?_, finalReady, tail.rawNone 0, framedPending,
      tail.complete.1.le, ?_, (tail.recovery 0).trans b, ?_, some fire.final.time, rfl, ?_, ?_⟩⟩
    · exact (Execution.contactsTransversal_append _ _).2
        ⟨(Execution.contactsTransversal_append _ _).2
          ⟨(Execution.contactsTransversal_append _ _).2 ⟨arrival.contacts_transversal, fire.contacts_transversal⟩,
            fast.contacts_transversal⟩, endingPositive⟩
    · change tail.final.x 0 (.z 0) = _
      rw [tail.gain]
      change fast.final.x 0 (.z 0) = _
      rw [fast.gains, fire.gain_preserved, readGain]
      norm_num [thresholdGain]
    · change (lead.append ending).deliveries = _
      rw [Execution.deliveries_append, endingDeliveries]
      change (((arrival.execution.append fire.execution).append fast.execution).deliveries ++ []) = _
      rw [Execution.deliveries_append, Execution.deliveries_append, arrival.deliveries, fire.deliveries,
        fast.deliveries]
      rfl
    · rw [Execution.emissionTimes, emissions]
      rfl
    · intro F h
      obtain rfl := Option.some.inj h
      rw [fire.date, date]
      constructor <;> linarith [fire.early, fire.deadline]


private theorem threshold_training_exists {θ ε start read remaining dates}
    (box : @PhysicalBox 1 θ ε) (physical : PhysicalInvariant θ start)
    (ready : ReadyCoordinates start 0) (rawNone : ∀ p, start.raw 0 p = none)
    (before : start.time < read) (future : ∀ d ∈ dates, start.time < d)
    (after : ∀ d ∈ dates, d + 24 ≤ read)
    (separated : dates.Pairwise (fun a b => a + 24 ≤ b))
    (queue : start.pending = conjunctionDoseTokens 0 dates ++ [conjunctionProbe read])
    (gain : start.x 0 (.z 0) = thresholdGain remaining) (recovery : start.x 0 .b = 2 / 25) :
    ∃ (final : Snapshot 1) (e : Execution θ (fun _ _ => []) start final),
      e.ContactsTransversal ∧ ReadyCoordinates final 0 ∧ (∀ p, final.raw 0 p = none) ∧
      final.time < read ∧ final.pending = [conjunctionProbe read] ∧
      final.x 0 (.z 0) = thresholdGain (remaining - dates.length) ∧ final.x 0 .b = 2 / 25 ∧
      e.deliveries = conjunctionDoseTokens 0 dates ∧ ∀ F ∈ e.emissionTimes 0, F < read := by
  induction dates generalizing start remaining with
  | nil =>
    exact ⟨start, .nil _, trivial, ready, rawNone, before, queue, by simpa using gain,
      recovery, rfl, by simp [Execution.emissionTimes, Execution.ledger, Ledger.zero]⟩
  | cons d ds ih =>
    obtain ⟨gap, spaced⟩ := List.pairwise_cons.mp separated
    have nextSpacing : ∀ t ∈ conjunctionDoseTokens 0 ds ++ [conjunctionProbe read], d + 24 ≤ t.due := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨date, hd, rfl⟩ := List.mem_map.mp ht
        exact gap date hd
      · obtain rfl := List.mem_singleton.mp ht
        exact after d (by simp)
    obtain ⟨slot⟩ := threshold_slot_exists box physical ready rawNone (future d (by simp))
      queue nextSpacing gain recovery
    obtain ⟨final, tail, positive, hready, hraw, date, pending, hgain, hb, deliveries, silent⟩ :=
      ih (slot.execution.physical_invariant box physical) slot.ready slot.rawNone
        (by linarith [slot.date, after d (by simp)]) (fun t ht => by linarith [slot.date, gap t ht])
        (fun t ht => after t (by simp [ht])) spaced slot.pending slot.gain slot.recovery
    refine ⟨final, slot.execution.append tail,
      (Execution.contactsTransversal_append _ _).2 ⟨slot.transverse, positive⟩,
      hready, hraw, date, pending, ?_, hb, ?_, ?_⟩
    · rw [hgain]
      congr 1
      simp only [List.length_cons]
      omega
    · rw [Execution.deliveries_append, slot.deliveries, deliveries]
      rfl
    · intro F h
      rw [Execution.emissionTimes_append, List.mem_append] at h
      rcases h with head | last
      · obtain ⟨fire, _, emit, window⟩ := slot.fires
        rw [emit] at head
        cases fire with
        | none => simp at head
        | some G =>
          have eq : F = G := by simpa using head
          subst F
          linarith [(window G rfl).2, after d (by simp)]
      · exact silent F last

noncomputable def thresholdProbeStart (time read : ℝ) (need : ℕ) (dates : List ℝ) : Snapshot 1 :=
  (conjunctionCounter time need).requeue (conjunctionDoseTokens 0 dates ++ [conjunctionProbe read])

theorem threshold_probe_physical {θ ε} (box : @PhysicalBox 1 θ ε)
    (time read : ℝ) (need : ℕ) (dates : List ℝ) :
    PhysicalInvariant θ (thresholdProbeStart time read need dates) := by
  have p := conjunction_counter_physical box time need
  exact ⟨p.region, p.gain_cap, p.recovery_cap, p.reserve⟩

theorem threshold_probe_ready (time read : ℝ) (need : ℕ) (dates : List ℝ) :
    ReadyCoordinates (thresholdProbeStart time read need dates) 0 :=
  ⟨rfl, by norm_num [thresholdProbeStart, conjunctionCounter, Snapshot.requeue, preparedTeacher],
    fun _ => ⟨rfl, by norm_num [thresholdProbeStart, conjunctionCounter, Snapshot.requeue,
      preparedTeacher, RestBand]⟩⟩

theorem threshold_probe_initial (time read : ℝ) (need : ℕ) (dates : List ℝ) :
    InitiallyBelowReady (thresholdProbeStart time read need dates) := by
  intro i c h
  cases c with
  | q => change (1 / 10 : ℝ) < 1; norm_num
  | m p => change (1 / 40 : ℝ) < 1; norm_num
  | z _ => exact False.elim h
  | b => exact False.elim h
  | energy => exact False.elim h

/-- With a full recovery interval between pulses, a fixed final read
reports whether the number of training pulses meets the hidden need.
The theorem includes excess pulses, whose earlier FIREs are outside
the report window. -/
theorem native_threshold_probe_exists_until {θ ε} (box : @PhysicalBox 1 θ ε)
    (time read horizon : ℝ) (need : ℕ) (dates : List ℝ)
    (positive : 0 < need) (before : time < read)
    (future : ∀ d ∈ dates, time < d) (after : ∀ d ∈ dates, d + 24 ≤ read)
    (spacing : dates.Pairwise (fun a b => a + 24 ≤ b)) (finish : read + 24 ≤ horizon) :
    Nonempty (ScheduledCell θ (thresholdProbeStart time read need dates) horizon
      (counterWindow read) (decide (need ≤ dates.length)) (fun s => s.pending = [])) := by
  let start := thresholdProbeStart time read need dates
  have phys := threshold_probe_physical box time read need dates
  have ready := threshold_probe_ready time read need dates
  have gain : start.x 0 (.z 0) = thresholdGain need := by
    change -(3 / 5 : ℝ) * ((need - 1 : ℕ) : ℝ) = thresholdGain need
    rw [Nat.cast_sub (by omega : 1 ≤ need), Nat.cast_one]
    unfold thresholdGain
    ring
  obtain ⟨middle, train, positive, ready, raw, early, queue, gain, recovery, delivered, earlier⟩ :=
    threshold_training_exists box phys ready (fun _ => rfl) before future after spacing rfl gain rfl
  obtain ⟨readout⟩ := threshold_slot_exists box (train.physical_invariant box phys) ready raw early queue
    (by simp) gain recovery
  have late : readout.final.time < horizon := by linarith [readout.date]
  obtain ⟨tail, complete, tailPositive, tailSilent, tailDeliveries⟩ :=
    quiet_ready_tail_exists (θ := θ) late
      (fun i => by rw [Subsingleton.elim i 0]; exact readout.ready)
      (fun i p => by rw [Subsingleton.elim i 0]; exact readout.rawNone p) readout.pending
  let e := (train.append readout.execution).append tail
  have empty : (quietAt readout.final horizon).pending = [] := readout.pending
  refine ⟨⟨_, e, complete, (Execution.contactsTransversal_append _ _).2
    ⟨(Execution.contactsTransversal_append _ _).2 ⟨positive, readout.transverse⟩, tailPositive⟩,
    ?_, ?_, empty⟩⟩
  · apply List.Perm.of_eq
    change ((train.append readout.execution).append tail).deliveries = _
    rw [Execution.deliveries_append, Execution.deliveries_append, delivered, readout.deliveries,
      tailDeliveries, List.append_nil]
    rfl
  · obtain ⟨fire, isSome, fireDates, window⟩ := readout.fires
    have none : tail.emissionTimes 0 = [] := by simp [Execution.emissionTimes, tailSilent]
    have silent : (train.emissionTimes 0).filter (counterWindow read).accepts = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro F h
      have early := earlier F h
      simp [ReportWindow.accepts, counterWindow, not_le.mpr early]
    have readDates : fire.toList.filter (counterWindow read).accepts = fire.toList := by
      cases eq : fire with
      | none => rfl
      | some F =>
        have bounds := window F eq
        simp [ReportWindow.accepts, counterWindow, bounds.1.le, bounds.2]
    unfold Reports ReportWindow.dates
    change ((((train.append readout.execution).append tail).emissionTimes 0).filter _).length = _
    rw [Execution.emissionTimes_append, Execution.emissionTimes_append, none, List.append_nil,
      List.filter_append, silent, List.nil_append, fireDates, readDates]
    have flags : fire.isSome = decide (need ≤ dates.length) :=
      isSome.trans (decide_eq_decide.mpr (by omega))
    cases fire <;> simp_all


theorem native_threshold_probe_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (time read : ℝ) (need : ℕ) (dates : List ℝ)
    (positive : 0 < need) (before : time < read)
    (future : ∀ d ∈ dates, time < d) (after : ∀ d ∈ dates, d + 24 ≤ read)
    (spacing : dates.Pairwise (fun a b => a + 24 ≤ b)) :
    Nonempty (ScheduledCell θ (thresholdProbeStart time read need dates) (read + 24)
      (counterWindow read) (decide (need ≤ dates.length)) (fun s => s.pending = [])) :=
  native_threshold_probe_exists_until box time read (read + 24) need dates positive before
    future after spacing le_rfl

/-- The pulse schedule depends on the tested count, independently of
the hidden need encoded in the start gain. -/
noncomputable def thresholdCalendar (time : ℝ) (count : ℕ) : List ℝ :=
  (List.range count).map fun (i : ℕ) => time + 24 * ((i : ℝ) + 1)

noncomputable def thresholdReadTime (time : ℝ) (count : ℕ) : ℝ :=
  time + 24 * ((count : ℝ) + 1)

private theorem threshold_calendar_length (time : ℝ) (count : ℕ) :
    (thresholdCalendar time count).length = count := by simp [thresholdCalendar]

private theorem threshold_calendar_valid (time : ℝ) (count : ℕ) :
    (∀ d ∈ thresholdCalendar time count, time < d ∧ d + 24 ≤ thresholdReadTime time count) ∧
    (thresholdCalendar time count).Pairwise (fun a b => a + 24 ≤ b) := by
  constructor
  · intro d h
    obtain ⟨i, mem, rfl⟩ := List.mem_map.mp h
    have bound : (i : ℝ) + 1 ≤ count := by
      exact_mod_cast Nat.succ_le_of_lt (List.mem_range.mp mem)
    have nonnegative : (0 : ℝ) ≤ i := by positivity
    constructor
    · linarith
    · unfold thresholdReadTime
      linarith
  · apply List.pairwise_map.mpr
    apply List.pairwise_lt_range.imp
    intro i j ij
    have bound : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt ij
    linarith

theorem threshold_count_probe_exists_until {θ ε} (box : @PhysicalBox 1 θ ε)
    (time clock horizon : ℝ) (need count : ℕ) (positive : 0 < need)
    (starts : time ≤ clock) (ends : thresholdReadTime clock count + 24 ≤ horizon) :
    let read := thresholdReadTime clock count
    let start := thresholdProbeStart time read need (thresholdCalendar clock count)
    Nonempty (ScheduledCell θ start horizon (counterWindow read)
      (decide (need ≤ count)) (fun s => s.pending = [])) := by
  have bound : (0 : ℝ) ≤ count := by positivity
  have ⟨valid, spacing⟩ := threshold_calendar_valid clock count
  have before : time < thresholdReadTime clock count := by unfold thresholdReadTime; linarith
  have probe := native_threshold_probe_exists_until box time (thresholdReadTime clock count) horizon need
    (thresholdCalendar clock count) positive before (fun d hd => starts.trans_lt (valid d hd).1)
    (fun d hd => (valid d hd).2) spacing ends
  rwa [threshold_calendar_length] at probe

theorem threshold_count_probe_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (time : ℝ) (need count : ℕ) (positive : 0 < need) :
    let read := thresholdReadTime time count
    let start := thresholdProbeStart time read need (thresholdCalendar time count)
    Nonempty (ScheduledCell θ start (read + 24) (counterWindow read)
      (decide (need ≤ count)) (fun s => s.pending = [])) :=
  threshold_count_probe_exists_until box time time _ need count positive le_rfl le_rfl

/-- For each hidden need, the threshold run exists in upward-crossing
semantics. Every complete crossing run agrees on its physical state,
ordered firing dates and actual deliveries. -/
theorem threshold_count_probe_crossing {θ ε} (box : @PhysicalBox 1 θ ε)
    (time : ℝ) (need count : ℕ) (positive : 0 < need) :
    let read := thresholdReadTime time count
    let start := thresholdProbeStart time read need (thresholdCalendar time count)
    ∃ (run : ScheduledCell θ start (read + 24) (counterWindow read)
        (decide (need ≤ count)) (fun s => s.pending = []))
      (crossing : CrossingExecution θ (fun _ _ => []) start run.final),
      crossing.execution = run.execution.toWeak ∧ CrossingCompleteThrough crossing (read + 24) ∧
      ∀ v (other : CrossingExecution θ (fun _ _ => []) start v), CrossingCompleteThrough other (read + 24) →
        ∃ native : Execution θ (fun _ _ => []) start v, native.toWeak = other.execution ∧
          v.ObservationalEq run.final ∧ native.deliveries.Perm run.execution.deliveries ∧
          ∀ i, other.execution.emissionTimes i = run.execution.emissionTimes i := by
  obtain ⟨run⟩ := threshold_count_probe_exists box time need count positive
  have initial := threshold_probe_initial time (thresholdReadTime time count) need (thresholdCalendar time count)
  have physical := threshold_probe_physical box time (thresholdReadTime time count) need (thresholdCalendar time count)
  have causal : StrictCausalRouter (fun (_ : Fin 1) (_ : ℝ) => []) :=
    fun _ _ _ h => (List.not_mem_nil h).elim
  obtain ⟨crossing, agree, done, every⟩ := complete_crossing_accounting run.execution run.complete
    run.transverse box physical initial causal
  exact ⟨run, crossing, agree, done, every⟩


/-- The entire routed packet is determined by the tested count. -/
noncomputable def thresholdPacket (clock : ℝ) (count : ℕ) : List (Delivery 1) :=
  conjunctionDoseTokens 0 (thresholdCalendar clock count) ++ [conjunctionProbe (thresholdReadTime clock count)]

private theorem threshold_packet_future {clock count d} (mem : d ∈ thresholdPacket clock count) :
    clock < d.due := by
  rcases List.mem_append.mp mem with before | read
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp before
    exact ((threshold_calendar_valid clock count).1 t ht).1
  · obtain rfl := List.mem_singleton.mp read
    change clock < thresholdReadTime clock count
    unfold thresholdReadTime
    linarith [show (0 : ℝ) ≤ count by positivity]

noncomputable def ReportLayout.appendThreshold {n} (layout : ReportLayout n) (source : Fin n)
    (need count : ℕ) : ReportLayout (n + 1) :=
  let clock := layout.last + 1
  let read := thresholdReadTime clock count
  let receiver := (thresholdProbeStart layout.start.time read need (thresholdCalendar clock count)).requeue []
  ⟨queueHead layout.start receiver,
    prependRouted layout.route (forwardReport source (layout.windows source) (thresholdPacket clock count)),
    Fin.cases (counterWindow read) layout.windows, read + 1⟩

theorem ReportLayout.appendThreshold_source_queue {n} (layout : ReportLayout n) (source : Fin n)
    (need count : ℕ) :
    (layout.appendThreshold source need count).start.pending = layout.start.pending.map Delivery.succ := rfl

theorem append_threshold_timed {n} {layout : ReportLayout n} (timed : layout.WellTimed)
    (source : Fin n) (need count : ℕ) : (layout.appendThreshold source need count).WellTimed := by
  have later : layout.last < (layout.appendThreshold source need count).last := by
    change layout.last < layout.last + 1 + 24 * ((count : ℝ) + 1) + 1
    linarith [show (0 : ℝ) ≤ count by positivity]
  refine ⟨timed.1.trans later, ?_⟩
  intro i
  cases i using Fin.cases with
  | zero => exact le_rfl
  | succ i => exact (timed.2 i).trans later.le

private theorem guarded_threshold_exists {θ ε} (box : @PhysicalBox 1 θ ε)
    (time clock horizon : ℝ) (need count : ℕ) (launch : Bool) (positive : 0 < need)
    (starts : time < clock) (ends : thresholdReadTime clock count + 24 ≤ horizon) :
    let read := thresholdReadTime clock count
    let base := thresholdProbeStart time read need (thresholdCalendar clock count)
    let start := base.requeue (if launch then thresholdPacket clock count else [])
    Nonempty (ScheduledCell θ start horizon (counterWindow read)
      (launch && decide (need ≤ count)) (fun s => s.pending = [])) := by
  cases launch with
  | true => exact threshold_count_probe_exists_until box time clock horizon need count positive starts.le ends
  | false =>
    let read := thresholdReadTime clock count
    let s := (thresholdProbeStart time read need (thresholdCalendar clock count)).requeue []
    have before : time < horizon := by
      change clock + 24 * ((count : ℝ) + 1) + 24 ≤ horizon at ends
      linarith [show (0 : ℝ) ≤ count by positivity]
    have ready (i : Fin 1) : ReadyCoordinates s i := by
      rw [Subsingleton.elim i 0]
      have h := threshold_probe_ready time read need (thresholdCalendar clock count)
      exact ⟨h.ready, h.charge, h.auxiliary⟩
    obtain ⟨wait, done, transverse, silent, deliveries⟩ :=
      quiet_ready_tail_exists (θ := θ) (s := s) before ready (fun _ _ => rfl) rfl
    exact ⟨⟨_, wait, done, transverse, by rw [deliveries]; rfl,
      by simp [Reports, ReportWindow.dates, Execution.emissionTimes, silent], rfl⟩⟩

/-- An earlier physical report launches the fixed threshold packet.
Only the final read window is visible to the downstream report wires. -/
theorem append_threshold_run {n θ θH ε T} {layout : ReportLayout n} {bits : Fin n → Bool}
    (prior : CompiledRun θ layout T bits) (box : @PhysicalBox 1 θH ε)
    (source : Fin n) (need count : ℕ) (positive : 0 < need) (timed : layout.WellTimed)
    (horizon : (layout.appendThreshold source need count).last + 75 < T) :
    ∃ run : CompiledRun (prependParameters θH θ) (layout.appendThreshold source need count) T
      (Fin.cases (bits source && decide (need ≤ count)) bits),
      lessonReceipts run.execution.deliveries 0 = (if bits source then count + 1 else 0) ∧
      (∀ i, run.final.x i.succ = prior.final.x i) ∧
      (∀ i, lessonReceipts run.execution.deliveries i.succ = lessonReceipts prior.execution.deliveries i) := by
  let clock := layout.last + 1
  let read := thresholdReadTime clock count
  let packet := thresholdPacket clock count
  let contacts := forwardReport source (layout.windows source) packet
  have starts : layout.start.time < clock := by dsimp [clock]; linarith [timed.1]
  obtain ⟨cell⟩ := guarded_threshold_exists box layout.start.time clock T need count (bits source)
    positive starts (by change read + 1 + 75 < T at horizon; linarith)
  have strict : StrictHeadRoutes contacts := forward_report_strict source (layout.windows source)
    (fun d hd => by linarith [threshold_packet_future hd, timed.2 source, show clock = layout.last + 1 from rfl])
  have queue := forward_report_inputs prior.execution source (layout.windows source) packet
    (bits source) (prior.reports source)
  obtain ⟨weave⟩ := compose_scheduled_receiver prior.execution cell.execution prior.complete cell.complete
    rfl [] contacts strict (List.Perm.of_eq queue)
  let e : Execution (prependParameters θH θ) (layout.appendThreshold source need count).route
      (layout.appendThreshold source need count).start _ := weave.execution
  have hp := threshold_probe_physical box layout.start.time read need (thresholdCalendar clock count)
  have init := threshold_probe_initial layout.start.time read need (thresholdCalendar clock count)
  have reports (i : Fin (n + 1)) : Reports e i ((layout.appendThreshold source need count).windows i)
      (Fin.cases (bits source && decide (need ≤ count)) bits i) := by
    cases i using Fin.cases with
    | zero =>
      unfold Reports ReportWindow.dates
      rw [show e.emissionTimes 0 = cell.execution.emissionTimes 0 from weave.head_emission_times]
      exact cell.reports
    | succ i =>
      unfold Reports ReportWindow.dates
      rw [show e.emissionTimes i.succ = prior.execution.emissionTimes i from weave.tail_emission_times i]
      exact prior.reports i
  let run : CompiledRun (prependParameters θH θ) (layout.appendThreshold source need count) T
      (Fin.cases (bits source && decide (need ≤ count)) bits) :=
    ⟨_, e, weave.complete prior.complete cell.complete, weave.contacts_transversal prior.positive cell.transverse,
      reports, prepend_physical prior.physical ⟨hp.region, hp.gain_cap, hp.recovery_cap, hp.reserve⟩ _,
      prepend_initial_ready prior.initial init, prepend_routed_causal prior.causal strict⟩
  refine ⟨run, (CausalTraceBalance.head_receipts weave.trace).trans ?_, fun _ => rfl,
    CausalTraceBalance.tail_receipts weave.trace⟩
  refine cell.deliveries.length_eq.trans ?_
  change (if bits source then packet else []).length = _
  cases bits source <;> simp [packet, thresholdPacket, conjunctionDoseTokens, threshold_calendar_length]


private theorem counter_window_eq_nil {read : ℝ} {dates : List ℝ}
    (outside : ∀ F ∈ dates, F < read ∨ read + 1 ≤ F) :
    dates.filter (counterWindow read).accepts = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro F h
  rcases outside F h with early | late
  · simp [ReportWindow.accepts, counterWindow, not_le.mpr early]
  · simp [ReportWindow.accepts, counterWindow, not_lt.mpr late]

private theorem threshold_slot_reports {θ s due later remaining}
    (slot : ThresholdSlot θ s due later remaining) :
    Reports slot.execution 0 (counterWindow due) (decide (remaining = 0)) ∧
      ∀ F ∈ slot.execution.emissionTimes 0, due < F ∧ F < due + 1 := by
  obtain ⟨fire, flag, dates, window⟩ := slot.fires
  cases eq : fire with
  | none => simp [Reports, ReportWindow.dates, dates, eq, ← flag]
  | some F =>
    have bounds := window F eq
    simp [Reports, ReportWindow.dates, dates, eq, ← flag, ReportWindow.accepts,
      counterWindow, bounds.1.le, bounds.2, bounds]

private theorem threshold_calendar_run {θ ε s T} (box : @PhysicalBox 1 θ ε)
    (dates : List ℝ) (remaining : ℕ)
    (physical : PhysicalInvariant θ s) (ready : ReadyCoordinates s 0)
    (raw : ∀ p, s.raw 0 p = none) (before : s.time < T)
    (future : ∀ d ∈ dates, s.time < d) (finish : ∀ d ∈ dates, d + 23 < T)
    (spacing : dates.Pairwise (fun a b => a + 24 ≤ b))
    (queue : s.pending = conjunctionDoseTokens 0 dates)
    (gain : s.x 0 (.z 0) = thresholdGain remaining) (recovery : s.x 0 .b = 2 / 25) :
    ∃ run : LocalRun θ s T,
      run.final.x 0 (.z 0) = thresholdGain (remaining - dates.length) ∧
      run.execution.deliveries = conjunctionDoseTokens 0 dates ∧
      (∀ F ∈ run.execution.emissionTimes 0, ∃ d ∈ dates, d < F ∧ F < d + 1) ∧
      ∀ earlierSlots d suffix, dates = earlierSlots ++ d :: suffix →
        Reports run.execution 0 (counterWindow d) (decide (remaining ≤ earlierSlots.length)) := by
  induction dates generalizing s remaining with
  | nil =>
    obtain ⟨e, complete, positive, silent, delivered⟩ :=
      quiet_ready_tail_exists (θ := θ) before
        (fun i => by rw [Subsingleton.elim i 0]; exact ready)
        (fun i p => by rw [Subsingleton.elim i 0]; exact raw p) queue
    refine ⟨⟨_, e, complete, positive⟩, ?_, delivered, ?_, ?_⟩
    · simpa [quietAt, quietValues] using gain
    · simp [Execution.emissionTimes, silent]
    · intro earlierSlots d suffix split
      cases earlierSlots <;> simp at split
  | cons d ds ih =>
    obtain ⟨gap, spaced⟩ := List.pairwise_cons.mp spacing
    have late : ∀ t ∈ conjunctionDoseTokens 0 ds, d + 24 ≤ t.due := by
      intro t ht
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
      exact gap a ha
    obtain ⟨slot⟩ := threshold_slot_exists box physical ready raw (future d (by simp))
      queue late gain recovery
    obtain ⟨tail, finalGain, delivered, tailDates, tailReports⟩ :=
      ih (remaining - 1) (slot.execution.physical_invariant box physical) slot.ready slot.rawNone
        (by linarith [slot.date, finish d (by simp)])
        (fun a ha => by linarith [slot.date, gap a ha])
        (fun a ha => finish a (by simp [ha])) spaced slot.pending slot.gain slot.recovery
    obtain ⟨headReport, headDates⟩ := threshold_slot_reports slot
    let e := slot.execution.append tail.execution
    have complete : CompleteThrough e T := tail.complete
    refine ⟨⟨_, e, complete, (Execution.contactsTransversal_append _ _).2
      ⟨slot.transverse, tail.positive⟩⟩, ?_, ?_, ?_, ?_⟩
    · rw [finalGain, List.length_cons]
      congr 1
      omega
    · rw [show e.deliveries = _ from Execution.deliveries_append _ _, slot.deliveries, delivered]
      rfl
    · intro F h
      rw [show e.emissionTimes 0 = _ from Execution.emissionTimes_append _ _ _, List.mem_append] at h
      rcases h with h | h
      · exact ⟨d, by simp, headDates F h⟩
      · obtain ⟨a, ha, bounds⟩ := tailDates F h
        exact ⟨a, by simp [ha], bounds⟩
    · intro earlierSlots a suffix split
      unfold Reports ReportWindow.dates at *
      change (e.emissionTimes 0 |>.filter (counterWindow a).accepts).length = _
      rw [show e.emissionTimes 0 = _ from Execution.emissionTimes_append _ _ _, List.filter_append]
      cases earlierSlots with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at split
        obtain ⟨rfl, rfl⟩ := split
        rw [counter_window_eq_nil (dates := tail.execution.emissionTimes 0) (fun F h => by
          obtain ⟨t, ht, bounds⟩ := tailDates F h
          exact Or.inr (by linarith [gap t ht, bounds.1])), List.append_nil]
        simpa using headReport
      | cons first earlierSlots =>
        simp only [List.cons_append, List.cons.injEq] at split
        have ha : a ∈ ds := by rw [split.2]; simp
        rw [counter_window_eq_nil (fun F h => Or.inl (by
          linarith [gap a ha, (headDates F h).2])), List.nil_append, tailReports earlierSlots a suffix split.2]
        have eq : decide (remaining - 1 ≤ earlierSlots.length) =
            decide (remaining ≤ (first :: earlierSlots).length) := by
          apply decide_eq_decide.mpr
          simp only [List.length_cons]
          omega
        rw [eq]

/-- One physical counter cell reports at every slot after its dose
threshold. Earlier pulses write the memory, whereas pulses after the
threshold report without changing its stored gain. -/
theorem threshold_calendar_reports {θ ε} (box : @PhysicalBox 1 θ ε)
    (time T : ℝ) (need : ℕ) (dates : List ℝ) (positive : 0 < need)
    (before : time < T) (future : ∀ d ∈ dates, time < d)
    (finish : ∀ d ∈ dates, d + 23 < T)
    (spacing : dates.Pairwise (fun a b => a + 24 ≤ b)) :
    let start := (conjunctionCounter time need).requeue (conjunctionDoseTokens 0 dates)
    ∃ run : LocalRun θ start T,
      run.final.x 0 (.z 0) = (3 / 5 : ℝ) * (1 - ((need - dates.length : ℕ) : ℝ)) ∧
      run.execution.deliveries = conjunctionDoseTokens 0 dates ∧
      ∀ earlierSlots d suffix, dates = earlierSlots ++ d :: suffix →
        Reports run.execution 0 (counterWindow d) (decide (need ≤ earlierSlots.length)) := by
  let start := (conjunctionCounter time need).requeue (conjunctionDoseTokens 0 dates)
  have physical : PhysicalInvariant θ start := by
    have h := conjunction_counter_physical box time need
    exact ⟨h.region, h.gain_cap, h.recovery_cap, h.reserve⟩
  have ready : ReadyCoordinates start 0 := by
    have h := threshold_probe_ready time time need dates
    exact ⟨h.ready, h.charge, h.auxiliary⟩
  have gain : start.x 0 (.z 0) = thresholdGain need := by
    change -(3 / 5 : ℝ) * ((need - 1 : ℕ) : ℝ) = thresholdGain need
    rw [Nat.cast_sub (by omega : 1 ≤ need), Nat.cast_one]
    unfold thresholdGain
    ring
  obtain ⟨run, gain, deliveries, _, reports⟩ :=
    threshold_calendar_run box dates need physical ready (fun _ => rfl) before future finish
      spacing rfl gain rfl
  exact ⟨run, gain, deliveries, reports⟩

end RecursiveLearning.Native
