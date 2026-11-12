import Teaching.SelectorReprepare
import Teaching.SelectorRoundUniversal

/-! A raw-free recurrent boundary and a fixed calendar. The period is a
conservative uniform bound, not an optimized timing claim. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

/-- Prepared resources at rest. Unlike SelectorReadPrepared, this boundary
has no admitted read RAW; the next round constructs that admission. -/
structure RoundReady (θ : Fin 1 → Parameters) (s : Snapshot 1) (high : Bool) : Prop where
  physical : PhysicalInvariant θ s
  ready : ReadyCoordinates s 0
  quiet : QuietSensors s
  recovery : s.x 0 .b = 11 / 10
  ignition : 9 / 5 ≤ Real.exp (s.x 0 (.z 1)) ∧ Real.exp (s.x 0 (.z 1)) ≤ 11 / 5
  work : s.x 0 (.z 0) = Real.log ((θ 0).cap 0)
  selector : s.x 0 (.z 2) = selectorReadLogGain high

theorem QuietMainReturn.capped_time_bound {θ route s}
    (run : QuietMainReturn θ route s) (charge : s.x 0 .q ≤ 1)
    (positive : 0 < s.x 0 .q) (recovery : s.x 0 .b = 11 / 10) :
    run.final.time < s.time + 10 := by
  rw [run.date, recovery]
  split
  · have head : Real.log (s.x 0 .q / (1 / 4)) ≤ 3 := by
      have h := Real.log_le_sub_one_of_pos (show 0 < s.x 0 .q / (1 / 4) by positivity)
      linarith
    have tail : Real.log (5 / 2 : ℝ) ≤ 3 / 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 2)
      linarith
    have divHead : Real.log (s.x 0 .q / (1 / 4)) / a ≤ 3 := by
      apply (div_le_iff₀ (by linarith [a_coarse_bounds.1])).mpr
      linarith [a_coarse_bounds.1]
    linarith
  · simp only [slowReopenDuration, recovery]
    have h := Real.log_le_sub_one_of_pos (show 0 < s.x 0 .q / (1 / 10) by positivity)
    linarith

theorem RestedSelectorRead.capped_time_bound {θ ε s high}
    (run : RestedSelectorRead θ s high) (box : @PhysicalBox 1 θ ε)
    (physical : PhysicalInvariant θ s) (recovery : s.x 0 .b = 11 / 10) :
    run.tail.final.time < s.time + 12 := by
  have pf := run.read.execution.physical_invariant box physical
  have positive : 0 < run.read.final.x 0 .q := by
    rw [run.read.chargeClock]
    unfold cadenceProtectedCharge
    split <;> positivity
  have bound := run.tail.capped_time_bound (pf.region 0).2.1 positive
    (run.read.recovery.trans recovery)
  rw [run.read.complete.1] at bound
  linarith [run.read.horizonBounds.2]

noncomputable def roundDate (origin : ℝ) (k : ℕ) : ℝ := origin + 32 * k
noncomputable def roundIgnition (origin : ℝ) (k : ℕ) : Delivery 1 :=
  reprepareIgnition (roundDate origin k + 1)

noncomputable def roundRouter (origin : ℝ) (delay : ℝ → ℝ) : Router 1 := by
  classical
  exact fun _ fire => if ∃ k : ℕ, roundDate origin k + 1 ≤ fire ∧ fire < roundDate origin k + 2
    then [cycleRead delay fire, cycleWork delay fire] else []

theorem round_router_active {origin delay fire k}
    (lower : roundDate origin k + 1 ≤ fire) (upper : fire < roundDate origin k + 2) :
    roundRouter origin delay 0 fire = [cycleRead delay fire, cycleWork delay fire] := by
  simp [roundRouter, show ∃ j : ℕ, roundDate origin j + 1 ≤ fire ∧
    fire < roundDate origin j + 2 from ⟨k, lower, upper⟩]

theorem round_router_quiet {origin delay fire k}
    (lower : roundDate origin k + 2 ≤ fire) (upper : fire < roundDate origin (k + 1) + 1) :
    roundRouter origin delay 0 fire = [] := by
  suffices absent : ¬ ∃ j : ℕ, roundDate origin j + 1 ≤ fire ∧ fire < roundDate origin j + 2 by
    simp [roundRouter, absent]
  rintro ⟨j, lo, hi⟩
  rcases le_or_gt j k with before | after
  · have h : (j : ℝ) ≤ k := by exact_mod_cast before
    dsimp [roundDate] at lo hi lower upper
    linarith
  · have h : (k : ℝ) + 1 ≤ j := by exact_mod_cast after
    simp only [roundDate, Nat.cast_add, Nat.cast_one] at lo hi lower upper
    linarith

theorem round_router_before {origin delay fire} (before : fire < origin + 1) :
    roundRouter origin delay 0 fire = [] := by
  suffices absent : ¬ ∃ j : ℕ, roundDate origin j + 1 ≤ fire ∧ fire < roundDate origin j + 2 by
    simp [roundRouter, absent]
  rintro ⟨j, lo, _⟩
  have nonnegative : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  dsimp [roundDate] at lo
  linarith

theorem round_router_causal {origin delay σ} (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : ∀ fire, delay fire ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ)) :
    StrictCausalRouter (roundRouter origin delay) := by
  intro i fire d member
  have positive := cycle_delay_gt_one budget (wire fire)
  simp only [roundRouter] at member
  split at member
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change fire < fire + delay fire + 7 / 5; linarith
    · change fire < fire + delay fire; linarith
  · simp at member

theorem round_delay_lt_two {delay σ : ℝ} (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : delay ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ)) :
    delay < 2 := by
  have bound := wire.2
  simp only [cappedTeacherWorkOffset, cappedTeacherWorkJitter] at bound budget
  linarith [capped_teacher_period_bounds.2]


theorem RoundReady.complete {θ route source s high} (ready : RoundReady θ s high)
    (e : Execution θ route source s) : CompleteThrough e s.time := by
  refine ⟨rfl, ?_, by simp [ready.quiet.empty]⟩
  intro v
  apply BeforeGuards.no_jump
  · constructor
    · intro i
      rw [Subsingleton.elim i 0, ready.ready.ready]
      linarith [ready.ready.charge.2]
    · intro i p
      rw [Subsingleton.elim i 0, (ready.quiet.auxiliary p).1]
      linarith [(ready.quiet.auxiliary p).2.2]
  · intro i p origin raw
    rw [Subsingleton.elim i 0, ready.quiet.raw] at raw
    contradiction
  · simp [ready.quiet.empty]

private theorem round_cast_transverse {n θ route s v u} (e : @Execution n θ route s u)
    (same : v = s) (positive : e.ContactsTransversal) :
    (e.cast_source same).ContactsTransversal := by
  cases same
  exact positive

structure CalendarRound (θ : Fin 1 → Parameters) (origin : ℝ) (delay : ℝ → ℝ)
    (k : ℕ) (s : Snapshot 1) (high : Bool) where
  final : Snapshot 1
  execution : Execution θ (roundRouter origin delay) (withFuture s [roundIgnition origin k]) final
  date : final.time = roundDate origin (k + 1)
  ready : RoundReady θ final high
  transverse : execution.ContactsTransversal
  complete : CompleteThrough execution (roundDate origin (k + 1))
  ignition : ℝ
  readFire : ℝ
  emissions : execution.ledger.emissions = [(0, ignition), (0, readFire)]
  cost : execution.deliveries.length = 3
  gains : ∀ p, final.x 0 (.z p) = s.x 0 (.z p)
  recovery : final.x 0 .b = s.x 0 .b

/-- Every admissible supplied delay uses the same period and ignition dates.
All waiting is a real quiet native flow and adds no input deliveries. -/
theorem calendar_round_exists {θ ε origin delay k s high σ} (box : @PhysicalBox 1 θ ε)
    (ready : RoundReady θ s high) (date : s.time = roundDate origin k)
    (nonnegative : 0 ≤ σ) (budget : σ ≤ cappedTeacherWorkJitter)
    (wire : ∀ fire, delay fire ∈ Icc (cappedTeacherWorkOffset - σ) (cappedTeacherWorkOffset + σ)) :
    Nonempty (CalendarRound θ origin delay k s high) := by
  obtain ⟨prep⟩ := rest_preparation_exists box ready.physical ready.ready ready.quiet
    (time := s.time + 1) (by linarith) ready.ignition ready.recovery ready.work ready.selector
    nonnegative budget wire
  obtain ⟨read⟩ := selector_read_return_exists box prep.prepared
    (by rw [prep.recovery, ready.recovery]; norm_num)
  have readCap : prep.final.x 0 .b = 11 / 10 := prep.recovery.trans ready.recovery
  have admittedBound : prep.final.time < s.time + 6 := by
    rw [prep.date]
    change prep.ignition + delay prep.ignition + 7 / 5 < s.time + 6
    linarith [prep.ignitionWindow.2, round_delay_lt_two budget (wire prep.ignition)]
  have returnedBound : read.tail.final.time < s.time + 18 :=
    (read.capped_time_bound box prep.physical readCap).trans (by linarith)
  let T := roundDate origin (k + 1)
  have period : T = s.time + 32 := by
    dsimp [T, roundDate]
    rw [date]
    simp [roundDate, Nat.cast_add, Nat.cast_one]
    ring
  have later : read.tail.final.time < T := by rw [period]; linarith
  obtain ⟨wait, _, waitPositive, waitSilent, waitDeliveries⟩ :=
    quiet_ready_tail_exists (θ := θ) later
      (fun i => by rw [Subsingleton.elim i 0]; exact read.tail.ready)
      (fun i p => by rw [Subsingleton.elim i 0]; exact read.tail.quiet.raw p) read.tail.quiet.empty
  let route := roundRouter origin delay
  obtain ⟨head, headLedger, headDeliveries, headContacts⟩ :=
    prep.execution.retarget_router_transversal route (by
      intro event member
      rw [prep.emissions] at member
      obtain rfl := List.mem_singleton.mp member
      have lo : s.time + 1 ≤ prep.ignition := by linarith [prep.ignitionWindow.1]
      have hi : prep.ignition < s.time + 1 + 1 := by linarith [prep.ignitionWindow.2]
      change reprepareRouter (s.time + 1) delay 0 prep.ignition =
        roundRouter origin delay 0 prep.ignition
      rw [round_router_active (by rw [← date]; exact lo) (by rw [← date]; linarith)]
      simp [reprepareRouter, cappedCycleRouter, lo, hi])
  have latencyPositive : 0 < read.read.latency := by
    cases high <;> have h := read.read.window.1 <;> linarith
  have latencyBound : read.read.latency < 1 := by
    cases high <;> have h := read.read.window.2 <;> linarith
  have readLower : roundDate origin k + 2 ≤ prep.final.time + read.read.latency := by
    rw [← date, prep.date]
    change s.time + 2 ≤ prep.ignition + delay prep.ignition + 7 / 5 + read.read.latency
    linarith [prep.ignitionWindow.1, cycle_delay_gt_one budget (wire prep.ignition)]
  have readUpper : prep.final.time + read.read.latency < roundDate origin (k + 1) + 1 := by
    change prep.final.time + read.read.latency < T + 1
    rw [period]; linarith
  obtain ⟨middle, middleLedger, middleDeliveries, middleContacts⟩ :=
    read.execution.retarget_router_transversal route (by
      intro event member
      rw [read.only_fire] at member
      obtain rfl := List.mem_singleton.mp member
      exact (round_router_quiet readLower readUpper).symm)
  obtain ⟨tail, tailLedger, tailDeliveries, tailContacts⟩ :=
    wait.retarget_router_transversal route (by simp [waitSilent])
  let body := (head.append middle).append tail
  have source : withFuture s [roundIgnition origin k] = withFuture s [reprepareIgnition (s.time + 1)] := by
    rw [date]; rfl
  let e := body.cast_source source
  have physicalStart : PhysicalInvariant θ (withFuture s [roundIgnition origin k]) :=
    ⟨ready.physical.region, ready.physical.gain_cap, ready.physical.recovery_cap, ready.physical.reserve⟩
  have gains (p : Port) : (quietAt read.tail.final T).x 0 (.z p) = s.x 0 (.z p) :=
    (read.gains p).trans (prep.gains p)
  have recovery : (quietAt read.tail.final T).x 0 .b = s.x 0 .b :=
    read.recovery.trans prep.recovery
  have quietReady := quietAt_ready_coordinates read.tail.final 0 read.tail.ready later.le
  have finalReady : RoundReady θ (quietAt read.tail.final T) high :=
    ⟨e.physical_invariant box physicalStart, quietReady,
      ⟨quietReady.auxiliary, read.tail.quiet.raw, read.tail.quiet.empty⟩,
      recovery.trans ready.recovery, by rw [gains]; exact ready.ignition,
      (gains 0).trans ready.work, (gains 2).trans ready.selector⟩
  refine ⟨{
    final := quietAt read.tail.final T, execution := e, date := rfl, ready := finalReady
    transverse := round_cast_transverse body source ?_
    complete := finalReady.complete e
    ignition := prep.ignition, readFire := prep.final.time + read.read.latency
    emissions := ?_, cost := ?_, gains := gains, recovery := recovery }⟩
  · exact (Execution.contactsTransversal_append _ _).2
      ⟨(Execution.contactsTransversal_append _ _).2
        ⟨headContacts.mpr prep.transverse, middleContacts.mpr read.transverse⟩,
        tailContacts.mpr waitPositive⟩
  · rw [Execution.cast_source_ledger]
    simp only [body, Execution.emissions_append]
    rw [headLedger, middleLedger, tailLedger, prep.emissions, read.only_fire, waitSilent]
    rfl
  · rw [Execution.cast_source_deliveries]
    simp only [body, Execution.deliveries_append]
    rw [headDeliveries, middleDeliveries, tailDeliveries, read.no_deliveries, waitDeliveries,
      List.append_nil, List.append_nil]
    exact prep.pulse_cost

end RecursiveLearning.Native
