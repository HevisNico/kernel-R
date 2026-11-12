import Teaching.SelectorRead
import Teaching.FrozenWorkFlow
import KernelR.HybridSlowReopenExistence

/-! Construct the raw-free tail after a selector read. Positive recovery
is required: a zero recovery rate does not discharge the SLOW return.
No coordinate is reset, and the energy coordinate follows the native ODE. -/
namespace RecursiveLearning.Native
open KernelR.Hybrid Set

structure QuietSensors (s : Snapshot 1) : Prop where
  auxiliary : ∀ p, s.aux 0 p = .ready ∧ RestBand (s.x 0 (.m p))
  raw : ∀ p, s.raw 0 p = none
  empty : s.pending = []

private theorem quiet_sensor_orbit {θ : Fin 1 → Parameters} {s : Snapshot 1}
    (quiet : QuietSensors s) (p : Port) (t : ℝ) :
    cellOrbitValues θ s t 0 (.m p) = relax (1 / 2) (1 / 40) (s.x 0 (.m p)) s.time t := by
  simp [cellOrbitValues, cellBaseValues, (quiet.auxiliary p).1,
    cellAuxAmplitude, current, quiet.raw, auxPulse_zero_eq_relax]

private theorem QuietSensors.at_flow_end {θ s} (quiet : QuietSensors s) {T : ℝ}
    (later : s.time ≤ T) : QuietSensors (frozenWorkEnd θ s T) := by
  refine ⟨?_, quiet.raw, quiet.empty⟩
  intro p
  refine ⟨(quiet.auxiliary p).1, ?_⟩
  change RestBand (cellOrbitValues θ s T 0 (.m p))
  rw [quiet_sensor_orbit quiet]
  exact relax_mem_Icc (by norm_num) later (quiet.auxiliary p).2 (by constructor <;> norm_num)

private theorem QuietSensors.setMain {s} (quiet : QuietSensors s) (mode : MainMode) :
    QuietSensors (setMain s 0 mode) := ⟨quiet.auxiliary, quiet.raw, quiet.empty⟩

private noncomputable def quiet_protected_flow {θ s} (quiet : QuietSensors s) {T : ℝ}
    (later : s.time < T)
    (main : ∀ t ∈ Ico s.time T,
      match s.main 0 with
      | .ready => cellOrbitValues θ s t 0 .q < 1
      | .fast => 1 / 4 < cellOrbitValues θ s t 0 .q
      | .slow => 1 / 10 < cellOrbitValues θ s t 0 .q) :
    Flow θ s (frozenWorkEnd θ s T) := by
  apply frozenWorkFlow s later
  · intro i p
    rw [Subsingleton.elim i 0]
    exact Or.inr (Or.inl (by rw [(quiet.auxiliary p).1]; decide))
  · intro i p
    rw [Subsingleton.elim i 0]
    exact Or.inr (Or.inl (by rw [(quiet.auxiliary p).1]; decide))
  · intro i p origin raw
    rw [Subsingleton.elim i 0, quiet.raw] at raw
    contradiction
  · intro t ht
    constructor
    · intro i; rw [Subsingleton.elim i 0]; exact main t ht
    · intro i p
      rw [Subsingleton.elim i 0, (quiet.auxiliary p).1, quiet_sensor_orbit quiet]
      exact relax_lt (by norm_num) ht.1 (by linarith [(quiet.auxiliary p).2.2]) (by norm_num)
  · simp [quiet.empty]

structure QuietMainReturn (θ : Fin 1 → Parameters) (route : Router 1) (s : Snapshot 1) where
  final : Snapshot 1
  execution : Execution θ route s final
  transverse : execution.ContactsTransversal
  later : s.time < final.time
  date : final.time = s.time + if s.main 0 = .fast then
    Real.log (s.x 0 .q / (1 / 4)) / a + Real.log (5 / 2) / s.x 0 .b
    else slowReopenDuration s 0
  ready : ReadyCoordinates final 0
  quiet : QuietSensors final
  charge : final.x 0 .q = 1 / 10
  gains : ∀ p, final.x 0 (.z p) = s.x 0 (.z p)
  recovery : final.x 0 .b = s.x 0 .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []
  complete : CompleteThrough execution final.time

private theorem quiet_return_complete {θ route s u} (e : Execution θ route s u)
    (quiet : QuietSensors u) (ready : u.main 0 = .ready) (charge : u.x 0 .q = 1 / 10) :
    CompleteThrough e u.time := by
  refine ⟨rfl, ?_, by simp [quiet.empty]⟩
  intro v
  apply BeforeGuards.no_jump
  · constructor
    · intro i; rw [Subsingleton.elim i 0, ready, charge]; norm_num
    · intro i p
      rw [Subsingleton.elim i 0, (quiet.auxiliary p).1]
      linarith [(quiet.auxiliary p).2.2]
  · intro i p origin raw
    rw [Subsingleton.elim i 0, quiet.raw] at raw
    contradiction
  · simp [quiet.empty]

/-- A raw-free SLOW cell with positive recovery reaches its actual logarithmic
root, takes the native reopen jump, and retains its memory and sensor residues. -/
theorem quiet_slow_return_exists {θ route s} (quiet : QuietSensors s)
    (slow : s.main 0 = .slow) (above : 1 / 10 < s.x 0 .q) (positive : 0 < s.x 0 .b) :
    Nonempty (QuietMainReturn θ route s) := by
  let T := s.time + slowReopenDuration s 0
  have later : s.time < T := by
    have ratio : 1 < s.x 0 .q / (1 / 10) := (lt_div_iff₀ (by norm_num)).mpr (by linarith)
    have duration := div_pos (Real.log_pos ratio) positive
    change s.time < s.time + Real.log (s.x 0 .q / (1 / 10)) / s.x 0 .b
    linarith
  let f : Flow θ s (frozenWorkEnd θ s T) := quiet_protected_flow quiet later
    (by intro t ht
        rw [slow]
        simpa [cellOrbitValues, cellBaseValues, slow] using slowReopen_preguard s 0 above positive ht.2)
  let before := frozenWorkEnd θ s T
  have root : before.x 0 .q = 1 / 10 := by
    simpa [before, frozenWorkEnd, cellOrbitValues, cellBaseValues, slow, T] using
      slowReopen_root s 0 above positive
  let final := setMain before 0 .ready
  let e : Execution θ route s final :=
    .cons (.flow f) (.cons (.jump (.reopen before 0 slow root)) (.nil _))
  have quietFinal : QuietSensors final := (quiet.at_flow_end later.le).setMain _
  have readyFinal : final.main 0 = .ready := by simp [final, setMain]
  have chargeFinal : final.x 0 .q = 1 / 10 := root
  refine ⟨{
    final := final, execution := e, transverse := by trivial
    later := later, ready := ⟨readyFinal, ?_, quietFinal.auxiliary⟩
    date := by simp [final, setMain, before, frozenWorkEnd, T, slow]
    quiet := quietFinal, charge := chargeFinal, gains := fun _ => rfl, recovery := rfl
    emissions := rfl, deliveries := rfl
    complete := quiet_return_complete e quietFinal readyFinal chargeFinal }⟩
  rw [chargeFinal]; constructor <;> norm_num

/-- The FAST exit is also constructed; it is not supplied as a future execution. -/
theorem quiet_fast_return_exists {θ route s} (quiet : QuietSensors s)
    (fast : s.main 0 = .fast) (above : 1 / 4 < s.x 0 .q) (positive : 0 < s.x 0 .b) :
    Nonempty (QuietMainReturn θ route s) := by
  have decay := protected_decay_schedule (initial := s.x 0 .q) (floor := (1 / 4 : ℝ)) (rate := a)
    (by norm_num) above (by linarith [a_coarse_bounds.1])
  let T := s.time + Real.log (s.x 0 .q / (1 / 4)) / a
  have later : s.time < T := by dsimp [T]; linarith [decay.1]
  let f : Flow θ s (frozenWorkEnd θ s T) := quiet_protected_flow quiet later
    (by intro t ht
        rw [fast]
        simp only [cellOrbitValues, cellBaseValues, fast]
        exact decay.2.2 (t - s.time) (by linarith [ht.1]) (by dsimp [T] at ht; linarith [ht.2]))
  let before := frozenWorkEnd θ s T
  have root : before.x 0 .q = 1 / 4 := by
    simpa [before, frozenWorkEnd, cellOrbitValues, cellBaseValues, fast, T] using decay.2.1
  let slow := setMain before 0 .slow
  let head : Execution θ route s slow :=
    .cons (.flow f) (.cons (.jump (.fastEnd before 0 fast root)) (.nil _))
  have quietSlow : QuietSensors slow := (quiet.at_flow_end later.le).setMain _
  obtain ⟨tail⟩ := quiet_slow_return_exists (θ := θ) (route := route) quietSlow
    (by simp [slow, setMain]) (by change 1 / 10 < before.x 0 .q; rw [root]; norm_num) positive
  let e := head.append tail.execution
  exact ⟨{
    final := tail.final, execution := e
    transverse := (Execution.contactsTransversal_append _ _).2 ⟨by trivial, tail.transverse⟩
    later := later.trans tail.later, ready := tail.ready, quiet := tail.quiet, charge := tail.charge
    date := by
      rw [tail.date]
      have slowMode : slow.main 0 = .slow := by simp [slow, setMain]
      rw [slowMode]
      simp only [reduceCtorEq, ite_false]
      change T + Real.log (before.x 0 .q / (1 / 10)) / s.x 0 .b = _
      rw [root, fast]
      norm_num
      dsimp [T]
      ring
    gains := tail.gains, recovery := tail.recovery
    emissions := by rw [Execution.emissions_append, tail.emissions]; rfl
    deliveries := by rw [Execution.deliveries_append, tail.deliveries]; rfl
    complete := quiet_return_complete e tail.quiet tail.ready.ready tail.charge }⟩

structure RestedSelectorRead (θ : Fin 1 → Parameters) (s : Snapshot 1) (high : Bool) where
  read : SelectorReadRun θ s high
  tail : QuietMainReturn θ (fun _ _ => []) read.final

/-- Both outcomes return through actual native flows and jumps. The positive
recovery premise is explicit and is satisfied by the capped controller. -/
theorem selector_read_return_exists {θ ε s high} (box : @PhysicalBox 1 θ ε)
    (prepared : SelectorReadPrepared s high) (positive : 0 < s.x 0 .b) :
    Nonempty (RestedSelectorRead θ s high) := by
  obtain ⟨read⟩ := selector_read_run_exists box prepared
  have quiet : QuietSensors read.final :=
    ⟨fun p => ⟨read.auxiliaryReady p, read.auxiliaryRest p⟩, read.rawNone, read.empty⟩
  have recovery : 0 < read.final.x 0 .b := by rw [read.recovery]; exact positive
  have early : 1 / 10 < read.latency := by
    cases high
    · have h := read.window.1; linarith
    · exact read.window.1
  by_cases fast : read.horizon < s.time + read.latency + 1
  · obtain ⟨tail⟩ := quiet_fast_return_exists (θ := θ) (route := fun _ _ => []) quiet
      (by rw [read.mainClock, ite_eq_left fast]) (by
        rw [read.chargeClock]
        simp only [cadenceProtectedCharge, fast, ite_true]
        rw [← exp_neg_a]
        apply Real.exp_lt_exp.mpr
        nlinarith [a_coarse_bounds.1]) recovery
    exact ⟨⟨read, tail⟩⟩
  · obtain ⟨tail⟩ := quiet_slow_return_exists (θ := θ) (route := fun _ _ => []) quiet
      (by rw [read.mainClock, ite_eq_right fast]) (by
        rw [read.chargeClock]
        simp only [cadenceProtectedCharge, fast, ite_false]
        exact selector_slow_charge_preguard prepared.recovery (le_of_not_gt fast)
          (by linarith [read.horizonBounds.2])) recovery
    exact ⟨⟨read, tail⟩⟩

noncomputable def RestedSelectorRead.execution {θ s high} (run : RestedSelectorRead θ s high) :
    Execution θ (fun _ _ => []) s run.tail.final := run.read.execution.append run.tail.execution

theorem RestedSelectorRead.complete {θ s high} (run : RestedSelectorRead θ s high) :
    CompleteThrough run.execution run.tail.final.time := run.tail.complete

theorem RestedSelectorRead.transverse {θ s high} (run : RestedSelectorRead θ s high) :
    run.execution.ContactsTransversal :=
  (Execution.contactsTransversal_append _ _).2 ⟨run.read.transversal, run.tail.transverse⟩

theorem RestedSelectorRead.only_fire {θ s high} (run : RestedSelectorRead θ s high) :
    run.execution.ledger.emissions = [(0, s.time + run.read.latency)] := by
  rw [RestedSelectorRead.execution, Execution.emissions_append, run.read.emissions, run.tail.emissions]
  rfl

theorem RestedSelectorRead.gains {θ s high} (run : RestedSelectorRead θ s high) (p : Port) :
    run.tail.final.x 0 (.z p) = s.x 0 (.z p) := (run.tail.gains p).trans (run.read.gains p)

theorem RestedSelectorRead.recovery {θ s high} (run : RestedSelectorRead θ s high) :
    run.tail.final.x 0 .b = s.x 0 .b := run.tail.recovery.trans run.read.recovery

theorem RestedSelectorRead.no_deliveries {θ s high} (run : RestedSelectorRead θ s high) :
    run.execution.deliveries = [] := by
  rw [RestedSelectorRead.execution, Execution.deliveries_append, run.read.deliveries, run.tail.deliveries]
  rfl

/-- Reserve safety is inherited through the native execution, not reset or
postulated at its endpoint. The starting physical invariant remains explicit. -/
theorem RestedSelectorRead.physical {θ ε s high} (run : RestedSelectorRead θ s high)
    (box : @PhysicalBox 1 θ ε) (initial : PhysicalInvariant θ s) :
    PhysicalInvariant θ run.tail.final := run.execution.physical_invariant box initial

/-- A zero-rate SLOW orbit does not reach the reopen guard. This is a
statement about the frozen incoming orbit, not an assumed progress theorem. -/
theorem zero_recovery_slow_orbit {θ : Fin 1 → Parameters} {s : Snapshot 1}
    (slow : s.main 0 = .slow) (zero : s.x 0 .b = 0) (above : 1 / 10 < s.x 0 .q) (t : ℝ) :
    1 / 10 < cellOrbitValues θ s t 0 .q := by
  simpa [cellOrbitValues, cellBaseValues, slow, zero] using above

/-- Return to rest is not re-preparation: a new read needs real input work. -/
theorem QuietMainReturn.not_prepared {θ route s} (run : QuietMainReturn θ route s) (high : Bool) :
    ¬ SelectorReadPrepared run.final high := by
  intro prepared
  have lower := prepared.charge.1
  rw [run.charge] at lower
  norm_num at lower

end RecursiveLearning.Native
