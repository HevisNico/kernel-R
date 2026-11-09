import RecursiveLearning.Example
import KernelR.HybridDoseCounting
import KernelR.HybridQuietSourceArrival
import KernelR.HybridWeakInputCycleExistence
import KernelR.HybridCrossingExecution

/-! Encode the two teaching credits and the selector in the three native
log-gains. The teacher pulse script is supplied in advance. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid

def Memory.portCredit (memory : Memory) (port : Port) : Nat :=
  if port = 0 then memory.preparationCredit
  else if port = 1 then memory.practiceCredit
  else if memory.focusOnPractice then 1 else 0

def Encodes {n : Nat} (origin : Port → ℝ) (state : Snapshot n)
    (teacher : Fin n) (memory : Memory) : Prop :=
  ∀ port, state.x teacher (.z port) =
    origin port + (3 / 5 : ℝ) * Memory.portCredit memory port

/-- The physical log-gain encodes the selector with a strict read margin of
    half a dose. This is a comparison of coordinates at the snapshot. -/
theorem selector_iff {n : Nat} {origin : Port → ℝ} {state : Snapshot n}
    {teacher : Fin n} {memory : Memory} (encoded : Encodes origin state teacher memory) :
    origin 2 + 3 / 10 < state.x teacher (.z 2) ↔ memory.focusOnPractice = true := by
  rw [encoded 2]
  cases h : memory.focusOnPractice <;> norm_num [Memory.portCredit, h]

/-- For an actual trace with complete exposed ERROR covers, the endpoint
    represents the proposed memory exactly when all three dose counts agree.
    Wrong, missing and excess doses are all detected. -/
theorem encodes_iff_counts {n θ route s u teacher before after origin}
    (execution : @Execution n θ route s u)
    (covers : ∀ port, ErrorSectionCover teacher port execution)
    (encoded : Encodes origin s teacher before) :
    Encodes origin u teacher after ↔
      ∀ port, Memory.portCredit before port + (covers port).count =
        Memory.portCredit after port := by
  have physical (port : Port) : u.x teacher (.z port) =
      origin port + (3 / 5 : ℝ) *
        (↑(Memory.portCredit before port + (covers port).count) : ℝ) := by
    rw [execution.gain_balance, (covers port).ledger_eq, encoded port, Nat.cast_add]
    ring
  constructor
  · intro endEncoded port
    have h := (physical port).symm.trans (endEncoded port)
    have hcast : (↑(Memory.portCredit before port + (covers port).count) : ℝ) =
        (Memory.portCredit after port : ℝ) := by
      linarith
    exact_mod_cast hcast
  · intro counts port
    rw [physical port, counts port]

/-- The whole physical effect of one prescribed weak source pulse. The
    execution includes waiting, delivery, the sensor cycle and quiet return. -/
structure PortDose (θ : Fin 1 → Parameters) (route : Router 1)
    (start : Snapshot 1) (port : Port) (due : ℝ) (later : List (Delivery 1)) where
  final : Snapshot 1
  execution : Execution θ route start final
  transversal : execution.ContactsTransversal
  complete : CompleteThrough execution (due + 15 / 2)
  pending : final.pending = later
  ready : ReadyCoordinates final 0
  rawNone : ∀ p, final.raw 0 p = none
  physical : PhysicalInvariant θ final
  rawValid : RawValid final
  gain : ∀ p, final.x 0 (.z p) = start.x 0 (.z p) +
    (if p = port then 3 / 5 else 0)
  deliveries : execution.deliveries = [⟨0, port, due⟩]
  emissions : execution.ledger.emissions = []

theorem port_dose_exists {θ ε route start port due later}
    (box : @PhysicalBox 1 θ ε) (physical : PhysicalInvariant θ start)
    (rawValid : RawValid start) (ready : ReadyCoordinates start 0)
    (rawNone : ∀ p, start.raw 0 p = none)
    (before : start.time < due) (queue : start.pending = ⟨0, port, due⟩ :: later)
    (separated : ∀ d ∈ later, due + 8 ≤ d.due)
    (weak : Real.exp (start.x 0 (.z port)) ≤ 7 / 6)
    (small : start.x 0 (.z port) ≤ Real.log (6 / 5) + 1 / 1000) :
    Nonempty (PortDose θ route start port due later) := by
  obtain ⟨arrival⟩ := quiet_source_arrival_exists (route := route) box start
    (⟨0, port, due⟩ : Delivery 1) later physical rawValid
    (fun j => by simpa only [Subsingleton.elim j 0] using ready)
    (fun j p => by simpa only [Subsingleton.elim j 0] using rawNone p) before queue
    (fun d hd => by linarith [separated d hd])
  obtain ⟨cycle⟩ := weak_input_cycle_exists (route := route) arrival.final box
    arrival.physical arrival.raw_valid 0 port arrival.ready
    (by rw [arrival.gain_preserved]; exact weak)
    (by rw [arrival.gain_preserved]; exact small)
    arrival.raw_active arrival.raw_other (by
      rw [arrival.date, arrival.pending]
      exact separated)
  exact ⟨{
    final := cycle.final
    execution := arrival.execution.append cycle.execution
    transversal := (Execution.contactsTransversal_append _ _).2
      ⟨arrival.contacts_transversal, cycle.contacts_transversal⟩
    complete := by
      change CompleteThrough cycle.execution (due + 15 / 2)
      simpa only [show arrival.final.time = due from arrival.date] using cycle.complete
    pending := cycle.pending.trans arrival.pending
    ready := cycle.pulse.coordinates
    rawNone := cycle.pulse.raw_finished
    physical := cycle.physical
    rawValid := cycle.raw_valid
    gain := by
      intro p
      by_cases h : p = port
      · subst p
        rw [cycle.pulse.gain_target, arrival.gain_preserved]
        simp
      · rw [cycle.pulse.gain_other p h, arrival.gain_preserved]
        simp [h]
    deliveries := by
      rw [Execution.deliveries_append, arrival.deliveries, cycle.deliveries, List.append_nil]
    emissions := by
      rw [Execution.emissions_append, arrival.emissions, cycle.emissions, List.nil_append]
  }⟩

/-- A declared queue delivering preparation, selector and practice doses at
    distinct times. No learner response is used to fill this queue. -/
def feedbackQueue (start : ℝ) : List (Delivery 1) :=
  [⟨0, 0, start + 1⟩, ⟨0, 2, start + 9⟩, ⟨0, 1, start + 17⟩]

structure ScriptedRun (θ : Fin 1 → Parameters) (route : Router 1)
    (start : Snapshot 1) where
  middle : Snapshot 1
  final : Snapshot 1
  first : Execution θ route start middle
  second : Execution θ route middle final
  transversal : (first.append second).ContactsTransversal
  physicalStart : PhysicalInvariant θ start
  firstComplete : CompleteThrough first (start.time + 33 / 2)
  secondComplete : CompleteThrough second (start.time + 49 / 2)
  initialMemory : Encodes (fun p => start.x 0 (.z p)) start 0 Example.initial
  firstMemory : Encodes (fun p => start.x 0 (.z p)) middle 0 Example.first
  secondMemory : Encodes (fun p => start.x 0 (.z p)) final 0 Example.second
  deliveries : (first.append second).deliveries = feedbackQueue start.time
  noEmissions : (first.append second).ledger.emissions = []
  pendingEmpty : final.pending = []

/-- Under the weak-input hypotheses, the supplied pulses realize both
    committed memory states of the discrete example on one native execution.
    The middle snapshot is carried unchanged into the second segment. -/
theorem scripted_run_exists {θ ε route start}
    (box : @PhysicalBox 1 θ ε) (physical : PhysicalInvariant θ start)
    (rawValid : RawValid start) (ready : ReadyCoordinates start 0)
    (rawNone : ∀ p, start.raw 0 p = none)
    (queue : start.pending = feedbackQueue start.time)
    (weak : ∀ p, Real.exp (start.x 0 (.z p)) ≤ 7 / 6)
    (small : ∀ p, start.x 0 (.z p) ≤ Real.log (6 / 5) + 1 / 1000) :
    Nonempty (ScriptedRun θ route start) := by
  let time := start.time
  obtain ⟨prep⟩ := port_dose_exists (route := route) (port := 0) (due := time + 1)
    (later := [⟨0, 2, time + 9⟩, ⟨0, 1, time + 17⟩])
    box physical rawValid ready rawNone (by dsimp [time]; linarith) queue (by
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · dsimp
        linarith
      · obtain rfl := List.mem_singleton.mp hd
        dsimp
        linarith) (weak 0) (small 0)
  have prepOther (p : Port) (ne : p ≠ 0) : prep.final.x 0 (.z p) = start.x 0 (.z p) := by
    rw [prep.gain p]
    simp [ne]
  obtain ⟨selector⟩ := port_dose_exists (route := route) (port := 2) (due := time + 9)
    (later := [⟨0, 1, time + 17⟩]) box prep.physical prep.rawValid prep.ready prep.rawNone
    (by rw [prep.complete.1]; linarith) prep.pending (by
      intro d hd
      obtain rfl := List.mem_singleton.mp hd
      dsimp
      linarith)
    (by rw [prepOther 2 (by decide)]; exact weak 2)
    (by rw [prepOther 2 (by decide)]; exact small 2)
  have practiceUnchanged : selector.final.x 0 (.z 1) = start.x 0 (.z 1) := by
    rw [selector.gain 1, prepOther 1 (by decide)]
    simp [show (1 : Port) ≠ 2 by decide]
  obtain ⟨practice⟩ := port_dose_exists (route := route) (port := 1) (due := time + 17)
    (later := []) box selector.physical selector.rawValid selector.ready selector.rawNone
    (by rw [selector.complete.1]; linarith) selector.pending (by simp)
    (by rw [practiceUnchanged]; exact weak 1) (by rw [practiceUnchanged]; exact small 1)
  refine ⟨{
    middle := selector.final
    final := practice.final
    first := prep.execution.append selector.execution
    second := practice.execution
    transversal := by simp [prep.transversal, selector.transversal, practice.transversal]
    physicalStart := physical
    firstComplete := ?_
    secondComplete := ?_
    initialMemory := ?_
    firstMemory := ?_
    secondMemory := ?_
    deliveries := ?_
    noEmissions := ?_
    pendingEmpty := practice.pending
  }⟩
  · change CompleteThrough selector.execution (start.time + 33 / 2)
    convert selector.complete using 1
    dsimp [time]
    ring
  · convert practice.complete using 1
    dsimp [time]
    ring
  · intro p
    fin_cases p <;> norm_num [Memory.portCredit, Example.initial]
  · intro p
    rw [selector.gain p, prep.gain p]
    fin_cases p <;> norm_num [Memory.portCredit, Example.first]
  · intro p
    rw [practice.gain p, selector.gain p, prep.gain p]
    fin_cases p <;> norm_num [Memory.portCredit, Example.second]
  · simp only [Execution.deliveries_append, prep.deliveries, selector.deliveries,
      practice.deliveries]
    rfl
  · simp only [Execution.emissions_append, prep.emissions, selector.emissions,
      practice.emissions, List.nil_append]

/-- A READY teacher with unit gain at every port. This is a prepared
    physical state with its feedback queue already present. -/
noncomputable def preparedTeacher (start : ℝ) : Snapshot 1 where
  time := start
  x := fun _ coordinate => match coordinate with
    | .q => 1 / 10
    | .m _ => 1 / 40
    | .z _ => 0
    | .b => 2 / 25
    | .energy => 100
  main := fun _ => .ready
  aux := fun _ _ => .ready
  raw := fun _ _ => none
  pending := feedbackQueue start

theorem prepared_run_exists {θ ε route} (box : @PhysicalBox 1 θ ε) (start : ℝ) :
    Nonempty (ScriptedRun θ route (preparedTeacher start)) := by
  have caps (i : Fin 1) (p : Port) : 1 ≤ (θ i).cap p := by
    have lower := (box.2 i p).1.1
    rcases box.1 with hε | hε
    all_goals rw [hε] at lower
    all_goals norm_num at lower
    all_goals linarith
  have physical : PhysicalInvariant θ (preparedTeacher start) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro i
      norm_num [UpperRegion, preparedTeacher, auxUpper]
    · intro i p
      exact Real.log_nonneg (caps i p)
    · intro i
      norm_num [preparedTeacher]
    · intro i
      norm_num [preparedTeacher]
  have ready : ReadyCoordinates (preparedTeacher start) 0 := by
    exact ⟨rfl, by norm_num [preparedTeacher], fun _ =>
      ⟨rfl, by norm_num [preparedTeacher, RestBand]⟩⟩
  refine scripted_run_exists box physical (by simp [RawValid, preparedTeacher])
    ready (fun _ => rfl) rfl ?_ ?_
  · intro p
    norm_num [preparedTeacher]
  · intro p
    have logPos : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
    change 0 ≤ Real.log (6 / 5 : ℝ) + 1 / 1000
    linarith

/-- The exact selector comparison flips between the two commits and stays
    high when practice is updated. -/
theorem ScriptedRun.selector_switch {θ route start} (run : ScriptedRun θ route start) :
    ¬ (start.x 0 (.z 2) + 3 / 10 < start.x 0 (.z 2)) ∧
    start.x 0 (.z 2) + 3 / 10 < run.middle.x 0 (.z 2) ∧
    start.x 0 (.z 2) + 3 / 10 < run.final.x 0 (.z 2) := by
  refine ⟨?_, (selector_iff run.firstMemory).2 rfl, (selector_iff run.secondMemory).2 rfl⟩
  intro reads
  have impossible := (selector_iff run.initialMemory).1 reads
  simp [Example.initial] at impossible

/-- The constructed history also gives a complete geometric execution with
    the same physical trajectory and deliveries. -/
theorem prepared_crossing_run_exists {θ ε route} (box : @PhysicalBox 1 θ ε) (start : ℝ) :
    ∃ (run : ScriptedRun θ route (preparedTeacher start))
      (crossing : CrossingExecution θ route (preparedTeacher start) run.final),
      crossing.execution = (run.first.append run.second).toWeak ∧
        CrossingCompleteThrough crossing (start + 49 / 2) := by
  obtain ⟨run⟩ := prepared_run_exists (route := route) box start
  let execution := run.first.append run.second
  have initial : InitiallyBelowReady (preparedTeacher start) := by
    intro i coordinate ready
    cases coordinate with
    | q => norm_num [preparedTeacher]
    | m _ => norm_num [preparedTeacher]
    | z _ => exact False.elim ready
    | b => exact False.elim ready
    | energy => exact False.elim ready
  have complete : CompleteThrough execution (start + 49 / 2) := run.secondComplete
  let crossing := execution.toCrossing initial box run.physicalStart run.transversal
  exact ⟨run, crossing, rfl, CompleteThrough.toCrossing execution complete initial box
    run.physicalStart run.transversal⟩

#print axioms selector_iff
#print axioms encodes_iff_counts
#print axioms port_dose_exists
#print axioms scripted_run_exists
#print axioms prepared_run_exists
#print axioms ScriptedRun.selector_switch
#print axioms prepared_crossing_run_exists

end RecursiveLearning.Native
