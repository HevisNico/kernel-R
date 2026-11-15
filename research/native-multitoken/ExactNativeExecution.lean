import ExecutionCuts
import NativeHistory
import PrefixAccounting
import Mathlib.Data.List.Sort

namespace NetworkStability.NativeMultiToken

open KernelR.Hybrid

/-- The fixed appendix of a native history: the three external pulse
endpoints, the two settled training cuts, the common SLOW cut, the
start of the terminal quiet suffix and each child's pulse endpoint. -/
noncomputable def exactCutDates (p : Parameters N) : List ℝ :=
  [firstDate + (auxDeadline : ℝ), secondDate p + (auxDeadline : ℝ),
    launchDate p + (auxDeadline : ℝ), firstDate + 15 / 2, secondDate p + 15 / 2,
    launchDate p + 19 / 10, launchDate p + 19 / 2] ++
  (List.finRange N).map (fun i => receiptDate p i + (auxDeadline : ℝ))

private theorem exact_cut_dates_in_range {p : Parameters N} (accepted : p.check = true) :
    ∀ date ∈ exactCutDates p, (prepared p).time ≤ date ∧ date < horizon p := by
  have gaps := (of_decide_eq_true accepted : p.Valid).2.2.1
  have g1 : (8 : ℝ) ≤ p.gap1 := by exact_mod_cast gaps.1
  have g2 : (8 : ℝ) ≤ p.gap2 := by exact_mod_cast gaps.2
  have firstNonneg : 0 ≤ firstDate := by norm_num [firstDate]
  have secondAfterFirst : firstDate + 15 / 2 < secondDate p := by unfold secondDate; linarith
  have launchAfterSecond : secondDate p + 15 / 2 < launchDate p := by unfold launchDate; linarith
  have auxNonneg : 0 ≤ (auxDeadline : ℝ) := by norm_num [auxDeadline]
  have auxUpper : (auxDeadline : ℝ) < 2 := by norm_num [auxDeadline]
  intro date mem
  change 0 ≤ date ∧ date < launchDate p + 10
  rcases List.mem_append.mp mem with external | receipt
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at external
    rcases external with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> linarith
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp receipt
    have early := receipt_after_fast_cut accepted i
    have late := (receipt_timing accepted i).2.2
    constructor <;> linarith

/-- Every actual admission belongs to the prescribed clock schedule. The
proof uses native conservation, so scheduled children are the router's
actual outputs and may appear at coincident clocks. -/
theorem native_history_admission_deadline {p : Parameters N} (accepted : p.check = true)
    (h : NativeHistory p) (token : Delivery N) (seen : token ∈ h.run.deliveries) :
    token.due + (auxDeadline : ℝ) ∈ exactCutDates p := by
  have balance := native_prefix_balance h.run
  have provenance := balance.mem_iff.mp (show token ∈ h.last.pending ++ h.run.deliveries from
    List.mem_append_right _ seen)
  rcases List.mem_append.mp provenance with seeded | routed
  · change token ∈ (seed p).map toDelivery at seeded
    obtain ⟨probe, sourceMem, identifies⟩ := List.mem_map.mp seeded
    rw [← identifies]
    simp only [seed, List.mem_append] at sourceMem
    rcases sourceMem with (first | second) | launch
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp first
      simp [exactCutDates, toDelivery]
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp second
      simp [exactCutDates, toDelivery]
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp launch
      simp [exactCutDates, toDelivery]
  · obtain ⟨event, fired, routed⟩ := List.mem_flatMap.mp routed
    rw [h.emissions] at fired
    have when : event.2 = launchDate p + latency p event.1 := by
      have occurs : event.2 ∈ h.launch.emissionTimes event.1 :=
        List.mem_map_of_mem (List.mem_filter.mpr ⟨fired, by simp⟩)
      simpa only [h.fires, List.mem_singleton] using occurs
    rw [when, router_launch accepted] at routed
    rcases List.mem_singleton.mp routed with rfl
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨event.1, List.mem_finRange _, rfl⟩

/-- One execution through the horizon with the entire finite schedule of
append boundaries. Its observations and ledgers agree with the original
construction, including when distinct cells share a deadline. -/
theorem native_exact_execution {p : Parameters N} (accepted : p.check = true) :
    ∃ (history : NativeHistory p)
      (run : Execution (nativeParameters N) (router p) (prepared p) history.last),
      CompleteThrough run (horizon p) ∧ history.last.pending = [] ∧
      (∀ date ∈ exactCutDates p, HasExecutionCut run date) ∧
      (∀ token ∈ run.deliveries, HasExecutionCut run (token.due + (auxDeadline : ℝ))) ∧
      NativeReciprocal.nativeAdmissions run = NativeReciprocal.nativeAdmissions history.run ∧
      run.ledger.emissions = history.run.ledger.emissions ∧
      (∀ i q, run.ledger.mark i q = history.run.ledger.mark i q) ∧
      (∀ i q, run.ledger.error i q = history.run.ledger.error i q) ∧
      (∀ i, run.ledger.recovery i = history.run.ledger.recovery i) ∧
      (run.ContactsTransversal ↔ history.run.ContactsTransversal) := by
  classical
  obtain ⟨history⟩ := native_history_exists accepted
  let dates := (exactCutDates p).mergeSort (fun x y => decide (x ≤ y))
  have order : dates.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) (exactCutDates p)
  have inDates (x : ℝ) : x ∈ dates ↔ x ∈ exactCutDates p := List.mem_mergeSort
  have ranges (date : ℝ) (mem : date ∈ dates) :
      (prepared p).time ≤ date ∧ date < history.last.time := by
    rw [history.complete.1]
    exact exact_cut_dates_in_range accepted date ((inDates date).mp mem)
  obtain ⟨run, cuts, admissions, fires, marks, contact⟩ :=
    exact_execution_cuts history.run dates order ranges
  refine ⟨history, run, history.complete, history.finalQueue,
    fun date mem => cuts date ((inDates date).mpr mem), ?_, admissions, fires, marks, ?_, ?_, ?_⟩
  · intro token mem
    rw [← NativeReciprocal.admissions_deliveries run, admissions,
      NativeReciprocal.admissions_deliveries history.run] at mem
    exact cuts _ ((inDates _).mpr (native_history_admission_deadline accepted history token mem))
  · intro i q
    linarith [run.gain_balance i q, history.run.gain_balance i q]
  · intro i
    linarith [run.recovery_balance i, history.run.recovery_balance i]
  · exact Iff.of_eq contact

/-- Expose the admission and exact end of each native pulse as factors of
one execution, independently of the guarded rows that will match them. -/
theorem native_exact_admission_windows {p : Parameters N} (accepted : p.check = true) :
    ∃ (last : Snapshot N)
      (run : Execution (nativeParameters N) (router p) (prepared p) last),
      CompleteThrough run (horizon p) ∧ last.pending = [] ∧
      (∀ date ∈ exactCutDates p, HasExecutionCut run date) ∧
      ∀ admission ∈ NativeReciprocal.nativeAdmissions run,
        ∃ (before admitted finished : Snapshot N)
          (head : Execution (nativeParameters N) (router p) (prepared p) before)
          (jump : Jump (router p) before admitted)
          (body : Execution (nativeParameters N) (router p) admitted finished)
          (tail : Execution (nativeParameters N) (router p) finished last),
          run = head.append (.cons (.jump jump) (body.append tail)) ∧
          NativeReciprocal.jumpAdmissions jump = [admission] ∧
          before.time = admission.token.due ∧
          finished.time = admission.token.due + (auxDeadline : ℝ) := by
  obtain ⟨h, run, complete, queue, cuts, deadlines, _⟩ := native_exact_execution accepted
  refine ⟨h.last, run, complete, queue, cuts, ?_⟩
  intro admission seen
  have token : admission.token ∈ run.deliveries := by
    rw [← NativeReciprocal.admissions_deliveries run]
    exact List.mem_map_of_mem seen
  exact admission_through_cut run admission seen (by norm_num [auxDeadline])
    (deadlines _ token)

/-- Recover the physical snapshot at each of the two settled cuts of the
exact run from the explicitly constructed training prefixes. -/
theorem exact_training_cuts {p : Parameters N} (accepted : p.check = true)
    (history : NativeHistory p) {last : Snapshot N}
    (run : Execution (nativeParameters N) (router p) (prepared p) last)
    (cuts : ∀ date ∈ exactCutDates p, HasExecutionCut run date) :
    ∀ t ∈ [firstDate + 15 / 2, secondDate p + 15 / 2],
      ∃ (cut : Snapshot N) (head : Execution (nativeParameters N) (router p) (prepared p) cut)
        (tail : Execution (nativeParameters N) (router p) cut last),
        run = head.append tail ∧ cut.time = t ∧
        (∀ i, cut.main i = .ready ∧ ∀ q, cut.raw i q = none ∧ cut.aux i q = .ready) := by
  have compare {reference : Snapshot N} (referenceRun : Execution (nativeParameters N) (router p) (prepared p) reference)
      {date : ℝ} (refComplete : CompleteThrough referenceRun date)
      (refReady : ∀ i, ReadyCoordinates reference i) (refRaw : ∀ i q, reference.raw i q = none)
      (scheduled : date ∈ exactCutDates p) :
      ∃ (cut : Snapshot N) (head : Execution (nativeParameters N) (router p) (prepared p) cut)
        (tail : Execution (nativeParameters N) (router p) cut last),
        run = head.append tail ∧ cut.time = date ∧
        (∀ i, cut.main i = .ready ∧ ∀ q, cut.raw i q = none ∧ cut.aux i q = .ready) := by
    obtain ⟨cut, head, tail, complete, shape⟩ := cuts date scheduled
    have same := (head.observational_unique referenceRun (native_box N) (prepared_physical accepted)
      complete refComplete).1
    refine ⟨cut, head, tail, shape, complete.1, fun i => ⟨?_, fun q => ⟨?_, ?_⟩⟩⟩
    · rw [same.main]; exact (refReady i).ready
    · rw [same.raw]; exact refRaw i q
    · rw [same.aux]; exact ((refReady i).auxiliary q).1
  intro date mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · let refRun := history.start.append (history.first.intake.append history.first.wave)
    have refComplete : CompleteThrough refRun (firstDate + 15 / 2) := by
      rw [← history.firstDate]
      exact history.first.settledComplete
    exact compare refRun refComplete history.first.settledReady history.first.settledRaw
      (by simp [exactCutDates])
  · let refRun := history.start.append (history.first.intake.append (history.first.wave.append
      (history.first.quiet.append (history.second.intake.append history.second.wave))))
    have refComplete : CompleteThrough refRun (secondDate p + 15 / 2) := by
      have settled := history.second.settledComplete
      refine ⟨settled.1.trans (congrArg (fun t => t + 15 / 2) history.first.date), settled.2.1, ?_⟩
      intro token mem
      have later := settled.2.2 token mem
      rw [history.first.date] at later
      exact later
    exact compare refRun refComplete history.second.settledReady history.second.settledRaw
      (by simp [exactCutDates])

def QuietSuffix (p : Parameters N) {last : Snapshot N}
    (run : Execution (nativeParameters N) (router p) (prepared p) last) : Prop :=
    ∃ (cut : Snapshot N)
      (head : Execution (nativeParameters N) (router p) (prepared p) cut)
      (tail : Execution (nativeParameters N) (router p) cut last),
      run = head.append tail ∧ cut.time = launchDate p + 19 / 2 ∧
      CompleteThrough tail (horizon p) ∧ tail.deliveries = [] ∧ tail.ledger.emissions = [] ∧
      tail.AllStates (fun s => ∀ i, s.main i = .ready ∧ ∀ q, s.raw i q = none ∧ s.aux i q = .ready)

/-- On the same witness, the final suffix starts at the planned settled
receipt cut and stays quiet through the frozen horizon. -/
theorem native_exact_quiet_suffix {p : Parameters N} (accepted : p.check = true)
    (history : NativeHistory p)
    (run : Execution (nativeParameters N) (router p) (prepared p) history.last)
    (cuts : ∀ date ∈ exactCutDates p, HasExecutionCut run date)
    (fires : run.ledger.emissions = history.run.ledger.emissions) : QuietSuffix p run := by
  obtain ⟨reference, refPart, _, _, refComplete, refQueue, refReady⟩ := history.receiptQuiet
  let refHead := history.throughWire.append refPart
  have before : CompleteThrough refHead (launchDate p + 19 / 2) := refComplete
  obtain ⟨cut, head, tail, complete, split⟩ := cuts (launchDate p + 19 / 2) (by simp [exactCutDates])
  have same := (head.observational_unique refHead (native_box N) (prepared_physical accepted) complete before).1
  have empty : cut.pending = [] := by
    have queue := same.pending
    rw [refQueue] at queue
    exact queue.eq_nil
  have noFire : tail.ledger.emissions = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro event member
    have inRun : event ∈ run.ledger.emissions := by
      rw [split, Execution.emissions_append]
      exact List.mem_append_right _ member
    rw [fires, history.emissions] at inRun
    have when : event.2 ∈ history.launch.emissionTimes event.1 := List.mem_map_of_mem
      (List.mem_filter.mpr ⟨inRun, by simp⟩)
    rw [history.fires, List.mem_singleton] at when
    have tooLate := (tail.emission_time_bounds event member).1
    rw [complete.1, when] at tooLate
    linarith [(scalar_latency accepted event.1).2.1]
  have noInput : tail.deliveries = [] := by
    have balance := native_prefix_balance tail
    rw [history.finalQueue, empty, noFire, List.flatMap_nil, List.nil_append] at balance
    exact balance.eq_nil
  refine ⟨cut, head, tail, split, complete.1, history.complete, noInput, noFire, ?_⟩
  have isolated (i : Fin N) (q : Port) : NoArrivalAt tail i q := by simp [NoArrivalAt, noInput]
  apply tail.allStates_forall
  intro i
  apply tail.allStates_and
  · apply tail.ready_states_of_no_emissions i
    · rw [same.main]; exact (refReady i).1.ready
    · simp [Execution.emissionTimes, noFire]
  · apply tail.allStates_forall
    intro q
    have raw : cut.raw i q = none := by rw [same.raw]; exact (refReady i).2 q
    have aux : cut.aux i q = .ready := by rw [same.aux]; exact ((refReady i).1.auxiliary q).1
    have band : RestBand (cut.x i (.m q)) := by rw [same.values]; exact ((refReady i).1.auxiliary q).2
    exact tail.allStates_and (tail.raw_none_states i q raw (isolated i q))
      (tail.aux_ready_without_input_band i q aux band.2 raw (isolated i q))

end NetworkStability.NativeMultiToken
