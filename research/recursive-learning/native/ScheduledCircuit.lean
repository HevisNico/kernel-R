import ScheduledGates

/-! Compile finite acyclic report circuits into ordinary R cells. Each new
node can only name earlier outputs. The layout assigns absolute clocks
using the input windows and the graph, independently of the input bits. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid

/-- A finite DAG in topological order, starting with the supplied reports.
An AND lists its first input separately so its arity is positive. -/
inductive ReportCircuit (inputs : ℕ) : ℕ → Type
  | inputs : ReportCircuit inputs inputs
  | andGate {n} (prior : ReportCircuit inputs n) (first : Fin n) (rest : List (Fin n)) :
      ReportCircuit inputs (n + 1)
  | notGate {n} (prior : ReportCircuit inputs n) (input : Fin n) : ReportCircuit inputs (n + 1)

structure ReportLayout (n : ℕ) where
  start : Snapshot n
  route : Router n
  windows : Fin n → ReportWindow
  last : ℝ

def ReportLayout.WellTimed {n} (layout : ReportLayout n) : Prop :=
  layout.start.time < layout.last ∧ ∀ i, (layout.windows i).stop ≤ layout.last

noncomputable def andWires {n} (windows : Fin n → ReportWindow) (slot : ℝ) :
    List (Fin n) → List (ReportWire n)
  | [] => []
  | i :: rest => ⟨i, windows i, slot⟩ :: andWires windows (slot + 8) rest

private theorem and_wires_length {n} (windows : Fin n → ReportWindow) (slot : ℝ)
    (parents : List (Fin n)) :
    (andWires windows slot parents).length = parents.length := by
  induction parents generalizing slot with
  | nil => rfl
  | cons i rest ih => simp [andWires, ih]

private theorem and_wire_bounds {n} {windows : Fin n → ReportWindow} {slot : ℝ}
    {parents : List (Fin n)} {w : ReportWire n} (mem : w ∈ andWires windows slot parents) :
    w.window = windows w.sender ∧ slot ≤ w.due ∧ w.due + 8 ≤ slot + 8 * parents.length := by
  induction parents generalizing slot with
  | nil => simp [andWires] at mem
  | cons i rest ih =>
    rcases List.mem_cons.mp mem with rfl | tail
    · refine ⟨rfl, le_rfl, ?_⟩
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith [show (0 : ℝ) ≤ rest.length by positivity]
    · obtain ⟨eq, lower, upper⟩ := ih tail
      refine ⟨eq, by linarith, ?_⟩
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

private theorem and_wires_gap {n} (windows : Fin n → ReportWindow) (slot : ℝ)
    (parents : List (Fin n)) :
    (andWires windows slot parents).Pairwise (fun a b => a.due + 8 ≤ b.due) := by
  induction parents generalizing slot with
  | nil => exact .nil
  | cons i rest ih =>
    exact List.pairwise_cons.mpr ⟨fun _ mem => (and_wire_bounds mem).2.1, ih _⟩

private theorem and_wires_bits {n} (windows : Fin n → ReportWindow) (slot : ℝ)
    (parents : List (Fin n)) (bits : Fin n → Bool) :
    (∀ w ∈ andWires windows slot parents, bits w.sender = true) ↔
      ∀ i ∈ parents, bits i = true := by
  induction parents generalizing slot with
  | nil => simp [andWires]
  | cons i rest ih => simp [andWires, ih]

noncomputable def ReportLayout.appendAnd {n} (layout : ReportLayout n) (parents : List (Fin n)) :
    ReportLayout (n + 1) :=
  let slot := layout.last + 1
  let read := slot + 8 * parents.length
  let wires := andWires layout.windows slot parents
  ⟨queueHead layout.start (scheduledAndStart layout.start.time read wires.length),
    prependRouted layout.route (reportWireContacts wires),
    Fin.cases (counterWindow read) layout.windows, read + 1⟩

noncomputable def ReportLayout.appendNot {n} (layout : ReportLayout n) (input : Fin n) :
    ReportLayout (n + 1) :=
  let clock := layout.last + 1
  ⟨queueHead layout.start (scheduledNotBase layout.start.time clock),
    prependRouted layout.route (forwardReport input (layout.windows input) [notTrigger clock]),
    Fin.cases (notWindow clock) layout.windows, clock + 18⟩

noncomputable def ReportCircuit.compile {n m} (circuit : ReportCircuit n m)
    (input : ReportLayout n) : ReportLayout m :=
  match circuit with
  | .inputs => input
  | .andGate prior first rest => (prior.compile input).appendAnd (first :: rest)
  | .notGate prior source => (prior.compile input).appendNot source

noncomputable def ReportCircuit.eval {n m} (circuit : ReportCircuit n m)
    (input : Fin n → Bool) : Fin m → Bool :=
  match circuit with
  | .inputs => input
  | .andGate prior first rest =>
    let bits := prior.eval input
    Fin.cases (decide (∀ i ∈ first :: rest, bits i = true)) bits
  | .notGate prior source =>
    let bits := prior.eval input
    Fin.cases (!bits source) bits

def initialParameters {n m} : ReportCircuit n m → (Fin m → Parameters) → Fin n → Parameters
  | .inputs, θ => θ
  | .andGate prior _ _, θ => initialParameters prior (fun i => θ i.succ)
  | .notGate prior _, θ => initialParameters prior (fun i => θ i.succ)

theorem ReportCircuit.initial_box {n m θ ε} (c : ReportCircuit n m)
    (box : @PhysicalBox m θ ε) : PhysicalBox (initialParameters c θ) ε := by
  induction c with
  | inputs => exact box
  | andGate _ _ _ ih => exact ih ⟨box.1, fun i => box.2 i.succ⟩
  | notGate _ _ ih => exact ih ⟨box.1, fun i => box.2 i.succ⟩

theorem append_and_timed {n} {layout : ReportLayout n} (timed : layout.WellTimed)
    (parents : List (Fin n)) : (layout.appendAnd parents).WellTimed := by
  have lt : layout.last < (layout.appendAnd parents).last := by
    change layout.last < layout.last + 1 + 8 * (parents.length : ℝ) + 1
    linarith [show (0 : ℝ) ≤ parents.length by positivity]
  refine ⟨timed.1.trans lt, ?_⟩
  intro i
  cases i using Fin.cases with
  | zero => exact le_rfl
  | succ i => exact (timed.2 i).trans lt.le

theorem append_not_timed {n} {layout : ReportLayout n} (timed : layout.WellTimed)
    (i : Fin n) : (layout.appendNot i).WellTimed := by
  have lt : layout.last < (layout.appendNot i).last := by
    change layout.last < layout.last + 1 + 18
    linarith
  refine ⟨timed.1.trans lt, ?_⟩
  intro j
  cases j using Fin.cases with
  | zero => exact le_rfl
  | succ j => exact (timed.2 j).trans lt.le

theorem ReportCircuit.compile_timed {n m} (c : ReportCircuit n m) {layout : ReportLayout n}
    (timed : layout.WellTimed) : (c.compile layout).WellTimed := by
  induction c with
  | inputs => exact timed
  | andGate _ first rest ih => exact append_and_timed ih (first :: rest)
  | notGate _ source ih => exact append_not_timed ih source

structure CompiledRun {m} (θ : Fin m → Parameters) (layout : ReportLayout m)
    (T : ℝ) (bits : Fin m → Bool) where
  final : Snapshot m
  execution : Execution θ layout.route layout.start final
  complete : CompleteThrough execution T
  positive : execution.ContactsTransversal
  reports : ∀ i, Reports execution i (layout.windows i) (bits i)
  physical : PhysicalInvariant θ layout.start
  initial : InitiallyBelowReady layout.start
  causal : StrictCausalRouter layout.route

theorem prepend_parameters_all {n} (θ : Fin (n + 1) → Parameters) :
    prependParameters (fun _ => θ 0) (fun i => θ i.succ) = θ := by
  funext i
  cases i using Fin.cases <;> rfl

theorem prepend_initial_ready {n} {s : Snapshot n} {h : Snapshot 1} {Q}
    (tail : InitiallyBelowReady s) (head : InitiallyBelowReady h) :
    InitiallyBelowReady (s.prependQueued h Q) := by
  intro i c ready
  cases i using Fin.cases with
  | zero => exact head 0 c ready
  | succ i => exact tail i c ready

private theorem and_initial (origin read : ℝ) (count : ℕ) :
    InitiallyBelowReady (scheduledAndStart origin read count) := by
  intro i c h
  cases c with
  | q => change (1 / 10 : ℝ) < 1; norm_num
  | m p => change (1 / 40 : ℝ) < 1; norm_num
  | z _ => exact False.elim h
  | b => exact False.elim h
  | energy => exact False.elim h

theorem append_and_run {n θ θH ε T} {layout : ReportLayout n} {bits : Fin n → Bool}
    (prior : CompiledRun θ layout T bits) (box : @PhysicalBox 1 θH ε)
    (parents : List (Fin n)) (positiveArity : 0 < parents.length)
    (timed : layout.WellTimed) (horizon : (layout.appendAnd parents).last + 45 < T) :
    ∃ run : CompiledRun (prependParameters θH θ) (layout.appendAnd parents) T
      (Fin.cases (decide (∀ i ∈ parents, bits i = true)) bits),
      (∀ i, run.final.x i.succ = prior.final.x i) ∧
      (∀ i, lessonReceipts run.execution.deliveries i.succ = lessonReceipts prior.execution.deliveries i) := by
  classical
  let slot := layout.last + 1
  let read := slot + 8 * parents.length
  let wires := andWires layout.windows slot parents
  let assigned := fun w : ReportWire n => bits w.sender
  have last : (layout.appendAnd parents).last = read + 1 := rfl
  have length : wires.length = parents.length := and_wires_length _ _ _
  have margin (w : ReportWire n) (mem : w ∈ wires) : w.window.stop ≤ w.due := by
    obtain ⟨eq, lo, _⟩ := and_wire_bounds mem
    rw [eq]
    have lower := timed.2 w.sender
    dsimp [slot] at lo
    linarith
  have reports (w : ReportWire n) (mem : w ∈ wires) :
      Reports prior.execution w.sender w.window (assigned w) := by
    rw [(and_wire_bounds mem).1]
    exact prior.reports w.sender
  have before : layout.start.time < read := by
    dsimp [read, slot]
    linarith [timed.1, show (0 : ℝ) ≤ parents.length by positivity]
  have future (w : ReportWire n) (mem : w ∈ wires) : layout.start.time < w.due := by
    have lo := (and_wire_bounds mem).2.1
    dsimp [slot] at lo
    linarith [timed.1]
  have late (w : ReportWire n) (mem : w ∈ wires) : w.due + 15 / 2 < read := by
    have hi : w.due + 8 ≤ read := (and_wire_bounds mem).2.2
    linarith
  obtain ⟨v, e, complete, transverse, gate, previous, values, receipts⟩ :=
    compose_report_and prior.execution prior.complete box wires assigned
      (by rw [length]; exact positiveArity) reports margin future (and_wires_gap _ _ _) late before
      (by rw [last] at horizon; linarith)
  let built : Execution (prependParameters θH θ) (layout.appendAnd parents).route
      (layout.appendAnd parents).start v := e
  have phys := conjunction_counter_physical box layout.start.time wires.length
  refine ⟨⟨v, built, complete, transverse prior.positive, ?_,
    prepend_physical prior.physical ⟨phys.region, phys.gain_cap, phys.recovery_cap, phys.reserve⟩ _,
    prepend_initial_ready prior.initial (and_initial _ _ _),
    prepend_routed_causal prior.causal (report_wire_contacts_strict margin)⟩, values, receipts⟩
  · intro i
    unfold Reports ReportWindow.dates
    cases i using Fin.cases with
    | zero =>
      have bit : decide (∀ w ∈ wires, assigned w = true) = decide (∀ j ∈ parents, bits j = true) :=
        decide_eq_decide.mpr (and_wires_bits _ _ _ _)
      change _ = if decide (∀ j ∈ parents, bits j = true) then 1 else 0
      rw [← bit]
      exact gate
    | succ i =>
      change ((e.emissionTimes i.succ).filter (layout.windows i).accepts).length = _
      rw [previous]
      exact prior.reports i

theorem append_not_run_with_dates {n θ θH ε T} {layout : ReportLayout n} {bits : Fin n → Bool}
    (prior : CompiledRun θ layout T bits) (box : @PhysicalBox 1 θH ε)
    (source : Fin n) (timed : layout.WellTimed) (horizon : (layout.appendNot source).last + 45 < T) :
    ∃ run : CompiledRun (prependParameters θH θ) (layout.appendNot source) T
      (Fin.cases (!bits source) bits),
      (∀ i, run.final.x i.succ = prior.final.x i) ∧
      (∀ i, lessonReceipts run.execution.deliveries i.succ = lessonReceipts prior.execution.deliveries i) ∧
      (∀ i, run.execution.emissionTimes i.succ = prior.execution.emissionTimes i) := by
  let clock := layout.last + 1
  have last : (layout.appendNot source).last = clock + 18 := rfl
  have margin : (layout.windows source).stop ≤ clock + 1 := by
    dsimp [clock]
    linarith [timed.2 source]
  obtain ⟨cell, weave, done, gate, previous⟩ := compose_report_not (clock := clock)
    prior.execution prior.complete box source (layout.windows source) (bits source) (prior.reports source)
    (by dsimp [clock]; linarith [timed.1]) (by rw [last] at horizon; linarith) margin
  let e : Execution (prependParameters θH θ) (layout.appendNot source).route
      (layout.appendNot source).start _ := weave.execution
  have phys := lessonProbe_physical (prepared := false) (time := clock) box
  refine ⟨⟨_, e, done, weave.contacts_transversal prior.positive cell.transverse, ?_,
    prepend_physical prior.physical ⟨phys.region, phys.gain_cap, phys.recovery_cap, phys.reserve⟩ _,
    prepend_initial_ready prior.initial (lessonProbe_initial false clock),
    prepend_routed_causal prior.causal (forward_report_strict source (layout.windows source) ?_)⟩,
    fun _ => rfl, CausalTraceBalance.tail_receipts weave.trace, previous⟩
  · intro i
    cases i using Fin.cases with
    | zero => exact gate
    | succ i =>
      unfold Reports ReportWindow.dates
      rw [show e.emissionTimes i.succ = prior.execution.emissionTimes i from previous i]
      exact prior.reports i
  · intro d mem
    obtain rfl := List.mem_singleton.mp mem
    exact margin

theorem append_not_run {n θ θH ε T} {layout : ReportLayout n} {bits : Fin n → Bool}
    (prior : CompiledRun θ layout T bits) (box : @PhysicalBox 1 θH ε)
    (source : Fin n) (timed : layout.WellTimed) (horizon : (layout.appendNot source).last + 45 < T) :
    ∃ run : CompiledRun (prependParameters θH θ) (layout.appendNot source) T
      (Fin.cases (!bits source) bits),
      (∀ i, run.final.x i.succ = prior.final.x i) ∧
      (∀ i, lessonReceipts run.execution.deliveries i.succ = lessonReceipts prior.execution.deliveries i) := by
  obtain ⟨run, values, receipts, _⟩ := append_not_run_with_dates prior box source timed horizon
  exact ⟨run, values, receipts⟩

/-- For a fixed finite DAG and declared input windows, a single computed
layout works for every input pattern and every admissible fabrication.
Only the input execution can vary with the input pattern. -/
theorem ReportCircuit.run {n m θ ε T} (c : ReportCircuit n m) {layout : ReportLayout n}
    {bits : Fin n → Bool} (input : CompiledRun (initialParameters c θ) layout T bits)
    (box : @PhysicalBox m θ ε) (timed : layout.WellTimed) (horizon : (c.compile layout).last + 45 < T) :
    Nonempty (CompiledRun θ (c.compile layout) T (c.eval bits)) := by
  induction c with
  | inputs => exact ⟨input⟩
  | andGate prior first rest ih =>
    rename_i k
    have tailBox : PhysicalBox (fun i : Fin k => θ i.succ) ε := ⟨box.1, fun i => box.2 i.succ⟩
    have headBox : @PhysicalBox 1 (fun _ => θ 0) ε := ⟨box.1, fun _ => box.2 0⟩
    have later : (prior.compile layout).last + 45 < T := by
      change (prior.compile layout).last + 1 + 8 * ((first :: rest).length : ℝ) + 1 + 45 < T at horizon
      linarith [show (0 : ℝ) ≤ ((first :: rest).length : ℝ) by positivity]
    obtain ⟨tail⟩ := ih input tailBox later
    obtain ⟨built, _, _⟩ := append_and_run tail headBox (first :: rest) (by simp)
      (prior.compile_timed timed) horizon
    change Nonempty (CompiledRun θ ((prior.compile layout).appendAnd (first :: rest)) T _)
    rw [prepend_parameters_all θ] at built
    exact ⟨built⟩
  | notGate prior source ih =>
    rename_i k
    have tailBox : PhysicalBox (fun i : Fin k => θ i.succ) ε := ⟨box.1, fun i => box.2 i.succ⟩
    have headBox : @PhysicalBox 1 (fun _ => θ 0) ε := ⟨box.1, fun _ => box.2 0⟩
    have later : (prior.compile layout).last + 45 < T := by
      change (prior.compile layout).last + 1 + 18 + 45 < T at horizon
      linarith
    obtain ⟨tail⟩ := ih input tailBox later
    obtain ⟨built, _, _⟩ := append_not_run tail headBox source (prior.compile_timed timed) horizon
    change Nonempty (CompiledRun θ ((prior.compile layout).appendNot source) T _)
    rw [prepend_parameters_all θ] at built
    exact ⟨built⟩

theorem CompiledRun.crossing {n θ ε layout T bits} (run : @CompiledRun n θ layout T bits)
    (box : PhysicalBox θ ε) :
    ∃ crossing : CrossingExecution θ layout.route layout.start run.final,
      crossing.execution = run.execution.toWeak ∧ CrossingCompleteThrough crossing T ∧
      ∀ otherFinal (other : CrossingExecution θ layout.route layout.start otherFinal),
        CrossingCompleteThrough other T → otherFinal.ObservationalEq run.final ∧
        ∀ i, other.execution.emissionTimes i = run.execution.emissionTimes i := by
  refine ⟨run.execution.toCrossing run.initial box run.physical run.positive, rfl,
    run.complete.toCrossing run.execution run.initial box run.physical run.positive, ?_⟩
  intro otherFinal other done
  obtain ⟨native, same⟩ := other.execution.toNative_of_transverse_completion run.execution
    run.causal box run.physical run.complete run.positive (le_of_eq done.1)
  have weak := done.toWeak_of_native other native same run.initial box run.physical
  exact ⟨(run.execution.observational_unique_weak box other.execution run.physical
    run.complete run.positive weak).1.symm,
    fun i => (run.execution.emissionTimes_unique_weak other.execution box run.physical
      run.complete run.positive weak i).symm⟩


noncomputable def learnerReportLayout (time : ℝ) {n} (kinds passed : Fin n → Bool) :
    ReportLayout n :=
  ⟨trialBankStart time kinds passed, trialBankRouter n, fun _ => ⟨time + 65, time + 66⟩, time + 66⟩

theorem ReportCircuit.layout_last_mono {n m} (c : ReportCircuit n m) (layout : ReportLayout n) :
    layout.last ≤ (c.compile layout).last := by
  induction c with
  | inputs => exact le_rfl
  | andGate prior first rest ih =>
    change _ ≤ (prior.compile layout).last + 1 + 8 * ((first :: rest).length : ℝ) + 1
    linarith [show (0 : ℝ) ≤ ((first :: rest).length : ℝ) by positivity]
  | notGate prior source ih =>
    change _ ≤ (prior.compile layout).last + 1 + 18
    linarith

theorem learner_report_layout_timed (time : ℝ) {n} (kinds passed : Fin n → Bool) :
    (learnerReportLayout time kinds passed).WellTimed := by
  refine ⟨?_, fun _ => le_rfl⟩
  change (trialBankStart time kinds passed).time < time + 66
  rw [trial_bank_clock]
  linarith

/-- Real learner reports supply the input contract of the compiler. -/
theorem learner_report_run {n θ ε T} (box : @PhysicalBox n θ ε) (time : ℝ)
    (kinds passed : Fin n → Bool) (later : time + 96 < T) :
    Nonempty (CompiledRun θ (learnerReportLayout time kinds passed) T passed) := by
  let layout := learnerReportLayout time kinds passed
  obtain ⟨bank⟩ := trial_bank_exists box later kinds passed
  have reports (i : Fin n) : Reports bank.execution i (layout.windows i) (passed i) := by
    unfold Reports ReportWindow.dates
    rw [bank.dates]
    cases h : bank.fires i with
    | none =>
      have flag : passed i = false := by simpa [h] using (bank.flags i).symm
      simp [flag]
    | some F =>
      have flag : passed i = true := by simpa [h] using (bank.flags i).symm
      obtain ⟨early, late⟩ := bank.window i F h
      simp [flag, layout, learnerReportLayout, ReportWindow.accepts, early.le, late]
  exact ⟨⟨bank.final, bank.execution, bank.complete, bank.positive, reports,
    trial_bank_physical box time kinds passed, trial_bank_initial time kinds passed, trial_bank_causal n⟩⟩

/-- The input execution can itself consist of real R learners. Their
report bits are established by their delivered trials and physical reads. -/
theorem ReportCircuit.run_with_learners {n m θ ε T} (c : ReportCircuit n m)
    (box : @PhysicalBox m θ ε) (time : ℝ) (kinds passed : Fin n → Bool)
    (horizon : (c.compile (learnerReportLayout time kinds passed)).last + 45 < T) :
    Nonempty (CompiledRun θ (c.compile (learnerReportLayout time kinds passed)) T (c.eval passed)) := by
  have later : time + 96 < T := by
    have low := c.layout_last_mono (learnerReportLayout time kinds passed)
    change time + 66 ≤ _ at low
    linarith
  obtain ⟨input⟩ := learner_report_run (c.initial_box box) time kinds passed later
  exact c.run input box (learner_report_layout_timed time kinds passed) horizon

end RecursiveLearning.Native
