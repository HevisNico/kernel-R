import Teaching.ScheduledCommit

/-! A finite family of lesson and credit actions guarded by report
circuit outputs. The action receivers start with empty queues and
have disjoint addresses, so they may share a fixed calendar. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid

inductive CommitPlan (inputs : ℕ) : ℕ → Type
  | none : CommitPlan inputs inputs
  | add {n} (prior : CommitPlan inputs n) (decision : Fin n) (port : Port) (lesson : Lesson)
      (capacity : lesson.preparation ≤ 4 ∧ lesson.practice ≤ 4) : CommitPlan inputs (n + 1 + 1)

noncomputable def ReportLayout.appendBranch {n} (layout : ReportLayout n)
    (decision : Fin n) (port : Port) (lesson : Lesson) : ReportLayout (n + 1 + 1) :=
  let emptyWindow : ReportWindow := ⟨layout.last, layout.last⟩
  ⟨branchStart layout.start, branchRouter layout.route decision (layout.windows decision)
    (layout.last + 1) port lesson, Fin.cases emptyWindow (Fin.cases emptyWindow layout.windows),
    layout.last⟩

def noActionReports {n} (bits : Fin n → Bool) : Fin (n + 1 + 1) → Bool :=
  Fin.cases false (Fin.cases false bits)

noncomputable def CommitPlan.compile {n m} (plan : CommitPlan n m) (layout : ReportLayout n) :
    ReportLayout m :=
  match plan with
  | .none => layout
  | .add prior decision port lesson _ => (prior.compile layout).appendBranch decision port lesson

def CommitPlan.eval {n m} (plan : CommitPlan n m) (input : Fin n → Bool) : Fin m → Bool :=
  match plan with
  | .none => input
  | .add prior _ _ _ _ => noActionReports (prior.eval input)

def CommitPlan.initialParameters {n m} : CommitPlan n m → (Fin m → Parameters) → Fin n → Parameters
  | .none, θ => θ
  | .add prior _ _ _ _, θ => prior.initialParameters (fun i => θ i.succ.succ)

/-- Exact credit and lesson effects, in the receiver order declared by the
plan. Each new action uses a fresh pair. The second cell stores the credit
and the first receives the lesson. -/
def CommitPlan.Effects {n m} (plan : CommitPlan n m) (input : Fin n → Bool)
    (gains : Fin m → Port → ℝ) (receipts : Fin m → ℕ) : Prop :=
  match plan with
  | .none => True
  | @CommitPlan.add _ k prior decision port lesson _ =>
    let accepted := prior.eval input decision
    receipts 0 = (if accepted then lesson.cost else 0) ∧
    receipts (0 : Fin (k + 1)).succ = (if accepted then 1 else 0) ∧
    (∀ p, gains (0 : Fin (k + 1)).succ p = if p = port ∧ accepted then 3 / 5 else 0) ∧
    prior.Effects input (fun i => gains i.succ.succ) (fun i => receipts i.succ.succ)

theorem CommitPlan.compile_last {n m} (plan : CommitPlan n m) (layout : ReportLayout n) :
    (plan.compile layout).last = layout.last := by
  induction plan with
  | none => rfl
  | add _ _ _ _ _ ih => exact ih

theorem append_branch_timed {n} {layout : ReportLayout n} (timed : layout.WellTimed)
    (decision : Fin n) (port : Port) (lesson : Lesson) :
    (layout.appendBranch decision port lesson).WellTimed := by
  refine ⟨timed.1, ?_⟩
  intro i
  cases i using Fin.cases with
  | zero => exact le_rfl
  | succ i =>
    cases i using Fin.cases with
    | zero => exact le_rfl
    | succ i => exact timed.2 i

theorem CommitPlan.compile_timed {n m} (plan : CommitPlan n m) {layout : ReportLayout n}
    (timed : layout.WellTimed) : (plan.compile layout).WellTimed := by
  induction plan with
  | none => exact timed
  | add _ decision port lesson _ ih => exact append_branch_timed ih decision port lesson

theorem CommitPlan.initial_box {n m θ ε} (plan : CommitPlan n m)
    (box : @PhysicalBox m θ ε) : PhysicalBox (plan.initialParameters θ) ε := by
  induction plan with
  | none => exact box
  | add _ _ _ _ _ ih => exact ih ⟨box.1, fun i => box.2 i.succ.succ⟩

private theorem empty_window_reports {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (clock : ℝ) : Reports e i ⟨clock, clock⟩ false := by
  unfold Reports ReportWindow.dates
  have empty : (e.emissionTimes i).filter (ReportWindow.accepts ⟨clock, clock⟩) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro F _
    have impossible : ¬(clock ≤ F ∧ F < clock) := fun h => (not_lt_of_ge h.1) h.2
    simp [ReportWindow.accepts, impossible]
  rw [empty]
  rfl

theorem append_branch_run {n θ θC θL ε T} {layout : ReportLayout n} {bits : Fin n → Bool}
    (prior : CompiledRun θ layout T bits) (creditBox : @PhysicalBox 1 θC ε)
    (lessonBox : @PhysicalBox 1 θL ε) (decision : Fin n) (port : Port) (lesson : Lesson)
    (capacity : lesson.preparation ≤ 4 ∧ lesson.practice ≤ 4)
    (timed : layout.WellTimed) (horizon : layout.last + 75 < T) :
    ∃ (action : BranchCommit prior.execution θC θL decision (layout.windows decision)
        (layout.last + 1) T port lesson (bits decision))
      (run : CompiledRun (prependParameters θL (prependParameters θC θ))
        (layout.appendBranch decision port lesson) T (noActionReports bits)),
      run.final = action.final ∧
      lessonReceipts run.execution.deliveries 0 = (if bits decision then lesson.cost else 0) ∧
      lessonReceipts run.execution.deliveries (0 : Fin (n + 1)).succ = (if bits decision then 1 else 0) ∧
      (∀ i, lessonReceipts run.execution.deliveries i.succ.succ = lessonReceipts prior.execution.deliveries i) := by
  let clock := layout.last + 1
  have before : layout.start.time < clock := by dsimp [clock]; linarith [timed.1]
  have margin : (layout.windows decision).stop ≤ clock := by dsimp [clock]; linarith [timed.2 decision]
  have cost : (lesson.cost : ℝ) ≤ 8 := by
    exact_mod_cast (show lesson.cost ≤ 8 by unfold Lesson.cost; omega)
  obtain ⟨action⟩ := compose_report_commit prior.execution prior.complete creditBox lessonBox decision
    (layout.windows decision) (bits decision) (prior.reports decision) port lesson capacity
    before margin (by dsimp [clock]; linarith)
  let e : Execution (prependParameters θL (prependParameters θC θ))
      (layout.appendBranch decision port lesson).route (layout.appendBranch decision port lesson).start
      action.final := action.execution
  have reports (i : Fin (n + 1 + 1)) :
      Reports e i ((layout.appendBranch decision port lesson).windows i) (noActionReports bits i) := by
    cases i using Fin.cases with
    | zero => exact empty_window_reports e 0 layout.last
    | succ i =>
      cases i using Fin.cases with
      | zero => exact empty_window_reports e (0 : Fin (n + 1)).succ layout.last
      | succ i =>
        unfold Reports ReportWindow.dates
        rw [show e.emissionTimes i.succ.succ = prior.execution.emissionTimes i from action.previousTimes i]
        exact prior.reports i
  let run : CompiledRun (prependParameters θL (prependParameters θC θ))
      (layout.appendBranch decision port lesson) T (noActionReports bits) :=
    ⟨action.final, e, action.complete, action.transverse prior.positive, reports,
      branch_physical prior.physical creditBox lessonBox, branch_initial prior.initial,
      branch_causal prior.causal decision port lesson margin⟩
  exact ⟨action, run, rfl, action.lessonReceipts, action.creditReceipts, action.previousReceipts⟩

theorem split_branch_parameters {n} (θ : Fin (n + 1 + 1) → Parameters) :
    prependParameters (fun _ => θ 0)
      (prependParameters (fun _ => θ (0 : Fin (n + 1)).succ) (fun i => θ i.succ.succ)) = θ := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases <;> rfl

/-- Attach any finite family of guarded actions, preserving every effect
already established. The circuit reports can fan out to many actions. -/
theorem CommitPlan.run {n m θ ε T} (plan : CommitPlan n m) {layout : ReportLayout n}
    {bits : Fin n → Bool} (input : CompiledRun (plan.initialParameters θ) layout T bits)
    (box : @PhysicalBox m θ ε) (timed : layout.WellTimed) (horizon : layout.last + 75 < T) :
    ∃ run : CompiledRun θ (plan.compile layout) T (plan.eval bits),
      plan.Effects bits (fun i p => run.final.x i (.z p)) (lessonReceipts run.execution.deliveries) := by
  induction plan with
  | none => exact ⟨input, trivial⟩
  | add prior decision port lesson capacity ih =>
    rename_i k
    have tailBox : PhysicalBox (fun i : Fin k => θ i.succ.succ) ε :=
      ⟨box.1, fun i => box.2 i.succ.succ⟩
    have creditBox : @PhysicalBox 1 (fun _ => θ (0 : Fin (k + 1)).succ) ε :=
      ⟨box.1, fun _ => box.2 (0 : Fin (k + 1)).succ⟩
    have lessonBox : @PhysicalBox 1 (fun _ => θ 0) ε := ⟨box.1, fun _ => box.2 0⟩
    obtain ⟨tail, old⟩ := ih input tailBox
    obtain ⟨action, built, eq, lessonCount, creditCount, previous⟩ := append_branch_run tail creditBox
      lessonBox decision port lesson capacity (prior.compile_timed timed)
      (by rw [prior.compile_last]; exact horizon)
    have effects :
        (prior.add decision port lesson capacity).Effects bits
          (fun i p => built.final.x i (.z p)) (lessonReceipts built.execution.deliveries) := by
      refine ⟨lessonCount, creditCount, ?_, ?_⟩
      · intro p
        rw [eq]
        exact action.credit p
      · have values : (fun i p => built.final.x i.succ.succ (.z p)) =
            (fun i p => tail.final.x i (.z p)) := by
          funext i p
          rw [eq, action.previousValues]
        have receipts : (fun i => lessonReceipts built.execution.deliveries i.succ.succ) =
            lessonReceipts tail.execution.deliveries := funext previous
        rw [values, receipts]
        exact old
    have joined : ∃ run : CompiledRun _ ((prior.add decision port lesson capacity).compile layout) T _,
        (prior.add decision port lesson capacity).Effects bits
          (fun i p => run.final.x i (.z p)) (lessonReceipts run.execution.deliveries) :=
      ⟨built, effects⟩
    rw [split_branch_parameters θ] at joined
    exact joined

/-- Operational wiring and all report windows agree across input trials. -/
def ReportLayout.SameWiring {n} (a b : ReportLayout n) : Prop :=
  a.route = b.route ∧ a.windows = b.windows ∧ a.last = b.last

theorem ReportCircuit.compile_same_wiring {n m} (c : ReportCircuit n m)
    {a b : ReportLayout n} (same : a.SameWiring b) :
    (c.compile a).SameWiring (c.compile b) := by
  induction c with
  | inputs => exact same
  | andGate prior first rest ih =>
    obtain ⟨route, windows, clock⟩ := ih
    simp [ReportCircuit.compile, ReportLayout.SameWiring, ReportLayout.appendAnd, route, windows, clock]
  | notGate prior source ih =>
    obtain ⟨route, windows, clock⟩ := ih
    simp [ReportCircuit.compile, ReportLayout.SameWiring, ReportLayout.appendNot, route, windows, clock]

theorem CommitPlan.compile_same_wiring {n m} (p : CommitPlan n m)
    {a b : ReportLayout n} (same : a.SameWiring b) :
    (p.compile a).SameWiring (p.compile b) := by
  induction p with
  | none => exact same
  | add prior decision port lesson _ ih =>
    obtain ⟨route, windows, clock⟩ := ih
    simp [CommitPlan.compile, ReportLayout.SameWiring, ReportLayout.appendBranch, route, windows, clock]

theorem finite_teaching_program_fixed_wiring {n k m} (c : ReportCircuit n k) (p : CommitPlan k m)
    (time : ℝ) (kinds first second : Fin n → Bool) :
    (p.compile (c.compile (learnerReportLayout time kinds first))).SameWiring
      (p.compile (c.compile (learnerReportLayout time kinds second))) :=
  p.compile_same_wiring (c.compile_same_wiring ⟨rfl, rfl, rfl⟩)

/-- Compile a report circuit with any finite plan of guarded credits and
lessons. There is a complete physical execution, and every complete
upward-crossing run has the same delivery multiset and terminal state. -/
theorem compile_finite_teaching_program {n k m θ ε} (circuit : ReportCircuit n k)
    (actions : CommitPlan k m) (box : @PhysicalBox m θ ε)
    (time : ℝ) (kinds passed : Fin n → Bool) :
    let logic := circuit.compile (learnerReportLayout time kinds passed)
    let layout := actions.compile logic
    let bits := circuit.eval passed
    let T := logic.last + 76
    ∃ (run : CompiledRun θ layout T (actions.eval bits))
      (crossing : CrossingExecution θ layout.route layout.start run.final),
      crossing.execution = run.execution.toWeak ∧ CrossingCompleteThrough crossing T ∧
      actions.Effects bits (fun i p => run.final.x i (.z p)) (lessonReceipts run.execution.deliveries) ∧
      ∀ v (other : CrossingExecution θ layout.route layout.start v), CrossingCompleteThrough other T →
        ∃ native : Execution θ layout.route layout.start v, native.toWeak = other.execution ∧
          v.ObservationalEq run.final ∧ native.deliveries.Perm run.execution.deliveries ∧
          ∀ i, other.execution.emissionTimes i = run.execution.emissionTimes i := by
  let logic := circuit.compile (learnerReportLayout time kinds passed)
  let T := logic.last + 76
  have sourceBox := actions.initial_box box
  obtain ⟨tested⟩ := circuit.run_with_learners sourceBox time kinds passed (T := T)
    (by change logic.last + 45 < logic.last + 76; linarith)
  have timed : (learnerReportLayout time kinds passed).WellTimed := by
    refine ⟨?_, fun _ => le_rfl⟩
    change (trialBankStart time kinds passed).time < time + 66
    rw [trial_bank_clock]
    linarith
  obtain ⟨run, effects⟩ := actions.run tested box (circuit.compile_timed timed)
    (by change logic.last + 75 < logic.last + 76; linarith)
  obtain ⟨crossing, same, done, every⟩ := complete_crossing_accounting run.execution run.complete
    run.positive box run.physical run.initial run.causal
  exact ⟨run, crossing, same, done, effects, every⟩

end RecursiveLearning.Native
