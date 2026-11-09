import AdaptiveRounds

/-! A single compiled decision tree for a family of birth calibrations.
The tree is finite and each node uses one certified physical trial. -/

namespace RecursiveLearning.Native
open KernelR.Hybrid

/-- Every profile shares the same lesson and read port for this probe.
Only the supplied calibration and its certified outcome can vary. -/
structure CalibratedProbe (Profile : Type) where
  lesson : Lesson
  practice : Bool
  trial : Profile → AdaptiveTrial
  sameLesson : ∀ h, (trial h).lesson = lesson
  samePort : ∀ h, (trial h).testPractice = practice

theorem CalibratedProbe.same_tokens {Profile} (probe : CalibratedProbe Profile) (a b : Profile)
    (clock : ℝ) : (probe.trial a).tokens clock = (probe.trial b).tokens clock := by
  simp only [AdaptiveTrial.tokens, probe.sameLesson, probe.samePort]

/-- A tree can use a certified two-block lesson or the native count
threshold with a need-dependent birth gain. -/
inductive TreeProbe (Profile : Type)
  | lesson (probe : CalibratedProbe Profile)
  | threshold (count : ℕ) (need : Profile → ℕ) (positive : ∀ h, 0 < need h)

def TreeProbe.passes {Profile} (probe : TreeProbe Profile) (h : Profile) : Bool :=
  match probe with
  | .lesson test => (test.trial h).passes
  | .threshold count need _ => decide (need h ≤ count)

def TreeProbe.attempt {Profile n m} (probe : TreeProbe Profile) (h : Profile)
    (base : AdaptiveProgram n m) (enable : Fin m) : AdaptiveProgram n (m + 1) :=
  match probe with
  | .lesson test => base.trial enable (test.trial h)
  | .threshold count need pos => base.threshold enable (need h) count (pos h)

theorem TreeProbe.same_plan {Profile n m} (probe : TreeProbe Profile) (a b : Profile)
    {baseA baseB : AdaptiveProgram n m} (same : baseA.SamePlan baseB) (enable : Fin m) :
    (probe.attempt a baseA enable).SamePlan (probe.attempt b baseB enable) := by
  cases probe with
  | lesson test => exact .trial same (test.same_tokens a b)
  | threshold => exact .threshold same

@[simp] theorem TreeProbe.eval_head {Profile n m} (probe : TreeProbe Profile) (h : Profile)
    (base : AdaptiveProgram n m) (enable : Fin m) (input : Fin n → Bool) :
    (probe.attempt h base enable).eval input 0 = (base.eval input enable && probe.passes h) := by
  cases probe <;> rfl

@[simp] theorem TreeProbe.eval_tail {Profile n m} (probe : TreeProbe Profile) (h : Profile)
    (base : AdaptiveProgram n m) (enable i : Fin m) (input : Fin n → Bool) :
    (probe.attempt h base enable).eval input i.succ = base.eval input i := by
  cases probe <;> rfl

theorem TreeProbe.previous_effects {Profile n m} (probe : TreeProbe Profile) (h : Profile)
    (base : AdaptiveProgram n m) (enable : Fin m) {input gains receipts}
    (effects : (probe.attempt h base enable).Effects input gains receipts) :
    base.Effects input (fun i => gains i.succ) (fun i => receipts i.succ) := by
  cases probe <;> exact effects.2

structure TreeAction where
  lesson : Lesson
  creditPort : Port
  capacity : lesson.preparation ≤ 4 ∧ lesson.practice ≤ 4

inductive CalibratedTree (Profile : Type)
  | leaf (action : TreeAction)
  | ask (probe : TreeProbe Profile) (yes no : CalibratedTree Profile)

/-- Leaf indices are paths, so distinct leaves can carry the same lesson. -/
inductive CalibratedTree.Leaf {Profile : Type} : CalibratedTree Profile → Type
  | here (action : TreeAction) : Leaf (.leaf action)
  | yes {probe yes no} : Leaf yes → Leaf (.ask probe yes no)
  | no {probe yes no} : Leaf no → Leaf (.ask probe yes no)

def CalibratedTree.Leaf.action {Profile : Type} {tree : CalibratedTree Profile} :
    tree.Leaf → TreeAction
  | .here action => action
  | .yes idx => idx.action
  | .no idx => idx.action

def CalibratedTree.Leaf.reached {Profile : Type} {tree : CalibratedTree Profile} :
    tree.Leaf → Profile → Bool
  | .here _, _ => true
  | @CalibratedTree.Leaf.yes _ probe _ _ idx, h => probe.passes h && idx.reached h
  | @CalibratedTree.Leaf.no _ probe _ _ idx, h => !probe.passes h && idx.reached h

def CalibratedTree.select {Profile : Type} (h : Profile) :
    (tree : CalibratedTree Profile) → tree.Leaf
  | .leaf action => .here action
  | .ask probe yes no =>
    if probe.passes h then .yes (yes.select h) else .no (no.select h)

theorem CalibratedTree.Leaf.reached_iff {Profile : Type} {tree : CalibratedTree Profile}
    (l : tree.Leaf) (h : Profile) : l.reached h = true ↔ l = tree.select h := by
  induction l with
  | here => simp [CalibratedTree.Leaf.reached, CalibratedTree.select]
  | @yes probe _ _ l ih =>
    cases pass : probe.passes h <;> simp [CalibratedTree.Leaf.reached, CalibratedTree.select, pass, ih]
  | @no probe _ _ l ih =>
    cases pass : probe.passes h <;> simp [CalibratedTree.Leaf.reached, CalibratedTree.select, pass, ih]

def TreeAction.Effect (action : TreeAction) (active : Bool)
    (lessonGain creditGain : Port → ℝ) (lessonCount creditCount : ℕ) : Prop :=
  lessonCount = (if active then action.lesson.cost else 0) ∧
  creditCount = (if active then 1 else 0) ∧
  (∀ p, creditGain p = if p = action.creditPort ∧ active then 3 / 5 else 0) ∧
  (∀ needs, GainsRetain lessonGain needs ↔
    ((if active then action.lesson else ⟨0, 0⟩).train needs).retained = true)

structure TreeExtension {Profile : Type} {n : ℕ} (base : Profile → AdaptiveProgram 1 n)
    (enable : Fin n) (tree : CalibratedTree Profile) where
  size : ℕ
  program : Profile → AdaptiveProgram 1 size
  samePlan : ∀ a b, (program a).SamePlan (program b)
  carry : Fin n → Fin size
  lessonCell : tree.Leaf → Fin size
  creditCell : tree.Leaf → Fin size
  preserves : ∀ h input i, (program h).eval input (carry i) = (base h).eval input i
  accounts : ∀ h input gains receipts, (program h).Effects input gains receipts →
    (base h).Effects input (fun i => gains (carry i)) (fun i => receipts (carry i)) ∧
    ∀ l : tree.Leaf, l.action.Effect ((base h).eval input enable && l.reached h)
      (gains (lessonCell l)) (gains (creditCell l)) (receipts (lessonCell l)) (receipts (creditCell l))

private noncomputable def addQuestion {Profile : Type} {n : ℕ} (base : Profile → AdaptiveProgram 1 n)
    (enable : Fin n) (probe : TreeProbe Profile) (h : Profile) : AdaptiveProgram 1 (n + 1 + 1 + 1) :=
  let attempted := probe.attempt h (base h) enable
  let silent := attempted.notGate 0
  silent.andGate enable.succ.succ [0]

private theorem question_plan {Profile : Type} {n : ℕ} {base : Profile → AdaptiveProgram 1 n}
    (enable : Fin n) (probe : TreeProbe Profile)
    (same : ∀ a b, (base a).SamePlan (base b)) (a b : Profile) :
    (addQuestion base enable probe a).SamePlan (addQuestion base enable probe b) :=
  .andGate (.notGate (probe.same_plan a b (same a b) enable))

private theorem question_yes {Profile : Type} {n : ℕ} (base : Profile → AdaptiveProgram 1 n)
    (enable : Fin n) (probe : TreeProbe Profile) (h : Profile) (input : Fin 1 → Bool) :
    (addQuestion base enable probe h).eval input ((0 : Fin (n + 1)).succ.succ) =
      ((base h).eval input enable && probe.passes h) := by
  change (probe.attempt h (base h) enable).eval input 0 = _
  exact probe.eval_head h (base h) enable input

private theorem question_no {Profile : Type} {n : ℕ} (base : Profile → AdaptiveProgram 1 n)
    (enable : Fin n) (probe : TreeProbe Profile) (h : Profile) (input : Fin 1 → Bool) :
    (addQuestion base enable probe h).eval input 0 =
      ((base h).eval input enable && !probe.passes h) := by
  simp only [addQuestion, AdaptiveProgram.eval, Fin.cases_zero, Fin.cases_succ,
    List.all_cons, List.all_nil, Bool.and_true, TreeProbe.eval_head, TreeProbe.eval_tail]
  cases (base h).eval input enable <;> cases probe.passes h <;> rfl

/-- Append the tree below a guard. A silent report only launches the
negative branch if the trial itself was enabled. -/
noncomputable def CalibratedTree.append {Profile : Type} {n : ℕ}
    (base : Profile → AdaptiveProgram 1 n) (enable : Fin n)
    (same : ∀ a b, (base a).SamePlan (base b)) (tree : CalibratedTree Profile) :
    TreeExtension base enable tree :=
  match tree with
  | .leaf action =>
    ⟨n + 1 + 1, fun h => (base h).commit enable action.creditPort action.lesson action.capacity,
      fun a b => .commit (same a b), fun i => i.succ.succ, fun _ => 0,
      fun _ => (0 : Fin (n + 1)).succ, fun _ _ _ => rfl, by
        intro h input gains receipts effects
        refine ⟨effects.2.2.2.2, ?_⟩
        intro l
        cases l
        simpa only [CalibratedTree.Leaf.action, CalibratedTree.Leaf.reached, Bool.and_true] using
          (show action.Effect ((base h).eval input enable) (gains 0)
            (gains (0 : Fin (n + 1)).succ) (receipts 0) (receipts (0 : Fin (n + 1)).succ) from
            ⟨effects.1, effects.2.1, effects.2.2.1, effects.2.2.2.1⟩)⟩
  | .ask probe yes no =>
    let question := addQuestion base enable probe
    let y := yes.append question ((0 : Fin (n + 1)).succ.succ) (question_plan enable probe same)
    let z := no.append y.program (y.carry 0) y.samePlan
    ⟨z.size, z.program, z.samePlan, fun i => z.carry (y.carry i.succ.succ.succ),
      (fun l => match l with | .yes l => z.carry (y.lessonCell l) | .no l => z.lessonCell l),
      (fun l => match l with | .yes l => z.carry (y.creditCell l) | .no l => z.creditCell l),
      (fun h input i => (z.preserves h input _).trans ((y.preserves h input _).trans
        (probe.eval_tail h (base h) enable i input))),
      by
        intro h input gains receipts effects
        obtain ⟨earlier, neg⟩ := z.accounts h input gains receipts effects
        obtain ⟨prev, pos⟩ := y.accounts h input _ _ earlier
        refine ⟨probe.previous_effects h (base h) enable prev, ?_⟩
        intro l
        cases l with
        | yes l =>
          have active := pos l
          rw [question_yes] at active
          simpa only [CalibratedTree.Leaf.action, CalibratedTree.Leaf.reached, Bool.and_assoc] using active
        | no l =>
          have active := neg l
          rw [y.preserves, question_no] at active
          simpa only [CalibratedTree.Leaf.action, CalibratedTree.Leaf.reached, Bool.and_assoc] using active⟩

noncomputable def CalibratedTree.compile {Profile : Type} (tree : CalibratedTree Profile) :
    TreeExtension (fun _ : Profile => (AdaptiveProgram.inputs : AdaptiveProgram 1 1)) 0 tree :=
  tree.append (fun _ => .inputs) 0 (fun _ _ => .inputs)


noncomputable def CalibratedTree.layout {Profile : Type} (tree : CalibratedTree Profile)
    (time : ℝ) (h : Profile) : ReportLayout tree.compile.size :=
  (tree.compile.program h).compile (learnerReportLayout time (fun _ => false) (fun _ => true))

theorem CalibratedTree.same_compilation {Profile : Type} (tree : CalibratedTree Profile)
    (time : ℝ) (h reference : Profile) :
    (tree.layout time h).SameSources (tree.layout time reference) :=
  (tree.compile.samePlan h reference).compile_same_sources ⟨⟨rfl, rfl, rfl⟩, rfl⟩

/-- Fix the compiled router before the profile is supplied. Every
profile and fabrication in the declared box has a complete execution.
Each leaf's exact effect is active precisely when its path is selected. -/
theorem compile_calibrated_decision_tree {Profile : Type} {ε : ℝ} (tree : CalibratedTree Profile)
    (reference : Profile) (time : ℝ) :
    let built := tree.compile
    let compiled := tree.layout time reference
    let T := compiled.last + 76
    ∀ h θ, @PhysicalBox built.size θ ε →
      let start := (tree.layout time h).start
      ∃ (final : Snapshot built.size) (e : Execution θ compiled.route start final)
        (crossing : CrossingExecution θ compiled.route start final),
        crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing T ∧
        (∀ l : tree.Leaf, l.action.Effect (l.reached h)
          (fun p => final.x (built.lessonCell l) (.z p)) (fun p => final.x (built.creditCell l) (.z p))
          (lessonReceipts e.deliveries (built.lessonCell l)) (lessonReceipts e.deliveries (built.creditCell l))) ∧
        (∀ i, Reports e i (compiled.windows i) ((built.program h).eval (fun _ => true) i)) ∧
        ∀ v (other : CrossingExecution θ compiled.route start v), CrossingCompleteThrough other T →
          ∃ native : Execution θ compiled.route start v, native.toWeak = other.execution ∧
            v.ObservationalEq final ∧ native.deliveries.Perm e.deliveries ∧
            ∀ i, other.execution.emissionTimes i = e.emissionTimes i := by
  dsimp only
  intro h θ box
  let base := learnerReportLayout time (fun _ : Fin 1 => false) (fun _ => true)
  let p := tree.compile.program h
  have same := tree.same_compilation time h reference
  rw [← same.1.1]
  have future : time + 96 < (tree.layout time reference).last + 76 := by
    have low := p.layout_last_mono base
    change time + 66 ≤ (tree.layout time h).last at low
    rw [same.1.2.2] at low
    linarith
  obtain ⟨seed⟩ := learner_report_run (p.initial_box box) time (fun _ => false) (fun _ => true) future
  obtain ⟨run, effects⟩ := p.run seed box (learner_report_layout_timed time (fun _ => false) (fun _ => true))
    (by change (tree.layout time h).last + 75 < (tree.layout time reference).last + 76
        rw [same.1.2.2]
        linarith)
  obtain ⟨crossing, agreement, complete, every⟩ :=
    complete_crossing_accounting run.execution run.complete run.positive box run.physical run.initial run.causal
  refine ⟨run.final, run.execution, crossing, agreement, complete, ?_, ?_, every⟩
  · intro l
    have result := (tree.compile.accounts h (fun _ => true) _ _ effects).2 l
    exact result
  · intro i
    have report := run.reports i
    change Reports run.execution i ((tree.layout time h).windows i) _ at report
    rw [same.1.2.1] at report
    exact report


/-- A balanced interval search. A span of s represents s + 1 candidate
needs, and a nontrivial interval is cut at its midpoint. -/
def bisectTree {Profile : Type} (probe : ℕ → TreeProbe Profile)
    (action : ℕ → TreeAction) : ℕ → ℕ → ℕ → CalibratedTree Profile
  | 0, lo, _ => .leaf (action lo)
  | _ + 1, lo, 0 => .leaf (action lo)
  | fuel + 1, lo, span + 1 =>
    let left := span / 2
    let cut := lo + left
    .ask (probe cut) (bisectTree probe action fuel lo left)
      (bisectTree probe action fuel (cut + 1) (span - left))

theorem bisectTree_selects {Profile : Type} (probe : ℕ → TreeProbe Profile)
    (action : ℕ → TreeAction) (h : Profile) (need : ℕ)
    (comparison : ∀ cut, (probe cut).passes h = decide (need ≤ cut))
    (fuel lo span : ℕ) (enough : span ≤ fuel) (lower : lo ≤ need) (upper : need ≤ lo + span) :
    ((bisectTree probe action fuel lo span).select h).action = action need := by
  induction fuel generalizing lo span with
  | zero =>
    have eq : lo = need := by omega
    simp [bisectTree, CalibratedTree.select, CalibratedTree.Leaf.action, eq]
  | succ fuel ih =>
    cases span with
    | zero =>
      have eq : lo = need := by omega
      simp [bisectTree, CalibratedTree.select, CalibratedTree.Leaf.action, eq]
    | succ span =>
      have half : span / 2 ≤ span := Nat.div_le_self _ _
      by_cases low : need ≤ lo + span / 2
      · simp only [bisectTree, CalibratedTree.select, comparison, decide_eq_true_eq, low, ite_true,
          CalibratedTree.Leaf.action]
        exact ih lo (span / 2) (by omega) lower low
      · simp only [bisectTree, CalibratedTree.select, comparison, decide_eq_true_eq, low, ite_false,
          CalibratedTree.Leaf.action]
        exact ih (lo + span / 2 + 1) (span - span / 2) (by omega) (by omega) (by omega)

def needSearchTree {K : ℕ} (probe : ℕ → CalibratedProbe (Fin K))
    (action : ℕ → TreeAction) : CalibratedTree (Fin K) :=
  bisectTree (fun cut => .lesson (probe cut)) action (K - 1) 1 (K - 1)

theorem need_search_selects {K : ℕ} (probe : ℕ → CalibratedProbe (Fin K))
    (action : ℕ → TreeAction) (h : Fin K)
    (comparison : ∀ cut, ((probe cut).trial h).passes = decide (h.val + 1 ≤ cut)) :
    ((needSearchTree probe action).select h).action = action (h.val + 1) := by
  have within := h.isLt
  exact bisectTree_selects (fun cut => .lesson (probe cut)) action h (h.val + 1) comparison
    (K - 1) 1 (K - 1) le_rfl
    (by omega) (by omega)

/-- A physical binary search, given calibrated comparisons with the pivots.
The terminal lesson and credit realize the action indexed by the hidden
need. The generic tree theorem supplies the exact inactive-leaf effects. -/
theorem compile_binary_need_search {K : ℕ} {ε : ℝ} (probe : ℕ → CalibratedProbe (Fin K))
    (action : ℕ → TreeAction) (comparison : ∀ h cut, ((probe cut).trial h).passes = decide (h.val + 1 ≤ cut))
    (reference : Fin K) (time : ℝ) (h : Fin K)
    (θ : Fin (needSearchTree probe action).compile.size → Parameters)
    (box : PhysicalBox θ ε) :
    let tree := needSearchTree probe action
    let compiled := tree.layout time reference
    let start := (tree.layout time h).start
    ∃ (final : Snapshot tree.compile.size) (e : Execution θ compiled.route start final)
      (crossing : CrossingExecution θ compiled.route start final),
      crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing (compiled.last + 76) ∧
      (action (h.val + 1)).Effect true
        (fun p => final.x (tree.compile.lessonCell (tree.select h)) (.z p))
        (fun p => final.x (tree.compile.creditCell (tree.select h)) (.z p))
        (lessonReceipts e.deliveries (tree.compile.lessonCell (tree.select h)))
        (lessonReceipts e.deliveries (tree.compile.creditCell (tree.select h))) := by
  let tree := needSearchTree probe action
  obtain ⟨final, e, crossing, same, done, effects, _, _⟩ :=
    compile_calibrated_decision_tree tree reference time h θ box
  have selected := effects (tree.select h)
  have reached : (tree.select h).reached h = true := ((tree.select h).reached_iff h).mpr rfl
  rw [reached, need_search_selects probe action h (comparison h)] at selected
  exact ⟨final, e, crossing, same, done, selected⟩


/-- Profile i represents the single hidden need i + 1. Every pivot
uses that same need to initialize its native threshold cell. -/
def nativeNeedSearchTree (K : ℕ) (action : ℕ → TreeAction) : CalibratedTree (Fin K) :=
  bisectTree (fun cut => .threshold cut (fun h : Fin K => h.val + 1) (fun _ => by omega))
    action (K - 1) 1 (K - 1)

theorem native_need_search_selects {K : ℕ} (action : ℕ → TreeAction) (h : Fin K) :
    ((nativeNeedSearchTree K action).select h).action = action (h.val + 1) := by
  have within := h.isLt
  exact bisectTree_selects (fun cut => .threshold cut (fun h : Fin K => h.val + 1) (fun _ => by omega))
    action h (h.val + 1) (fun _ => rfl) (K - 1) 1 (K - 1) le_rfl (by omega) (by omega)

theorem native_need_search_same_compilation {K : ℕ} (positive : 0 < K)
    (action : ℕ → TreeAction) (time : ℝ) (h : Fin K) :
    ((nativeNeedSearchTree K action).layout time h).SameSources
      ((nativeNeedSearchTree K action).layout time ⟨0, positive⟩) :=
  (nativeNeedSearchTree K action).same_compilation time h ⟨0, positive⟩

/-- Native binary search with no supplied pivot comparisons. The router
is compiled from K and the actions. A profile supplies only the hidden
need used in the birth calibration of each threshold cell. -/
theorem compile_native_binary_need_search {K : ℕ} {ε : ℝ} (positive : 0 < K)
    (action : ℕ → TreeAction) (time : ℝ) (h : Fin K)
    (θ : Fin (nativeNeedSearchTree K action).compile.size → Parameters)
    (box : PhysicalBox θ ε) :
    let tree := nativeNeedSearchTree K action
    let compiled := tree.layout time ⟨0, positive⟩
    let start := (tree.layout time h).start
    let T := compiled.last + 76
    ∃ (final : Snapshot tree.compile.size) (e : Execution θ compiled.route start final)
      (crossing : CrossingExecution θ compiled.route start final),
      crossing.execution = e.toWeak ∧ CrossingCompleteThrough crossing T ∧
      (action (h.val + 1)).Effect true
        (fun p => final.x (tree.compile.lessonCell (tree.select h)) (.z p))
        (fun p => final.x (tree.compile.creditCell (tree.select h)) (.z p))
        (lessonReceipts e.deliveries (tree.compile.lessonCell (tree.select h)))
        (lessonReceipts e.deliveries (tree.compile.creditCell (tree.select h))) ∧
      (∀ l : tree.Leaf, l ≠ tree.select h → l.action.Effect false
        (fun p => final.x (tree.compile.lessonCell l) (.z p))
        (fun p => final.x (tree.compile.creditCell l) (.z p))
        (lessonReceipts e.deliveries (tree.compile.lessonCell l))
        (lessonReceipts e.deliveries (tree.compile.creditCell l))) ∧
      ∀ v (other : CrossingExecution θ compiled.route start v), CrossingCompleteThrough other T →
        ∃ native : Execution θ compiled.route start v, native.toWeak = other.execution ∧
          v.ObservationalEq final ∧ native.deliveries.Perm e.deliveries ∧
          ∀ i, other.execution.emissionTimes i = e.emissionTimes i := by
  let tree := nativeNeedSearchTree K action
  obtain ⟨final, e, crossing, same, done, effects, _, every⟩ :=
    compile_calibrated_decision_tree tree ⟨0, positive⟩ time h θ box
  have selected := effects (tree.select h)
  have reached : (tree.select h).reached h = true := ((tree.select h).reached_iff h).mpr rfl
  rw [reached, native_need_search_selects action h] at selected
  refine ⟨final, e, crossing, same, done, selected, ?_, every⟩
  intro l skipped
  have missed : l.reached h = false := Bool.eq_false_iff.mpr
    (fun reached => skipped ((l.reached_iff h).mp reached))
  have effect := effects l
  rw [missed] at effect
  exact effect

end RecursiveLearning.Native
