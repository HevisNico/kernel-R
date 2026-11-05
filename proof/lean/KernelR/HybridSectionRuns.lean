import KernelR.HybridDoseCounting

/-! Open-section automata for actual physical traces. An open run may be cut
inside a complete learning phase; closing it reconstructs its real section.
This interface supports flow subdivisions and interleaved foreign events. -/
namespace KernelR.Hybrid
open Set

inductive LearningSection where
  | error | mark
  deriving DecidableEq

def LearningSection.mode : LearningSection → AuxMode
  | .error => .error
  | .mark => .mark

def LearningSection.Inactive {n θ route s u} (kind : LearningSection)
    (move : @Move n θ route s u) (i : Fin n) (p : Port) : Prop :=
  match kind with
  | .error => move.ErrorInactive i p
  | .mark => move.MarkInactive i p

def LearningSection.Open {n θ s u} (kind : LearningSection)
    (flow : @Flow n θ s u) (i : Fin n) (p : Port) : Prop :=
  match kind with
  | .error => ErrorOpen flow i p
  | .mark => MarkOpen flow i p

def LearningSection.Valid {n} (kind : LearningSection) (i : Fin n) (p : Port)
    (active : Bool) (s : Snapshot n) : Prop :=
  active = true → s.aux i p = kind.mode

inductive SectionStep {n θ route} (kind : LearningSection) (i : Fin n) (p : Port) :
    {s u : Snapshot n} → Move θ route s u → Bool → Bool → ℕ → Prop
  | inactive {s u} (move : Move θ route s u) (h : kind.Inactive move i p) :
      SectionStep kind i p move false false 0
  | enter {s u} (jump : Jump route s u)
      (before : s.aux i p ≠ kind.mode) (after : u.aux i p = kind.mode) :
      SectionStep kind i p (.jump jump) false true 0
  | flow {s u} (f : Flow θ s u) (exposed : kind.Open f i p) :
      SectionStep kind i p (.flow f) true true 0
  | jump {s u} (j : Jump route s u)
      (before : s.aux i p = kind.mode) (after : u.aux i p = kind.mode) :
      SectionStep kind i p (.jump j) true true 0
  | exit {s u} (jump : Jump route s u)
      (before : s.aux i p = kind.mode) (after : u.aux i p ≠ kind.mode) :
      SectionStep kind i p (.jump jump) true false 1

inductive SectionRun {n θ route} (kind : LearningSection) (i : Fin n) (p : Port) :
    {s u : Snapshot n} → Execution θ route s u → Bool → Bool → ℕ → Prop
  | nil (s) (active : Bool) (valid : kind.Valid i p active s) :
      SectionRun kind i p (.nil s) active active 0
  | cons {s v u} {move : Move θ route s v} {rest : Execution θ route v u}
      {first middle last : Bool} {stepCount tailCount : ℕ}
      (step : SectionStep kind i p move first middle stepCount)
      (tail : SectionRun kind i p rest middle last tailCount) :
      SectionRun kind i p (.cons move rest) first last (stepCount + tailCount)

theorem LearningSection.Open.aux {n θ s u i p} {kind : LearningSection}
    {flow : @Flow n θ s u} (h : kind.Open flow i p) : s.aux i p = kind.mode := by
  cases kind <;> exact h.1

theorem SectionStep.initial_valid {n θ route kind i p s u a b k}
    {move : @Move n θ route s u} (step : SectionStep kind i p move a b k) :
    kind.Valid i p a s := by
  cases step with
  | inactive | enter => simp [LearningSection.Valid]
  | flow f exposed => exact fun _ => exposed.aux
  | jump j before after => exact fun _ => before
  | exit j before after => exact fun _ => before

theorem SectionStep.final_valid {n θ route kind i p s u a b k}
    {move : @Move n θ route s u} (step : SectionStep kind i p move a b k) :
    kind.Valid i p b u := by
  cases step with
  | inactive | exit => simp [LearningSection.Valid]
  | enter j before after => exact fun _ => after
  | flow f exposed =>
    intro _
    rw [f.aux_fixed]
    exact exposed.aux
  | jump j before after => exact fun _ => after

theorem SectionStep.flow_flags {n θ route kind i p s u a b k}
    {f : @Flow n θ s u} (step : SectionStep (route:=route) kind i p (.flow f) a b k) :
    a = b ∧ k = 0 := by
  cases step <;> exact ⟨rfl, rfl⟩

/-- A foreign event that retains this port's auxiliary mode is a zero-count
step, including when a counted learning section is currently open. -/
theorem SectionStep.same_aux_jump {n θ route i p s u active} {kind : LearningSection}
    (jump : @Jump n route s u) (valid : kind.Valid i p active s)
    (same : u.aux i p = s.aux i p) :
    SectionStep (θ:=θ) kind i p (.jump jump) active active 0 := by
  cases active with
  | false =>
    apply SectionStep.inactive
    cases kind <;> trivial
  | true => exact .jump jump (valid rfl) (same.trans (valid rfl))

theorem SectionRun.initial_valid {n θ route kind i p s u a b k}
    {e : @Execution n θ route s u} (run : SectionRun kind i p e a b k) :
    kind.Valid i p a s := by
  cases run with
  | nil s active valid => exact valid
  | cons step tail => exact step.initial_valid

theorem SectionRun.final_valid {n θ route kind i p s u a b k}
    {e : @Execution n θ route s u} (run : SectionRun kind i p e a b k) :
    kind.Valid i p b u := by
  induction run with
  | nil s active valid => exact valid
  | cons step tail ih => exact ih

theorem SectionRun.append {n θ route kind i p s v u a b c k l}
    {first : @Execution n θ route s v} {rest : Execution θ route v u}
    (left : SectionRun kind i p first a b k) (right : SectionRun kind i p rest b c l) :
    SectionRun kind i p (first.append rest) a c (k+l) := by
  induction left with
  | nil => simpa only [Execution.append, zero_add] using right
  | cons step tail ih =>
    simpa only [Execution.append, Nat.add_assoc] using SectionRun.cons step (ih right)

theorem SectionRun.cons_iff {n θ route kind i p s v u a c k}
    {move : @Move n θ route s v} {rest : Execution θ route v u} :
    SectionRun kind i p (.cons move rest) a c k ↔
      ∃ b stepCount tailCount, k = stepCount+tailCount ∧
        SectionStep kind i p move a b stepCount ∧ SectionRun kind i p rest b c tailCount := by
  constructor
  · intro run
    cases run with
    | cons step tail => exact ⟨_, _, _, rfl, step, tail⟩
  · rintro ⟨b, stepCount, tailCount, rfl, step, tail⟩
    exact .cons step tail

theorem SectionRun.nil_iff {n θ route kind i p s a b k} :
    SectionRun (n:=n) (θ:=θ) (route:=route) kind i p (.nil s) a b k ↔
      a = b ∧ k = 0 ∧ kind.Valid i p a s := by
  constructor
  · intro run
    cases run with
    | nil s active valid => exact ⟨rfl, rfl, valid⟩
  · rintro ⟨rfl, rfl, valid⟩
    exact .nil s _ valid

def LearningSection.Exposed {n θ route s u} (kind : LearningSection)
    (e : @Execution n θ route s u) (i : Fin n) (p : Port) : Prop :=
  match kind with
  | .error => e.ErrorExposed i p
  | .mark => e.MarkExposed i p

def LearningSection.Cover {n θ route s u} (kind : LearningSection)
    (i : Fin n) (p : Port) (e : @Execution n θ route s u) : Type :=
  match kind with
  | .error => ErrorSectionCover i p e
  | .mark => MarkSectionCover i p e

def LearningSection.coverCount {n θ route s u} (kind : LearningSection)
    {i : Fin n} {p : Port} {e : @Execution n θ route s u} : kind.Cover i p e → ℕ :=
  match kind with
  | .error => ErrorSectionCover.count
  | .mark => MarkSectionCover.count

structure ClosedSectionCover {n θ route s u} (kind : LearningSection)
    (i : Fin n) (p : Port) (e : @Execution n θ route s u) (count : ℕ) where
  cover : kind.Cover i p e
  count_eq : kind.coverCount cover = count

/-- The trace starts inside one exposed section. Its real exit is retained,
and everything after that exit already has a closed complete-section cover. -/
structure OpenSectionCover {n θ route s u} (kind : LearningSection)
    (i : Fin n) (p : Port) (e : @Execution n θ route s u) (count : ℕ) where
  middle : Snapshot n
  after : Snapshot n
  span : Execution θ route s middle
  exit : Jump route middle after
  rest : Execution θ route after u
  phase : span.AllStates (fun v => v.aux i p = kind.mode)
  exposed : kind.Exposed span i p
  departed : after.aux i p ≠ kind.mode
  tail : kind.Cover i p rest
  count_eq : count = kind.coverCount tail + 1
  reconstruct : e = span.append (.cons (.jump exit) rest)

def SectionRunResult {n θ route s u} (kind : LearningSection)
    (i : Fin n) (p : Port) (e : @Execution n θ route s u) (active : Bool) (count : ℕ) : Type :=
  if active then OpenSectionCover kind i p e count else ClosedSectionCover kind i p e count

theorem ClosedSectionCover.nil {n θ route kind i p s} :
    Nonempty (ClosedSectionCover (θ:=θ) (route:=route) (n:=n) kind i p (.nil s) 0) := by
  cases kind
  · exact ⟨⟨.nil _, rfl⟩⟩
  · exact ⟨⟨.nil _, rfl⟩⟩

theorem ClosedSectionCover.inactive {n θ route kind i p s v u k}
    (move : @Move n θ route s v) {rest : Execution θ route v u}
    (h : kind.Inactive move i p) (tail : ClosedSectionCover kind i p rest k) :
    Nonempty (ClosedSectionCover kind i p (.cons move rest) k) := by
  cases kind
  · exact ⟨⟨.inactive move rest h tail.cover, tail.count_eq⟩⟩
  · exact ⟨⟨.inactive move rest h tail.cover, tail.count_eq⟩⟩

theorem OpenSectionCover.enter {n θ route kind i p s v u k}
    (entry : @Jump n route s v) {rest : Execution θ route v u}
    (before : s.aux i p ≠ kind.mode) (entered : v.aux i p = kind.mode)
    (tail : OpenSectionCover kind i p rest k) :
    Nonempty (ClosedSectionCover kind i p (.cons (.jump entry) rest) k) := by
  rcases tail with ⟨middle, after, span, exit, suffix, phase, exposed, departed,
    cover, count_eq, rfl⟩
  have leaving := span.allStates_final phase
  cases kind
  · exact ⟨⟨.fullPhase entry span exit suffix before entered leaving departed phase exposed cover,
      count_eq.symm⟩⟩
  · exact ⟨⟨.fullPhase entry span exit suffix before entered leaving departed phase exposed cover,
      count_eq.symm⟩⟩

theorem OpenSectionCover.prepend_flow {n θ route kind i p s v u k}
    (flow : @Flow n θ s v) {rest : Execution θ route v u}
    (exposed : kind.Open flow i p) (tail : OpenSectionCover kind i p rest k) :
    Nonempty (OpenSectionCover kind i p (.cons (.flow flow) rest) k) := by
  refine ⟨{
    middle := tail.middle, after := tail.after
    span := .cons (.flow flow) tail.span, exit := tail.exit, rest := tail.rest
    phase := ⟨exposed.aux, tail.phase⟩
    exposed := ?_, departed := tail.departed, tail := tail.tail
    count_eq := tail.count_eq, reconstruct := ?_
  }⟩
  · cases kind <;> exact ⟨exposed, tail.exposed⟩
  · exact congrArg (Execution.cons (.flow flow)) tail.reconstruct

theorem OpenSectionCover.prepend_jump {n θ route kind i p s v u k}
    (jump : @Jump n route s v) {rest : Execution θ route v u}
    (before : s.aux i p = kind.mode) (tail : OpenSectionCover kind i p rest k) :
    Nonempty (OpenSectionCover kind i p (.cons (.jump jump) rest) k) := by
  refine ⟨{
    middle := tail.middle, after := tail.after
    span := .cons (.jump jump) tail.span, exit := tail.exit, rest := tail.rest
    phase := ⟨before, tail.phase⟩
    exposed := ?_, departed := tail.departed, tail := tail.tail
    count_eq := tail.count_eq, reconstruct := ?_
  }⟩
  · cases kind <;> exact tail.exposed
  · exact congrArg (Execution.cons (.jump jump)) tail.reconstruct

theorem OpenSectionCover.of_exit {n θ route kind i p s v u k}
    (exit : @Jump n route s v) {rest : Execution θ route v u}
    (before : s.aux i p = kind.mode) (after : v.aux i p ≠ kind.mode)
    (tail : ClosedSectionCover kind i p rest k) :
    Nonempty (OpenSectionCover kind i p (.cons (.jump exit) rest) (1+k)) := by
  refine ⟨{
    middle := s, after := v, span := .nil s, exit := exit, rest := rest
    phase := before, exposed := ?_, departed := after, tail := tail.cover
    count_eq := by rw [tail.count_eq]; omega
    reconstruct := rfl
  }⟩
  cases kind <;> trivial

/-- Closing the automaton reconstructs actual complete entry/span/exit covers.
No equation about a memory increment is a premise of this extraction. -/
theorem SectionRun.to_result {n θ route kind i p s u active last count}
    {e : @Execution n θ route s u} (run : SectionRun kind i p e active last count)
    (closed : last = false) :
    Nonempty (SectionRunResult kind i p e active count) := by
  induction run with
  | nil s active valid => subst active; exact ClosedSectionCover.nil
  | cons step tail ih =>
    have result := ih closed
    cases step with
    | inactive move h =>
      obtain ⟨covered⟩ := result
      simpa [SectionRunResult] using ClosedSectionCover.inactive _ h covered
    | enter jump before after =>
      obtain ⟨covered⟩ := result
      simpa [SectionRunResult] using OpenSectionCover.enter jump before after covered
    | flow f exposed =>
      obtain ⟨covered⟩ := result
      simpa [SectionRunResult] using OpenSectionCover.prepend_flow f exposed covered
    | jump j before after =>
      obtain ⟨covered⟩ := result
      simpa [SectionRunResult] using OpenSectionCover.prepend_jump j before covered
    | exit jump before after =>
      obtain ⟨covered⟩ := result
      exact OpenSectionCover.of_exit jump before after covered

theorem SectionRun.to_cover {n θ route kind i p s u count}
    {e : @Execution n θ route s u} (run : SectionRun kind i p e false false count) :
    Nonempty (ClosedSectionCover kind i p e count) := run.to_result rfl

theorem LearningSection.exposed_run {n θ route kind i p s u}
    (e : @Execution n θ route s u)
    (phase : e.AllStates (fun v => v.aux i p = kind.mode))
    (exposed : kind.Exposed e i p) : SectionRun kind i p e true true 0 := by
  induction e with
  | nil => exact .nil _ true (fun _ => phase)
  | cons move rest ih =>
    cases move with
    | flow f =>
      have hopen : kind.Open f i p := by cases kind <;> exact exposed.1
      have htail : kind.Exposed rest i p := by cases kind <;> exact exposed.2
      exact .cons (.flow f hopen) (ih phase.2 htail)
    | jump j =>
      have htail : kind.Exposed rest i p := by cases kind <;> exact exposed
      exact .cons (.jump j phase.1 (rest.allStates_initial phase.2)) (ih phase.2 htail)

theorem ErrorSectionCover.sectionRun {n θ route i p s u}
    {e : @Execution n θ route s u} (cover : ErrorSectionCover i p e) :
    SectionRun .error i p e false false cover.count := by
  induction cover with
  | nil s => exact .nil s false (by simp [LearningSection.Valid])
  | inactive move rest physical tail ih =>
    simpa only [ErrorSectionCover.count, zero_add] using
      SectionRun.cons (SectionStep.inactive (kind:=.error) move physical) ih
  | fullPhase entry span exit rest before entered leaving after phase exposed tail ih =>
    have middle : SectionRun .error i p span true true 0 :=
      LearningSection.exposed_run span phase exposed
    have result := SectionRun.cons (SectionStep.enter entry before entered)
      (middle.append (SectionRun.cons (SectionStep.exit exit leaving after) ih))
    simpa only [ErrorSectionCover.count, zero_add, Nat.add_comm] using result

theorem MarkSectionCover.sectionRun {n θ route i p s u}
    {e : @Execution n θ route s u} (cover : MarkSectionCover i p e) :
    SectionRun .mark i p e false false cover.count := by
  induction cover with
  | nil s => exact .nil s false (by simp [LearningSection.Valid])
  | inactive move rest physical tail ih =>
    simpa only [MarkSectionCover.count, zero_add] using
      SectionRun.cons (SectionStep.inactive (kind:=.mark) move physical) ih
  | fullPhase entry span exit rest before entered leaving after phase exposed tail ih =>
    have middle : SectionRun .mark i p span true true 0 :=
      LearningSection.exposed_run span phase exposed
    have result := SectionRun.cons (SectionStep.enter entry before entered)
      (middle.append (SectionRun.cons (SectionStep.exit exit leaving after) ih))
    simpa only [MarkSectionCover.count, zero_add, Nat.add_comm] using result

theorem error_section_run_iff {n θ route i p s u count}
    {e : @Execution n θ route s u} :
    SectionRun .error i p e false false count ↔
      ∃ cover : ErrorSectionCover i p e, cover.count = count := by
  constructor
  · intro run
    obtain ⟨covered⟩ := run.to_cover
    exact ⟨covered.cover, covered.count_eq⟩
  · rintro ⟨cover, rfl⟩
    exact cover.sectionRun

theorem mark_section_run_iff {n θ route i p s u count}
    {e : @Execution n θ route s u} :
    SectionRun .mark i p e false false count ↔
      ∃ cover : MarkSectionCover i p e, cover.count = count := by
  constructor
  · intro run
    obtain ⟨covered⟩ := run.to_cover
    exact ⟨covered.cover, covered.count_eq⟩
  · rintro ⟨cover, rfl⟩
    exact cover.sectionRun

end KernelR.Hybrid
