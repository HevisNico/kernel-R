import KernelR.HybridFlow
import KernelR.HybridExecutionTools

/-! Whole-execution counting of complete, exposed learning sections.

The covers below decompose an actual `Execution`, not an assumed learning
ledger. Each counted section contains its actual entry jump, all intermediate
states in the auxiliary mode, exposed integral flows, and its actual exit jump.
Uncounted moves are inactive for physical mode reasons. In particular, an
active partial section cannot be hidden in a zero-ledger premise.

The covers are independent for each cell and port. Simultaneous events and
overlapping MARK phases on different ports are retained. Counts concern
complete exposed phases, not arbitrary inputs, failures or threshold touches.
-/
namespace KernelR.Hybrid
open Set MeasureTheory

/-- No ERROR actuation is possible on this move, for a structural mode reason.
Clipping or a closed energy gate is deliberately not an inactivity witness. -/
def Move.ErrorInactive {n θ route s u} (move : @Move n θ route s u)
    (i : Fin n) (p : Port) : Prop :=
  match move with
  | .flow _ => s.aux i p ≠ .error ∨ s.main i ≠ .ready
  | .jump _ => True

/-- No MARK actuation is possible on this move, for a structural mode reason. -/
def Move.MarkInactive {n θ route s u} (move : @Move n θ route s u)
    (i : Fin n) (p : Port) : Prop :=
  match move with
  | .flow _ => s.aux i p ≠ .mark ∨ s.main i = .ready
  | .jump _ => True

theorem Move.error_zero_of_inactive {n θ route s u}
    (move : @Move n θ route s u) (i : Fin n) (p : Port)
    (inactive : move.ErrorInactive i p) : move.ledger.error i p = 0 := by
  cases move with
  | flow f =>
    rcases inactive with haux | hmain
    · simp [Move.ledger, Flow.ledger, errorAct, haux]
    · simp [Move.ledger, Flow.ledger, errorAct, hmain]
  | jump j => exact j.no_actuation.1 i p

theorem Move.mark_zero_of_inactive {n θ route s u}
    (move : @Move n θ route s u) (i : Fin n) (p : Port)
    (inactive : move.MarkInactive i p) : move.ledger.mark i p = 0 := by
  cases move with
  | flow f =>
    rcases inactive with haux | hmain
    · simp [Move.ledger, Flow.ledger, markAct, haux]
    · simp [Move.ledger, Flow.ledger, markAct, hmain]
  | jump j => exact j.no_mark_actuation i p

/-- Exact decomposition of the actual trace into inactive moves and complete
ERROR sections at a particular cell/port. No dose equality is a constructor
premise. The `section` constructor records real mode-changing jumps. -/
inductive ErrorSectionCover {n : ℕ} {θ : Fin n → Parameters} {route : Router n}
    (i : Fin n) (p : Port) :
    {s u : Snapshot n} → Execution θ route s u → Type
  | nil (s) : ErrorSectionCover i p (.nil s)
  | inactive {s v u} (move : Move θ route s v) (rest : Execution θ route v u)
      (physical : move.ErrorInactive i p) (tail : ErrorSectionCover i p rest) :
      ErrorSectionCover i p (.cons move rest)
  | section {s a b c u}
      (entry : Jump route s a) (span : Execution θ route a b)
      (exit : Jump route b c) (rest : Execution θ route c u)
      (before : s.aux i p ≠ .error) (entered : a.aux i p = .error)
      (leaving : b.aux i p = .error) (after : c.aux i p ≠ .error)
      (phase : span.AllStates (fun v => v.aux i p = .error))
      (exposed : span.ErrorExposed i p) (tail : ErrorSectionCover i p rest) :
      ErrorSectionCover i p
        (.cons (.jump entry) (span.append (.cons (.jump exit) rest)))

/-- Exact decomposition of the actual trace into inactive moves and complete
protected MARK sections. Covers for separate ports may overlap in time. -/
inductive MarkSectionCover {n : ℕ} {θ : Fin n → Parameters} {route : Router n}
    (i : Fin n) (p : Port) :
    {s u : Snapshot n} → Execution θ route s u → Type
  | nil (s) : MarkSectionCover i p (.nil s)
  | inactive {s v u} (move : Move θ route s v) (rest : Execution θ route v u)
      (physical : move.MarkInactive i p) (tail : MarkSectionCover i p rest) :
      MarkSectionCover i p (.cons move rest)
  | section {s a b c u}
      (entry : Jump route s a) (span : Execution θ route a b)
      (exit : Jump route b c) (rest : Execution θ route c u)
      (before : s.aux i p ≠ .mark) (entered : a.aux i p = .mark)
      (leaving : b.aux i p = .mark) (after : c.aux i p ≠ .mark)
      (phase : span.AllStates (fun v => v.aux i p = .mark))
      (exposed : span.MarkExposed i p) (tail : MarkSectionCover i p rest) :
      MarkSectionCover i p
        (.cons (.jump entry) (span.append (.cons (.jump exit) rest)))

def ErrorSectionCover.count {n θ route i p s u} {e : @Execution n θ route s u} :
    ErrorSectionCover i p e → ℕ
  | .nil _ => 0
  | .inactive _ _ _ tail => tail.count
  | .section _ _ _ _ _ _ _ _ _ _ tail => tail.count + 1

def MarkSectionCover.count {n θ route i p s u} {e : @Execution n θ route s u} :
    MarkSectionCover i p e → ℕ
  | .nil _ => 0
  | .inactive _ _ _ tail => tail.count
  | .section _ _ _ _ _ _ _ _ _ _ tail => tail.count + 1

theorem Execution.dose_error_append {n θ route s v u}
    (segment : @Execution n θ route s v) (rest : Execution θ route v u)
    (i : Fin n) (p : Port) :
    (segment.append rest).ledger.error i p =
      segment.ledger.error i p + rest.ledger.error i p := by
  induction segment with
  | nil => simp [append, ledger, Ledger.zero]
  | cons move tail ih => simp only [append, ledger, Ledger.add, ih, add_assoc]

theorem Execution.dose_mark_append {n θ route s v u}
    (segment : @Execution n θ route s v) (rest : Execution θ route v u)
    (i : Fin n) (p : Port) :
    (segment.append rest).ledger.mark i p =
      segment.ledger.mark i p + rest.ledger.mark i p := by
  induction segment with
  | nil => simp [append, ledger, Ledger.zero]
  | cons move tail ih => simp only [append, ledger, Ledger.add, ih, add_assoc]

theorem ErrorSectionCover.ledger_eq {n θ route i p s u}
    {e : @Execution n θ route s u} (cover : ErrorSectionCover i p e) :
    e.ledger.error i p = (3 / 5 : ℝ) * cover.count := by
  induction cover with
  | nil s => simp [count, Execution.ledger, Ledger.zero]
  | inactive move rest physical tail ih =>
    change move.ledger.error i p + rest.ledger.error i p = _
    rw [move.error_zero_of_inactive i p physical, zero_add, ih]
    rfl
  | section entry span exit rest before entered leaving after phase exposed tail ih =>
    have hd := guarded_error_dose entry span exit i p before entered leaving after exposed
    simp only [Execution.ledger, Move.ledger, Ledger.add,
      entry.no_actuation.1, zero_add, Execution.dose_error_append,
      exit.no_actuation.1, hd, ih, count, Nat.cast_add, Nat.cast_one]
    ring

theorem MarkSectionCover.ledger_eq {n θ route i p s u}
    {e : @Execution n θ route s u} (cover : MarkSectionCover i p e) :
    e.ledger.mark i p = (1 / 10 : ℝ) * cover.count := by
  induction cover with
  | nil s => simp [count, Execution.ledger, Ledger.zero]
  | inactive move rest physical tail ih =>
    change move.ledger.mark i p + rest.ledger.mark i p = _
    rw [move.mark_zero_of_inactive i p physical, zero_add, ih]
    rfl
  | section entry span exit rest before entered leaving after phase exposed tail ih =>
    have hd := guarded_mark_dose entry span exit i p before entered leaving after exposed
    simp only [Execution.ledger, Move.ledger, Ledger.add,
      entry.no_mark_actuation, zero_add, Execution.dose_mark_append,
      exit.no_mark_actuation, hd, ih, count, Nat.cast_add, Nat.cast_one]
    ring

/-- The count is independent of the choice of valid actual-trace cover. -/
theorem ErrorSectionCover.count_unique {n θ route i p s u}
    {e : @Execution n θ route s u} (left right : ErrorSectionCover i p e) :
    left.count = right.count := by
  have h := left.ledger_eq.symm.trans right.ledger_eq
  have hc : (left.count : ℝ) = right.count := by linarith
  exact_mod_cast hc

theorem MarkSectionCover.count_unique {n θ route i p s u}
    {e : @Execution n θ route s u} (left right : MarkSectionCover i p e) :
    left.count = right.count := by
  have h := left.ledger_eq.symm.trans right.ledger_eq
  have hc : (left.count : ℝ) = right.count := by linarith
  exact_mod_cast hc

/-- Explicit whole-trace energy and headroom hypotheses. These inequalities
hold on every actual flow, including both endpoints, for all cells and ports.
The inactive constructors cannot use failure of one of these gates. -/
def LearningGatesOpen {n θ route s u} (e : @Execution n θ route s u) : Prop :=
  e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, ∀ i,
    0 < f.path t i .energy ∧ f.path t i .b < 11 / 10 ∧
      ∀ p, f.path t i (.z p) < Real.log ((θ i).cap p))

/-- Whole-execution counting. No fabrication parameter or event date occurs
in the resulting memory increments. The actual counts may depend on them.
This algebraic statement needs no physical box: exposure is checked on the
observed sections themselves. The birth headline below displays that scope. -/
theorem Execution.memory_of_section_covers {n θ route s u}
    (e : @Execution n θ route s u)
    (errors : ∀ i p, ErrorSectionCover i p e)
    (marks : ∀ i p, MarkSectionCover i p e) :
    (∀ i p, u.x i (.z p) = s.x i (.z p) + (3 / 5 : ℝ) * (errors i p).count) ∧
    (∀ i, u.x i .b = s.x i .b + (1 / 10 : ℝ) *
      (∑ p : Port, (marks i p).count : ℕ)) := by
  constructor
  · intro i p
    rw [e.gain_balance i p, (errors i p).ledger_eq]
  · intro i
    have hm : e.ledger.recovery i =
        (1 / 10 : ℝ) * ∑ p : Port, ((marks i p).count : ℝ) := by
      rw [e.recovery_sum_marks i]
      calc
        (∑ p : Port, e.ledger.mark i p) =
            ∑ p : Port, (1 / 10 : ℝ) * ((marks i p).count : ℝ) :=
          Finset.sum_congr rfl (fun p _ => (marks i p).ledger_eq)
        _ = _ := (Finset.mul_sum _ _ _).symm
    rw [e.recovery_balance i, hm]
    simp only [Nat.cast_sum]

/-- For every fixed device in a physical box, a full birth-to-terminal trace
with no partial active learning sections has integer-counted memory increments.
READY auxiliary endpoints rule out initial or terminal unfinished cycles.
All-flow positive energy and strict headroom are explicit premises, not inferred
from the word 'complete'. These hypotheses do not establish protocol existence.
Birth uncertainty remains in the displayed birth values. -/
theorem from_birth_memory_of_section_covers {n θ route born u ε}
    (e : @Execution n θ route born u)
    (_box : PhysicalBox θ ε) (_birth : BirthState born)
    (_born_ready : ∀ i p, born.aux i p = .ready)
    (_terminal_ready : ∀ i p, u.aux i p = .ready)
    (_gates : LearningGatesOpen e)
    (errors : ∀ i p, ErrorSectionCover i p e)
    (marks : ∀ i p, MarkSectionCover i p e) :
    (∀ i p, u.x i (.z p) = born.x i (.z p) + (3 / 5 : ℝ) * (errors i p).count) ∧
    (∀ i, u.x i .b = born.x i .b + (1 / 10 : ℝ) *
      (∑ p : Port, (marks i p).count : ℕ)) :=
  e.memory_of_section_covers errors marks

/-- Equal actual section counts give equal memory increments across different
devices, event dates and birth offsets. Equality of the birth memories is not
required: only the increments, rather than the absolute memories, agree. -/
theorem same_increments_of_same_counts
    {n θ₁ θ₂ route₁ route₂ s₁ u₁ s₂ u₂}
    (left : @Execution n θ₁ route₁ s₁ u₁)
    (right : @Execution n θ₂ route₂ s₂ u₂)
    (leftErrors : ∀ i p, ErrorSectionCover i p left)
    (leftMarks : ∀ i p, MarkSectionCover i p left)
    (rightErrors : ∀ i p, ErrorSectionCover i p right)
    (rightMarks : ∀ i p, MarkSectionCover i p right)
    (errorCounts : ∀ i p, (leftErrors i p).count = (rightErrors i p).count)
    (markCounts : ∀ i,
      (∑ p : Port, (leftMarks i p).count) = ∑ p : Port, (rightMarks i p).count) :
    (∀ i p, u₁.x i (.z p) - s₁.x i (.z p) =
      u₂.x i (.z p) - s₂.x i (.z p)) ∧
    (∀ i, u₁.x i .b - s₁.x i .b = u₂.x i .b - s₂.x i .b) := by
  have hl := left.memory_of_section_covers leftErrors leftMarks
  have hr := right.memory_of_section_covers rightErrors rightMarks
  constructor
  · intro i p
    rw [hl.1 i p, hr.1 i p, errorCounts i p]
    ring
  · intro i
    rw [hl.2 i, hr.2 i, markCounts i]
    ring

/-- A protocol-independent invariance corollary: different fabrication
parameters, dates and traces give the same learned memories when the initial
memories and actual complete-section counts agree. -/
theorem same_memories_of_same_birth_and_counts
    {n θ₁ θ₂ route₁ route₂ s₁ u₁ s₂ u₂}
    (left : @Execution n θ₁ route₁ s₁ u₁)
    (right : @Execution n θ₂ route₂ s₂ u₂)
    (leftErrors : ∀ i p, ErrorSectionCover i p left)
    (leftMarks : ∀ i p, MarkSectionCover i p left)
    (rightErrors : ∀ i p, ErrorSectionCover i p right)
    (rightMarks : ∀ i p, MarkSectionCover i p right)
    (initialGain : ∀ i p, s₁.x i (.z p) = s₂.x i (.z p))
    (initialRecovery : ∀ i, s₁.x i .b = s₂.x i .b)
    (errorCounts : ∀ i p, (leftErrors i p).count = (rightErrors i p).count)
    (markCounts : ∀ i,
      (∑ p : Port, (leftMarks i p).count) = ∑ p : Port, (rightMarks i p).count) :
    (∀ i p, u₁.x i (.z p) = u₂.x i (.z p)) ∧
    (∀ i, u₁.x i .b = u₂.x i .b) := by
  have hl := left.memory_of_section_covers leftErrors leftMarks
  have hr := right.memory_of_section_covers rightErrors rightMarks
  constructor
  · intro i p
    rw [hl.1 i p, hr.1 i p, initialGain i p, errorCounts i p]
  · intro i
    rw [hl.2 i, hr.2 i, initialRecovery i, markCounts i]

#print axioms Execution.memory_of_section_covers
#print axioms from_birth_memory_of_section_covers
#print axioms same_increments_of_same_counts
#print axioms same_memories_of_same_birth_and_counts
#print axioms ErrorSectionCover.count_unique
#print axioms MarkSectionCover.count_unique

end KernelR.Hybrid
