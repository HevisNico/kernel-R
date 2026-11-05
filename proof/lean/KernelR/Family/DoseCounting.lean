import KernelR.Family.Refinement

/-! Exact counting for the parametric R family.

Adapted from KernelR/HybridDoseCounting.lean (Nicolas Breuillaud, CC BY 4.0).
Covers contain actual entry and exit jumps and completely exposed intervening
execution spans. The resulting dose is proved from the symbolic field and
thresholds; no equality of a ledger with a prescribed count is assumed.
-/
namespace KernelR.Family
open KernelR.Hybrid Set MeasureTheory
variable {cfg : Constants}

/-- No ERROR actuation is possible on this move, for a structural mode reason.
Clipping or a closed energy gate is deliberately not an inactivity witness. -/
def Move.ErrorInactive {n θ route s u} (move : @Move n cfg θ route s u)
    (i : Fin n) (p : Port) : Prop :=
  match move with
  | .flow _ => s.aux i p ≠ .error ∨ s.main i ≠ .ready
  | .jump _ => True

/-- No MARK actuation is possible on this move, for a structural mode reason. -/
def Move.MarkInactive {n θ route s u} (move : @Move n cfg θ route s u)
    (i : Fin n) (p : Port) : Prop :=
  match move with
  | .flow _ => s.aux i p ≠ .mark ∨ s.main i = .ready
  | .jump _ => True

theorem Move.error_zero_of_inactive {n θ route s u}
    (move : @Move n cfg θ route s u) (i : Fin n) (p : Port)
    (inactive : move.ErrorInactive i p) : move.ledger.error i p = 0 := by
  cases move with
  | flow f =>
    rcases inactive with haux | hmain
    · simp [Move.ledger, Flow.ledger, errorAct, haux]
    · simp [Move.ledger, Flow.ledger, errorAct, hmain]
  | jump j => exact j.no_actuation.1 i p

theorem Move.mark_zero_of_inactive {n θ route s u}
    (move : @Move n cfg θ route s u) (i : Fin n) (p : Port)
    (inactive : move.MarkInactive i p) : move.ledger.mark i p = 0 := by
  cases move with
  | flow f =>
    rcases inactive with haux | hmain
    · simp [Move.ledger, Flow.ledger, markAct, haux]
    · simp [Move.ledger, Flow.ledger, markAct, hmain]
  | jump j => exact j.no_mark_actuation i p

/-- Exact decomposition of the actual trace into inactive moves and complete
ERROR sections at a particular cell/port. No dose equality is a constructor
premise. The `fullPhase` constructor records real mode-changing jumps. -/
inductive ErrorSectionCover {n : ℕ} {θ : Fin n → Parameters} {route : Router n}
    (i : Fin n) (p : Port) :
    {s u : Snapshot n} → Execution cfg θ route s u → Type
  | nil (s) : ErrorSectionCover i p (.nil s)
  | inactive {s v u} (move : Move cfg θ route s v) (rest : Execution cfg θ route v u)
      (physical : move.ErrorInactive i p) (tail : ErrorSectionCover i p rest) :
      ErrorSectionCover i p (.cons move rest)
  | fullPhase {s a b c u}
      (entry : Jump cfg route s a) (span : Execution cfg θ route a b)
      (exit : Jump cfg route b c) (rest : Execution cfg θ route c u)
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
    {s u : Snapshot n} → Execution cfg θ route s u → Type
  | nil (s) : MarkSectionCover i p (.nil s)
  | inactive {s v u} (move : Move cfg θ route s v) (rest : Execution cfg θ route v u)
      (physical : move.MarkInactive i p) (tail : MarkSectionCover i p rest) :
      MarkSectionCover i p (.cons move rest)
  | fullPhase {s a b c u}
      (entry : Jump cfg route s a) (span : Execution cfg θ route a b)
      (exit : Jump cfg route b c) (rest : Execution cfg θ route c u)
      (before : s.aux i p ≠ .mark) (entered : a.aux i p = .mark)
      (leaving : b.aux i p = .mark) (after : c.aux i p ≠ .mark)
      (phase : span.AllStates (fun v => v.aux i p = .mark))
      (exposed : span.MarkExposed i p) (tail : MarkSectionCover i p rest) :
      MarkSectionCover i p
        (.cons (.jump entry) (span.append (.cons (.jump exit) rest)))

def ErrorSectionCover.count {n θ route i p s u} {e : @Execution n cfg θ route s u} :
    ErrorSectionCover i p e → ℕ
  | .nil _ => 0
  | .inactive _ _ _ tail => tail.count
  | .fullPhase _ _ _ _ _ _ _ _ _ _ tail => tail.count + 1

def MarkSectionCover.count {n θ route i p s u} {e : @Execution n cfg θ route s u} :
    MarkSectionCover i p e → ℕ
  | .nil _ => 0
  | .inactive _ _ _ tail => tail.count
  | .fullPhase _ _ _ _ _ _ _ _ _ _ tail => tail.count + 1

theorem Execution.dose_error_append {n θ route s v u}
    (segment : @Execution n cfg θ route s v) (rest : Execution cfg θ route v u)
    (i : Fin n) (p : Port) :
    (segment.append rest).ledger.error i p =
      segment.ledger.error i p + rest.ledger.error i p := by
  induction segment with
  | nil => simp [append, ledger, Ledger.zero]
  | cons move tail ih => simp only [append, ledger, Ledger.add, ih, add_assoc]

theorem Execution.dose_mark_append {n θ route s v u}
    (segment : @Execution n cfg θ route s v) (rest : Execution cfg θ route v u)
    (i : Fin n) (p : Port) :
    (segment.append rest).ledger.mark i p =
      segment.ledger.mark i p + rest.ledger.mark i p := by
  induction segment with
  | nil => simp [append, ledger, Ledger.zero]
  | cons move tail ih => simp only [append, ledger, Ledger.add, ih, add_assoc]

theorem ErrorSectionCover.ledger_eq {n θ route i p s u}
    {e : @Execution n cfg θ route s u} (cover : ErrorSectionCover i p e) :
    e.ledger.error i p = cfg.errorDose * cover.count := by
  induction cover with
  | nil s => simp [count, Execution.ledger, Ledger.zero]
  | inactive move rest physical tail ih =>
    change move.ledger.error i p + rest.ledger.error i p = _
    rw [move.error_zero_of_inactive i p physical, zero_add, ih]
    rfl
  | fullPhase entry span exit rest before entered leaving after phase exposed tail ih =>
    have hd := guarded_error_dose entry span exit i p before entered leaving after exposed
    simp only [Execution.ledger, Move.ledger, Ledger.add,
      entry.no_actuation.1, zero_add, Execution.dose_error_append,
      exit.no_actuation.1, hd, ih, count, Nat.cast_add, Nat.cast_one]
    ring

theorem MarkSectionCover.ledger_eq {n θ route i p s u}
    {e : @Execution n cfg θ route s u} (cover : MarkSectionCover i p e) :
    e.ledger.mark i p = cfg.markDose * cover.count := by
  induction cover with
  | nil s => simp [count, Execution.ledger, Ledger.zero]
  | inactive move rest physical tail ih =>
    change move.ledger.mark i p + rest.ledger.mark i p = _
    rw [move.mark_zero_of_inactive i p physical, zero_add, ih]
    rfl
  | fullPhase entry span exit rest before entered leaving after phase exposed tail ih =>
    have hd := guarded_mark_dose entry span exit i p before entered leaving after exposed
    simp only [Execution.ledger, Move.ledger, Ledger.add,
      entry.no_mark_actuation, zero_add, Execution.dose_mark_append,
      exit.no_mark_actuation, hd, ih, count, Nat.cast_add, Nat.cast_one]
    ring

/-- The count is independent of the choice of valid actual-trace cover. -/
theorem ErrorSectionCover.count_unique {n θ route i p s u}
    {e : @Execution n cfg θ route s u} (left right : ErrorSectionCover i p e) (dose : cfg.errorDose ≠ 0) :
    left.count = right.count := by
  have h := left.ledger_eq.symm.trans right.ledger_eq
  have hc : (left.count : ℝ) = right.count := mul_left_cancel₀ dose h
  exact_mod_cast hc

theorem MarkSectionCover.count_unique {n θ route i p s u}
    {e : @Execution n cfg θ route s u} (left right : MarkSectionCover i p e) (dose : cfg.markDose ≠ 0) :
    left.count = right.count := by
  have h := left.ledger_eq.symm.trans right.ledger_eq
  have hc : (left.count : ℝ) = right.count := mul_left_cancel₀ dose h
  exact_mod_cast hc

/-- Physical level ordering and a positive gain factor imply identifiable counts. -/
theorem ErrorSectionCover.count_unique_of_admissible {n θ route i p s u}
    {e : @Execution n cfg θ route s u} (left right : ErrorSectionCover i p e)
    (admissible : Admissible cfg) : left.count = right.count :=
  left.count_unique right (ne_of_gt admissible.errorDose_pos)

/-- Physical level ordering and a positive recovery factor imply identifiable counts. -/
theorem MarkSectionCover.count_unique_of_admissible {n θ route i p s u}
    {e : @Execution n cfg θ route s u} (left right : MarkSectionCover i p e)
    (admissible : Admissible cfg) : left.count = right.count :=
  left.count_unique right (ne_of_gt admissible.markDose_pos)

/-- Explicit whole-trace energy and headroom hypotheses. These inequalities
hold on every actual flow, including both endpoints, for all cells and ports.
The inactive constructors cannot use failure of one of these gates. -/
def LearningGatesOpen {n θ route s u} (e : @Execution n cfg θ route s u) : Prop :=
  e.AllFlows (fun {v w} f => ∀ t ∈ Icc v.time w.time, ∀ i,
    0 < f.path t i .energy ∧ f.path t i .b < cfg.recoveryCap ∧
      ∀ p, f.path t i (.z p) < Real.log ((θ i).cap p))

/-- Whole-execution counting. No fabrication parameter or event date occurs
in the resulting memory increments. The actual counts may depend on them.
This algebraic statement needs no physical box: exposure is checked on the
observed sections themselves, and all fixed cell constants remain symbolic. -/
theorem Execution.memory_of_section_covers {n θ route s u}
    (e : @Execution n cfg θ route s u)
    (errors : ∀ i p, ErrorSectionCover i p e)
    (marks : ∀ i p, MarkSectionCover i p e) :
    (∀ i p, u.x i (.z p) = s.x i (.z p) + cfg.errorDose * (errors i p).count) ∧
    (∀ i, u.x i .b = s.x i .b + cfg.markDose *
      (∑ p : Port, (marks i p).count : ℕ)) := by
  constructor
  · intro i p
    rw [e.gain_balance i p, (errors i p).ledger_eq]
  · intro i
    have hm : e.ledger.recovery i =
        cfg.markDose * ∑ p : Port, ((marks i p).count : ℝ) := by
      rw [e.recovery_sum_marks i]
      calc
        (∑ p : Port, e.ledger.mark i p) =
            ∑ p : Port, cfg.markDose * ((marks i p).count : ℝ) :=
          Finset.sum_congr rfl (fun p _ => (marks i p).ledger_eq)
        _ = _ := (Finset.mul_sum _ _ _).symm
    rw [e.recovery_balance i, hm]
    simp only [Nat.cast_sum]

/-- Equal actual section counts give equal memory increments across different
devices, event dates and birth offsets. Equality of the birth memories is not
required: only the increments, rather than the absolute memories, agree. -/
theorem same_increments_of_same_counts
    {n θ₁ θ₂ route₁ route₂ s₁ u₁ s₂ u₂}
    (left : @Execution n cfg θ₁ route₁ s₁ u₁)
    (right : @Execution n cfg θ₂ route₂ s₂ u₂)
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
    (left : @Execution n cfg θ₁ route₁ s₁ u₁)
    (right : @Execution n cfg θ₂ route₂ s₂ u₂)
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

/-- Different members of the family can be compared when their section doses
agree. Equal counts alone do not erase a change in the actuator/level product. -/
theorem same_increments_of_same_doses_and_counts
    {leftCfg rightCfg : Constants} {n θ₁ θ₂ route₁ route₂ s₁ u₁ s₂ u₂}
    (left : @Execution n leftCfg θ₁ route₁ s₁ u₁)
    (right : @Execution n rightCfg θ₂ route₂ s₂ u₂)
    (leftErrors : ∀ i p, ErrorSectionCover i p left)
    (leftMarks : ∀ i p, MarkSectionCover i p left)
    (rightErrors : ∀ i p, ErrorSectionCover i p right)
    (rightMarks : ∀ i p, MarkSectionCover i p right)
    (errorDose : leftCfg.errorDose = rightCfg.errorDose)
    (markDose : leftCfg.markDose = rightCfg.markDose)
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
    rw [hl.1 i p, hr.1 i p, errorDose, errorCounts i p]
    ring
  · intro i
    rw [hl.2 i, hr.2 i, markDose, markCounts i]
    ring

#print axioms Execution.memory_of_section_covers
#print axioms same_increments_of_same_counts
#print axioms same_memories_of_same_birth_and_counts
#print axioms ErrorSectionCover.count_unique
#print axioms MarkSectionCover.count_unique
#print axioms same_increments_of_same_doses_and_counts


end KernelR.Family
