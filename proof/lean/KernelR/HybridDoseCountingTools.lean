import KernelR.HybridDoseCounting

/-! Constructive operations on actual-trace section covers. None of these
constructors uses an endpoint memory or ledger equality to manufacture a cover.
-/
namespace KernelR.Hybrid

private theorem doseCover_append_assoc {n θ route s a b u}
    (first : @Execution n θ route s a) (middle : Execution θ route a b)
    (last : Execution θ route b u) :
    (first.append middle).append last = first.append (middle.append last) := by
  induction first with
  | nil => rfl
  | cons move rest ih => simp only [Execution.append, ih]

noncomputable def ErrorSectionCover.append {n θ route i p s v u}
    {first : @Execution n θ route s v} {last : Execution θ route v u}
    (left : ErrorSectionCover i p first) (right : ErrorSectionCover i p last) :
    ErrorSectionCover i p (first.append last) := by
  induction left with
  | nil => exact right
  | inactive move rest physical tail ih =>
    exact .inactive move (rest.append last) physical (ih right)
  | fullPhase entry span exit rest before entered leaving after phase exposed tail ih =>
    simpa only [Execution.append, doseCover_append_assoc] using
      (ErrorSectionCover.fullPhase entry span exit (rest.append last)
        before entered leaving after phase exposed (ih right))

noncomputable def MarkSectionCover.append {n θ route i p s v u}
    {first : @Execution n θ route s v} {last : Execution θ route v u}
    (left : MarkSectionCover i p first) (right : MarkSectionCover i p last) :
    MarkSectionCover i p (first.append last) := by
  induction left with
  | nil => exact right
  | inactive move rest physical tail ih =>
    exact .inactive move (rest.append last) physical (ih right)
  | fullPhase entry span exit rest before entered leaving after phase exposed tail ih =>
    simpa only [Execution.append, doseCover_append_assoc] using
      (MarkSectionCover.fullPhase entry span exit (rest.append last)
        before entered leaving after phase exposed (ih right))

theorem ErrorSectionCover.count_append {n θ route i p s v u}
    {first : @Execution n θ route s v} {last : Execution θ route v u}
    (left : ErrorSectionCover i p first) (right : ErrorSectionCover i p last) :
    (left.append right).count = left.count + right.count := by
  have h := (left.append right).ledger_eq
  rw [Execution.dose_error_append, left.ledger_eq, right.ledger_eq] at h
  have he : ((left.append right).count : ℝ) = (left.count + right.count : ℕ) := by
    push_cast
    linarith
  exact_mod_cast he

theorem MarkSectionCover.count_append {n θ route i p s v u}
    {first : @Execution n θ route s v} {last : Execution θ route v u}
    (left : MarkSectionCover i p first) (right : MarkSectionCover i p last) :
    (left.append right).count = left.count + right.count := by
  have h := (left.append right).ledger_eq
  rw [Execution.dose_mark_append, left.ledger_eq, right.ledger_eq] at h
  have he : ((left.append right).count : ℝ) = (left.count + right.count : ℕ) := by
    push_cast
    linarith
  exact_mod_cast he

noncomputable def Execution.errorCover_of_inactive {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (inactive : e.AllFlows (fun {v w} (_ : Flow θ v w) =>
      v.aux i p ≠ .error ∨ v.main i ≠ .ready)) : ErrorSectionCover i p e := by
  induction e with
  | nil s => exact .nil s
  | cons move rest ih =>
    cases move with
    | flow f => exact .inactive (.flow f) rest inactive.1 (ih inactive.2)
    | jump j => exact .inactive (.jump j) rest trivial (ih inactive)

noncomputable def Execution.markCover_of_inactive {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (inactive : e.AllFlows (fun {v w} (_ : Flow θ v w) =>
      v.aux i p ≠ .mark ∨ v.main i = .ready)) : MarkSectionCover i p e := by
  induction e with
  | nil s => exact .nil s
  | cons move rest ih =>
    cases move with
    | flow f => exact .inactive (.flow f) rest inactive.1 (ih inactive.2)
    | jump j => exact .inactive (.jump j) rest trivial (ih inactive)

theorem Execution.errorCover_of_inactive_count {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (inactive : e.AllFlows (fun {v w} (_ : Flow θ v w) =>
      v.aux i p ≠ .error ∨ v.main i ≠ .ready)) :
    (e.errorCover_of_inactive i p inactive).count = 0 := by
  induction e with
  | nil => rfl
  | cons move rest ih =>
    cases move with
    | flow f => exact ih inactive.2
    | jump j => exact ih inactive

theorem Execution.markCover_of_inactive_count {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (inactive : e.AllFlows (fun {v w} (_ : Flow θ v w) =>
      v.aux i p ≠ .mark ∨ v.main i = .ready)) :
    (e.markCover_of_inactive i p inactive).count = 0 := by
  induction e with
  | nil => rfl
  | cons move rest ih =>
    cases move with
    | flow f => exact ih inactive.2
    | jump j => exact ih inactive

theorem Execution.error_inactive_of_auxFlows {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port) (mode : AuxMode)
    (different : mode ≠ .error) (modes : e.AuxFlows i p mode) :
    e.AllFlows (fun {v w} (_ : Flow θ v w) =>
      v.aux i p ≠ .error ∨ v.main i ≠ .ready) := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow f => exact ⟨Or.inl (by rw [modes.1]; exact different), ih modes.2⟩
    | jump j => exact ih modes

theorem Execution.mark_inactive_of_auxFlows {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port) (mode : AuxMode)
    (different : mode ≠ .mark) (modes : e.AuxFlows i p mode) :
    e.AllFlows (fun {v w} (_ : Flow θ v w) =>
      v.aux i p ≠ .mark ∨ v.main i = .ready) := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow f => exact ⟨Or.inl (by rw [modes.1]; exact different), ih modes.2⟩
    | jump j => exact ih modes

theorem Execution.error_inactive_of_protected {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (modes : e.AllStates (fun v => v.main i ≠ .ready)) :
    e.AllFlows (fun {v w} (_ : Flow θ v w) =>
      v.aux i p ≠ .error ∨ v.main i ≠ .ready) := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow f => exact ⟨Or.inr modes.1, ih modes.2⟩
    | jump j => exact ih modes.2

theorem Execution.error_inactive_of_mainFlows {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port) (mode : MainMode)
    (different : mode ≠ .ready) (modes : e.MainFlows i mode) :
    e.AllFlows (fun {v w} (_ : Flow θ v w) =>
      v.aux i p ≠ .error ∨ v.main i ≠ .ready) := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow f => exact ⟨Or.inr (by rw [modes.1]; exact different), ih modes.2⟩
    | jump j => exact ih modes

theorem Execution.mark_inactive_of_ready {n θ route s u}
    (e : @Execution n θ route s u) (i : Fin n) (p : Port)
    (modes : e.MainFlows i .ready) :
    e.AllFlows (fun {v w} (_ : Flow θ v w) =>
      v.aux i p ≠ .mark ∨ v.main i = .ready) := by
  induction e with
  | nil => trivial
  | cons move rest ih =>
    cases move with
    | flow f => exact ⟨Or.inr modes.1, ih modes.2⟩
    | jump j => exact ih modes

noncomputable def ErrorSectionCover.single {n θ route i p s a b c}
    (entry : @Jump n route s a) (span : Execution θ route a b)
    (exit : Jump route b c)
    (before : s.aux i p ≠ .error) (entered : a.aux i p = .error)
    (leaving : b.aux i p = .error) (after : c.aux i p ≠ .error)
    (phase : span.AllStates (fun v => v.aux i p = .error))
    (exposed : span.ErrorExposed i p) :
    ErrorSectionCover i p
      (.cons (.jump entry) (span.append (.cons (.jump exit) (.nil c)))) :=
  .fullPhase entry span exit (.nil c) before entered leaving after phase exposed (.nil c)

@[simp] theorem ErrorSectionCover.count_single {n θ route i p s a b c}
    (entry : @Jump n route s a) (span : Execution θ route a b)
    (exit : Jump route b c)
    (before : s.aux i p ≠ .error) (entered : a.aux i p = .error)
    (leaving : b.aux i p = .error) (after : c.aux i p ≠ .error)
    (phase : span.AllStates (fun v => v.aux i p = .error))
    (exposed : span.ErrorExposed i p) :
    (ErrorSectionCover.single entry span exit before entered leaving after phase exposed).count = 1 := rfl

noncomputable def MarkSectionCover.single {n θ route i p s a b c}
    (entry : @Jump n route s a) (span : Execution θ route a b)
    (exit : Jump route b c)
    (before : s.aux i p ≠ .mark) (entered : a.aux i p = .mark)
    (leaving : b.aux i p = .mark) (after : c.aux i p ≠ .mark)
    (phase : span.AllStates (fun v => v.aux i p = .mark))
    (exposed : span.MarkExposed i p) :
    MarkSectionCover i p
      (.cons (.jump entry) (span.append (.cons (.jump exit) (.nil c)))) :=
  .fullPhase entry span exit (.nil c) before entered leaving after phase exposed (.nil c)

@[simp] theorem MarkSectionCover.count_single {n θ route i p s a b c}
    (entry : @Jump n route s a) (span : Execution θ route a b)
    (exit : Jump route b c)
    (before : s.aux i p ≠ .mark) (entered : a.aux i p = .mark)
    (leaving : b.aux i p = .mark) (after : c.aux i p ≠ .mark)
    (phase : span.AllStates (fun v => v.aux i p = .mark))
    (exposed : span.MarkExposed i p) :
    (MarkSectionCover.single entry span exit before entered leaving after phase exposed).count = 1 := rfl

end KernelR.Hybrid
