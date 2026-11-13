import LearnedVariation.Learner

namespace LearnedVariation

structure WindowInvariant (p : Policy) (s : State) : Prop where
  empty : s.history = [] → s.validationSteps = 0 ∧ s.refinements = 0
  validating : s.mode = .validating → s.history ≠ [] →
    0 < s.remaining ∧ s.nextTime + s.remaining = s.windowStart + p.window + 1
  provisional : s.mode = .provisional →
    s.remaining = 0 ∧ s.windowStart + p.window < s.nextTime
  budget : s.validationSteps + s.remaining ≤ (s.refinements + 1) * p.window

theorem initial_window (p start budget) : WindowInvariant p (initial p start budget) := by
  constructor
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]

theorem charge_window {p s} (old : WindowInvariant p s) : WindowInvariant p (charge s) :=
  ⟨old.empty, old.validating, old.provisional, old.budget⟩

theorem stop_window {p s} (old : WindowInvariant p s) (mode : Mode)
    (notValidating : mode ≠ .validating) (notProvisional : mode ≠ .provisional) :
    WindowInvariant p { s with mode := mode } := by
  exact ⟨old.empty, by simp [notValidating], by simp [notProvisional], old.budget⟩

theorem accept_window {p s sample} (valid : p.Valid) (fresh : sample.time = s.nextTime)
    (old : WindowInvariant p s) : WindowInvariant p (accept p s sample) := by
  have positive : 0 < p.window := by have := valid.1; have := valid.2; omega
  simp only [accept]
  split
  · exact ⟨old.empty, by simp, by simp, old.budget⟩
  · split
    · constructor
      · simp
      · intro _ _
        simp only
        exact ⟨positive, by omega⟩
      · simp
      · have budget := old.budget
        simp only [Nat.add_mul, Nat.one_mul] at *
        omega
    · split
      next empty =>
        have zero := old.empty (by simpa using empty)
        constructor
        · simp
        · intro _ _
          simp only
          exact ⟨positive, by omega⟩
        · simp
        · simp only
          simp [zero.1, zero.2]
      next notEmpty =>
        have nonempty : s.history ≠ [] := by simpa using notEmpty
        split
        next validating =>
          have window := old.validating validating nonempty
          constructor
          · simp
          · intro mode _
            simp only at mode ⊢
            have remaining : 1 < s.remaining := by
              by_cases last : s.remaining ≤ 1
              · simp [last] at mode
              · omega
            exact ⟨by omega, by omega⟩
          · intro mode
            simp only at mode ⊢
            have last : s.remaining ≤ 1 := by
              by_cases last : s.remaining ≤ 1
              · exact last
              · simp [last] at mode
            exact ⟨by omega, by omega⟩
          · have budget := old.budget
            simp only
            omega
        next notValidating =>
          constructor
          · simp
          · intro impossible
            exact False.elim (notValidating impossible)
          · intro provisional
            have before := old.provisional provisional
            simp only
            exact ⟨before.1, by omega⟩
          · exact old.budget

theorem step_window (p s reading) (old : WindowInvariant p s) :
    WindowInvariant p (step p s reading) := by
  simp only [step]
  split
  · exact old
  · split
    · exact stop_window old .exhausted (by decide) (by decide)
    · cases reading with
      | none => exact stop_window (charge_window old) .fault (by decide) (by decide)
      | some sample =>
        simp only
        split
        next good => exact accept_window good.1 good.2 (charge_window old)
        next => exact stop_window (charge_window old) .fault (by decide) (by decide)

theorem run_window (p s readings) (old : WindowInvariant p s) :
    WindowInvariant p (run p s readings) := by
  induction readings generalizing s with
  | nil => exact old
  | cons reading rest ih => exact ih _ (step_window p s reading old)

theorem reachable_window (p start budget readings) :
    WindowInvariant p (run p (initial p start budget) readings) :=
  run_window p _ readings (initial_window p start budget)

theorem reachable_validation_budget (p start budget readings) :
    (run p (initial p start budget) readings).validationSteps +
      (run p (initial p start budget) readings).remaining ≤
      (p.cap + 1) * p.window := by
  have window := (reachable_window p start budget readings).budget
  have rank := refinements_bounded p start budget readings
  have product := Nat.mul_le_mul_right p.window (Nat.succ_le_succ rank)
  exact Nat.le_trans window (by simpa only [Nat.succ_eq_add_one] using product)

theorem proposal_has_elapsed_window {p start budget readings result}
    (offered : proposal p (run p (initial p start budget) readings) = some result) :
    (run p (initial p start budget) readings).windowStart + p.window <
      (run p (initial p start budget) readings).nextTime := by
  have mode := (proposal_requires_finished_window offered).1
  exact ((reachable_window p start budget readings).provisional mode).2

theorem reachable_proposal_dates {p start budget readings result}
    (offered : proposal p (run p (initial p start budget) readings) = some result) :
    result.fromTime + p.window = result.throughTime ∧
    result.throughTime < (run p (initial p start budget) readings).nextTime ∧
    result.bound = (run p (initial p start budget) readings).bound ∧
    result.horizon = p.horizon := by
  have elapsed := proposal_has_elapsed_window offered
  simp only [proposal] at offered
  split at offered
  next =>
    have same := Option.some.inj offered
    subst result
    exact ⟨rfl, elapsed, rfl, rfl⟩
  next => contradiction

end LearnedVariation
