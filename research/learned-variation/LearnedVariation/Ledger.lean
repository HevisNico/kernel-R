import LearnedVariation.Learner

namespace LearnedVariation

def SampledBound (p : Policy) (bound : Nat) (truth : Nat → Nat) : List Sample → Prop
  | [] => True
  | sample :: history =>
    (∀ old ∈ history, eligible p.horizon old sample = true → truth sample.time ≤ truth old.time + bound) ∧
    SampledBound p bound truth history

theorem fits_sampled_sound (p bound truth history) (fits : Fits p bound history)
    (honest : ∀ s ∈ history, s.interval.Contains (truth s.time)) : SampledBound p bound truth history := by
  induction history with
  | nil => trivial
  | cons sample history ih =>
    constructor
    · intro old member within
      exact demand_sampled_sound fits.1 member within
        (honest old (by simp [member])) (honest sample (by simp))
    · exact ih fits.2 (by intro s member; exact honest s (by simp [member]))

theorem learned_prefix_sampled_sound (p start budget readings truth)
    (honest : ∀ s ∈ (run p (initial p start budget) readings).history,
      s.interval.Contains (truth s.time)) :
    SampledBound p (run p (initial p start budget) readings).bound truth
      (run p (initial p start budget) readings).history :=
  fits_sampled_sound _ _ _ _ (prefix_fits p start budget readings) honest

theorem annotation_witnesses (p bound history sample old)
    (member : old ∈ (annotation p bound history sample).witnesses) :
    old ∈ history ∧ old.time < sample.time ∧ sample.time ≤ old.time + p.horizon ∧
    bound < pairNeed old sample := by
  simp only [annotation, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
    eligible] at member
  exact ⟨member.1, member.2.1.1, member.2.1.2, member.2.2⟩

theorem annotation_refutation_sound {p bound history sample} (truth : Nat → Nat)
    (oldHonest : ∀ old ∈ history, old.interval.Contains (truth old.time))
    (nextHonest : sample.interval.Contains (truth sample.time))
    (marked : (annotation p bound history sample).demonstrated = true) :
    ∃ old ∈ history, eligible p.horizon old sample = true ∧ truth old.time + bound < truth sample.time :=
  refuted_sampled_sound truth oldHonest nextHonest marked

theorem step_keeps_annotations (p s reading) :
    ∃ extra, (step p s reading).annotations = extra ++ s.annotations := by
  simp only [step]
  split
  · exact ⟨[], rfl⟩
  · split
    · exact ⟨[], rfl⟩
    · cases reading with
      | none => exact ⟨[], rfl⟩
      | some sample =>
        simp only
        split
        · exact accept_keeps_annotations p (charge s) sample
        · exact ⟨[], rfl⟩

theorem run_keeps_annotations (p s readings) :
    ∃ extra, (run p s readings).annotations = extra ++ s.annotations := by
  induction readings generalizing s with
  | nil => exact ⟨[], rfl⟩
  | cons next rest ih =>
    obtain ⟨recent, later⟩ := ih (step p s next)
    obtain ⟨current, kept⟩ := step_keeps_annotations p s next
    refine ⟨recent ++ current, ?_⟩
    simp only [run, later, kept, List.append_assoc]

theorem accept_bound_monotone (p s sample) : s.bound ≤ (accept p s sample).bound := by
  simp only [accept]
  split
  · exact Nat.le_refl _
  · split
    · exact widen_monotone _ _
    · split
      · exact Nat.le_refl _
      · split <;> exact Nat.le_refl _

theorem step_bound_monotone (p s reading) : s.bound ≤ (step p s reading).bound := by
  simp only [step]
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · cases reading with
      | none => exact Nat.le_refl _
      | some sample =>
        simp only
        split
        · exact accept_bound_monotone p (charge s) sample
        · exact Nat.le_refl _

theorem run_bound_monotone (p s readings) : s.bound ≤ (run p s readings).bound := by
  induction readings generalizing s with
  | nil => exact Nat.le_refl _
  | cons next rest ih => exact Nat.le_trans (step_bound_monotone p s next) (ih (step p s next))

theorem accept_history_size (p s sample) :
    (accept p s sample).history.length ≤ s.history.length + 1 := by
  simp only [accept]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split <;> simp

theorem step_memory_paid (p s reading) :
    (step p s reading).history.length + (step p s reading).credit ≤ s.history.length + s.credit := by
  simp only [step]
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    next paid =>
      have charged : (charge s).credit + 1 = s.credit := by simp only [charge]; omega
      cases reading with
      | none => change s.history.length + (s.credit - 1) ≤ s.history.length + s.credit; omega
      | some sample =>
        simp only
        split
        · have size := accept_history_size p (charge s) sample
          have credit := (accept_accounting p (charge s) sample).1
          rw [credit]
          change (accept p (charge s) sample).history.length ≤ s.history.length + 1 at size
          omega
        · change s.history.length + (s.credit - 1) ≤ s.history.length + s.credit
          omega

theorem finite_memory (p start budget readings) :
    (run p (initial p start budget) readings).history.length ≤ budget := by
  have general : ∀ s, (run p s readings).history.length + (run p s readings).credit ≤
      s.history.length + s.credit := by
    induction readings with
    | nil => intro s; exact Nat.le_refl _
    | cons next rest ih => intro s; exact Nat.le_trans (ih (step p s next)) (step_memory_paid p s next)
  have bound := general (initial p start budget)
  change (run p (initial p start budget) readings).history.length +
    (run p (initial p start budget) readings).credit ≤ 0 + budget at bound
  omega

end LearnedVariation
