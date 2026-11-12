import ReusableController.Model

namespace ReusableController
open RecursiveLearning

theorem initial_ready {need : Learner} {lesson : Lesson}
    (passes : (lesson.train need).retained = true) : Ready need (initial lesson) := by
  have h := (lesson.retained_iff need).mp passes
  simpa [Ready, initial] using h

theorem ready_retains {need : Learner} {s : State} (h : Ready need s) :
    (s.lesson.train need).retained = true :=
  (s.lesson.retained_iff need).mpr ⟨h.1, h.2.1⟩

theorem ready_generalizes {need other : Learner} {s : State} (h : Ready need s)
    (prep : other.preparationLeft ≤ need.preparationLeft)
    (practice : other.practiceLeft ≤ need.practiceLeft) :
    (s.lesson.train other).retained = true :=
  (s.lesson.retained_iff other).mpr ⟨Nat.le_trans prep h.1, Nat.le_trans practice h.2.1⟩

def Unblocked (s : State) : Axis → Prop
  | .preparation => s.preparationBlocked = false
  | .practice => s.practiceBlocked = false

theorem choose_unblocked {s : State} {axis : Axis} (h : s.choose = some axis) :
    Unblocked s axis := by
  cases s with
  | mk lesson pb qb tries accepted pulses =>
    cases pb <;> cases qb <;> cases axis <;>
      simp_all [State.choose, Unblocked]

theorem choose_none_iff (s : State) : s.choose = none ↔ s.halted = true := by
  cases s with
  | mk lesson pb qb tries accepted pulses =>
    cases pb <;> cases qb <;> simp [State.choose, State.halted]

/-- Exact validation charge, independently of whether the trial is accepted.
This is not merely an upper bound on the cost of successful trials. -/
theorem attempt_validation_charge (need : Learner) (s : State) (axis : Axis) :
    (attempt need s axis).trialPulses = s.trialPulses +
      (match candidate s.lesson axis with | none => 0 | some trial => trial.cost) := by
  cases hc : candidate s.lesson axis with
  | none => cases axis <;> simp [attempt, hc, block]
  | some trial =>
    cases axis <;> simp only [attempt, hc] <;> split <;> rfl

theorem rejected_keeps_lesson {need : Learner} {s : State} {axis : Axis} {trial : Lesson}
    (proposed : candidate s.lesson axis = some trial)
    (rejected : (trial.train need).retained = false) :
    (attempt need s axis).lesson = s.lesson ∧
    (attempt need s axis).accepted = s.accepted := by
  cases axis <;> simp [attempt, proposed, rejected, block]

/-- The controller never needs to erase a blocked-coordinate bit. This is a
logical monotonicity result, not yet a construction of its physical encoding. -/
theorem attempt_flags_monotone (need : Learner) (s : State) (axis : Axis) :
    (s.preparationBlocked = true → (attempt need s axis).preparationBlocked = true) ∧
    (s.practiceBlocked = true → (attempt need s axis).practiceBlocked = true) := by
  cases hc : candidate s.lesson axis with
  | none => cases axis <;> simp [attempt, hc, block]
  | some trial =>
    cases axis <;> simp only [attempt, hc] <;>
      split <;> simp [commit, block]

/-- One operational attempt preserves the reusable invariant, decreases a
well-founded potential, retains exact accepted-decrement accounting, and
charges all validation pulses, including rejected trials. -/
theorem attempt_contract {need : Learner} {s : State} {axis : Axis}
    (ready : Ready need s) (available : Unblocked s axis) :
    Ready need (attempt need s axis) ∧
    (attempt need s axis).lesson.cost + (attempt need s axis).accepted =
      s.lesson.cost + s.accepted ∧
    (attempt need s axis).attempts = s.attempts + 1 ∧
    (attempt need s axis).potential < s.potential ∧
    s.trialPulses ≤ (attempt need s axis).trialPulses ∧
    (attempt need s axis).trialPulses ≤ s.trialPulses + s.lesson.cost ∧
    (attempt need s axis).lesson.preparation ≤ s.lesson.preparation ∧
    (attempt need s axis).lesson.practice ≤ s.lesson.practice := by
  rcases s with ⟨⟨p, q⟩, pb, qb, tries, accepted, pulses⟩
  cases axis <;> cases pb <;> cases qb <;>
    simp_all only [Unblocked, Bool.true_eq_false]
  all_goals
    by_cases hp : p = 0 <;> by_cases hq : q = 0 <;>
      simp_all [attempt, candidate, Ready, block, commit, State.potential, Lesson.cost,
        Lesson.retained_iff]
  all_goals
    split <;> simp_all <;> omega

theorem round_halted {need : Learner} {s : State} (h : s.halted = true) :
    round need s = s := by
  simp [round, (choose_none_iff s).mpr h]

theorem round_ready {need : Learner} {s : State} (h : Ready need s) :
    Ready need (round need s) := by
  cases hc : s.choose with
  | none => simpa [round, hc] using h
  | some axis => simpa [round, hc] using (attempt_contract h (choose_unblocked hc)).1

theorem round_accounting {need : Learner} {s : State} (h : Ready need s) :
    (round need s).lesson.cost + (round need s).accepted = s.lesson.cost + s.accepted := by
  cases hc : s.choose with
  | none => simp [round, hc]
  | some axis => simpa [round, hc] using (attempt_contract h (choose_unblocked hc)).2.1

theorem round_bounds {need : Learner} {s : State} (h : Ready need s) :
    (round need s).trialPulses ≤ s.trialPulses + s.lesson.cost ∧
    (round need s).attempts ≤ s.attempts + 1 ∧
    (round need s).lesson.cost ≤ s.lesson.cost := by
  cases hc : s.choose with
  | none => simp [round, hc]
  | some axis =>
    obtain ⟨_, _, ht, _, _, hp, hprep, hprac⟩ := attempt_contract h (choose_unblocked hc)
    simp only [round, hc]
    exact ⟨hp, by omega, Nat.add_le_add hprep hprac⟩

theorem round_progress {need : Learner} {s : State} (h : Ready need s)
    (active : s.halted = false) : (round need s).potential < s.potential := by
  cases hc : s.choose with
  | none => have := (choose_none_iff s).mp hc; simp_all
  | some axis => simpa [round, hc] using (attempt_contract h (choose_unblocked hc)).2.2.2.1

theorem run_ready {need : Learner} (n : Nat) {s : State} (h : Ready need s) :
    Ready need (run need n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih (round_ready h)

theorem run_halted {need : Learner} (n : Nat) {s : State} (h : s.halted = true) :
    run need n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, round_halted h] using ih

theorem run_accounting {need : Learner} (n : Nat) {s : State} (h : Ready need s) :
    (run need n s).lesson.cost + (run need n s).accepted = s.lesson.cost + s.accepted := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact (ih (round_ready h)).trans (round_accounting h)

theorem run_bounds {need : Learner} (n : Nat) {s : State} (h : Ready need s) :
    (run need n s).trialPulses ≤ s.trialPulses + n * s.lesson.cost ∧
    (run need n s).attempts ≤ s.attempts + n ∧
    (run need n s).lesson.cost ≤ s.lesson.cost := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    obtain ⟨hp, ht, hc⟩ := round_bounds h
    obtain ⟨rp, rt, rc⟩ := ih (round_ready h)
    have mul := Nat.mul_le_mul_left n hc
    simp only [run]
    rw [Nat.succ_mul]
    exact ⟨by omega, by omega, Nat.le_trans rc hc⟩

/-- Termination follows from actual transitions, including rejections; it
does not assume the existence of an accepted future improvement. -/
theorem halts_within {need : Learner} (fuel : Nat) {s : State}
    (h : Ready need s) (enough : s.potential ≤ fuel) :
    (run need fuel s).halted = true := by
  induction fuel generalizing s with
  | zero =>
    have stopped : s.halted = true := by
      cases s with
      | mk lesson pb qb tries accepted pulses =>
        cases pb <;> cases qb <;> simp_all [State.potential, State.halted] <;> omega
    exact stopped
  | succ fuel ih =>
    cases active : s.halted with
    | true => rw [run_halted (fuel + 1) active]; exact active
    | false =>
      have smaller := round_progress h active
      exact ih (round_ready h) (by omega)

theorem halted_exact {need : Learner} {s : State} (h : Ready need s)
    (halted : s.halted = true) :
    s.lesson.preparation = need.preparationLeft ∧
    s.lesson.practice = need.practiceLeft := by
  have both : s.preparationBlocked = true ∧ s.practiceBlocked = true := by
    simpa [State.halted] using halted
  exact ⟨Nat.le_antisymm (h.2.2.1 both.1) h.1,
    Nat.le_antisymm (h.2.2.2 both.2) h.2.1⟩

/-- For every pair of natural requirements and every initially valid lesson,
the fixed algorithm terminates at the minimum two-block lesson. -/
theorem terminal_optimal {need : Learner} {lesson : Lesson}
    (passes : (lesson.train need).retained = true) :
    let final := run need (lesson.cost + 2) (initial lesson)
    Ready need final ∧ final.halted = true ∧
    final.lesson.preparation = need.preparationLeft ∧
    final.lesson.practice = need.practiceLeft ∧
    ∀ other : Lesson, (other.train need).retained = true → final.lesson.cost ≤ other.cost := by
  dsimp only
  have start := initial_ready passes
  have ready := run_ready (lesson.cost + 2) start
  have halted := halts_within (lesson.cost + 2) start (by simp [State.potential, initial])
  obtain ⟨hp, hq⟩ := halted_exact ready halted
  refine ⟨ready, halted, hp, hq, ?_⟩
  intro other success
  have bounds := (other.retained_iff need).mp success
  show _ + _ ≤ _ + _
  rw [hp, hq]
  exact Nat.add_le_add bounds.1 bounds.2

/-- A sufficient amortization condition, with all counted search work paid.
It compares repeated deployment of the final lesson to the initial lesson. -/
theorem deployment_break_even {need : Learner} {lesson : Lesson} (n uses overhead : Nat)
    (passes : (lesson.train need).retained = true)
    (paid : (run need n (initial lesson)).work overhead ≤
      uses * (run need n (initial lesson)).accepted) :
    (run need n (initial lesson)).work overhead +
      uses * (run need n (initial lesson)).lesson.cost ≤ uses * lesson.cost := by
  have acc := run_accounting n (initial_ready passes)
  change (run need n (initial lesson)).lesson.cost +
    (run need n (initial lesson)).accepted = lesson.cost + 0 at acc
  rw [Nat.add_zero] at acc
  rw [← acc, Nat.mul_add]
  omega

end ReusableController
