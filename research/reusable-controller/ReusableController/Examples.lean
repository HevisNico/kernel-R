import ReusableController.Proofs

namespace ReusableController.Examples
open RecursiveLearning

def need : Learner := ⟨3, 3⟩
def start : State := initial ⟨4, 5⟩
def final : State := run need 5 start

/-- The second trial fails, but the third trial improves the retained lesson.
The outcomes are computed from the unchanged learner, not stored in a script. -/
theorem reject_then_continue :
    (run need 0 start).lesson.cost = 9 ∧
    (run need 1 start).lesson.cost = 8 ∧
    (run need 2 start).lesson.cost = 8 ∧
    (run need 3 start).lesson.cost = 7 ∧
    (run need 2 start).preparationBlocked = true ∧
    (run need 2 start).halted = false ∧
    (run need 4 start).lesson.cost = 6 ∧
    final.halted = true ∧ final.accepted = 3 ∧ final.attempts = 5 ∧
    final.trialPulses = 33 := by decide

/-- Search costs 33 learner pulses plus five units of declared overhead.
With overhead one, thirteen deployments amortize search; twelve do not. -/
theorem example_amortization :
    final.work 1 = 38 ∧
    final.work 1 + 13 * final.lesson.cost ≤ 13 * start.lesson.cost ∧
    ¬ (final.work 1 + 12 * final.lesson.cost ≤ 12 * start.lesson.cost) := by decide

theorem held_out_box (other : Learner)
    (prep : other.preparationLeft ≤ 3) (practice : other.practiceLeft ≤ 3) :
    (final.lesson.train other).retained = true := by
  apply ready_generalizes (run_ready 5 (initial_ready (by decide :
    ((⟨4, 5⟩ : Lesson).train need).retained = true))) prep practice

theorem zero_requirements :
    let result := run (⟨0, 0⟩ : Learner) 2 (initial ⟨0, 0⟩)
    result.halted = true ∧ result.trialPulses = 0 ∧ result.attempts = 2 ∧
    result.accepted = 0 := by decide

theorem halted_has_no_extra_cost : run need 100 final = final :=
  run_halted 100 (by decide)

end ReusableController.Examples
