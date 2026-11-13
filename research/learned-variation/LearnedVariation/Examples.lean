import LearnedVariation.Window
import LearnedVariation.Ledger

namespace LearnedVariation.Examples
open SelfCertifyingLearning

def policy : Policy := ⟨2, 10, 2⟩
def sample (time rate radius : Nat) : Option Sample := some ⟨time, Renewal.measurement rate radius⟩
def start := initial policy 0 10
def first := run policy start [sample 0 10 0, sample 1 10 0, sample 2 10 0]
def changed := step policy first (sample 3 15 0)
def validated := run policy changed [sample 4 15 0, sample 5 15 0]
def overflow := step policy validated (sample 6 30 0)

theorem first_window : first.mode = .provisional ∧ first.remaining = 0 ∧
    first.validationSteps = 2 ∧ first.attempts = 3 := by decide

theorem no_early_validation :
    (run policy start [sample 0 10 0, sample 1 10 0]).mode = .validating := by decide

theorem widening_sample_is_not_validation : changed.bound = 5 ∧ changed.remaining = 2 ∧
    changed.validationSteps = 2 ∧ changed.windowStart = 3 ∧ changed.mode = .validating := by decide

theorem fixed_new_window : (proposal policy validated).map EmpiricalProposal.throughTime = some 5 ∧
    validated.validationSteps = 4 ∧ validated.refinements = 1 := by decide

theorem overflow_is_not_fitted : overflow.mode = .exhausted ∧ overflow.bound = 5 ∧
    proposal policy overflow = none ∧ overflow.annotations.length = 2 ∧
    overflow.attempts = 7 := by decide

theorem overflowing_witness_retained : (overflow.annotations.head?).map Annotation.required = some 15 ∧
    (overflow.annotations.head?).map (fun a => a.trigger.time) = some 6 := by decide

theorem no_restart_same_bound :
    (step policy validated (sample 6 15 0)).mode = .provisional ∧
    (step policy validated (sample 6 15 0)).remaining = 0 ∧
    (step policy validated (sample 6 15 0)).validationSteps = 4 := by decide

theorem all_pairs_checked :
    (run policy start [sample 0 0 0, sample 1 4 0, sample 2 8 0]).bound = 8 := by decide

theorem noise_only_enlargement :
    let s := run policy start [sample 0 9 1, sample 1 11 1]
    s.bound = 4 ∧ s.mode = .validating ∧
      (s.annotations.head?).map Annotation.demonstrated = some false := by decide

theorem missing_probe_costs_one :
    (step policy first none).mode = .fault ∧ (step policy first none).attempts = 4 := by decide

theorem stale_probe_faults :
    (step policy first (sample 2 10 0)).mode = .fault := by decide

theorem skipped_validation_tick_faults :
    (run policy start [sample 0 10 0, sample 2 10 0]).mode = .fault := by decide

theorem invalid_window_faults :
    (step ⟨41, 10, 40⟩ (initial ⟨41, 10, 40⟩ 0 5) (sample 0 10 0)).mode = .fault := by decide

theorem terminal_cannot_refill : step policy overflow (sample 7 10 0) = overflow := by decide

theorem empty_budget_no_measurement :
    (step policy (initial policy 0 0) (sample 0 10 0)).attempts = 0 ∧
    (step policy (initial policy 0 0) (sample 0 10 0)).mode = .exhausted := by decide

end LearnedVariation.Examples
