import KernelR.LearnedSingleCell
import KernelR.FutureControls

/-! A nonempty reacting prefix in the actual fabrication family, and concrete
counterexamples to applying the frozen-mode constructor in learning modes. -/
namespace KernelR.LearnedCycleControls
open KernelR.Hybrid KernelR.FutureControls

theorem first_mark_exists : Nonempty (FirstMarkPrefix parameters learned 0) :=
  learned_first_mark_prefix learned_section parameters_box

theorem first_fire_exists : Nonempty (FirstFirePrefix parameters learned 0) :=
  learned_first_fire_prefix learned_section parameters_box

theorem learned_return_exists_control : Nonempty (LearnedReturn parameters (fun _ => 0) learned 0) :=
  learned_return_exists learned_section parameters_box

theorem learned_contract_exists : Nonempty (PulseContract parameters (fun _ _ => [])
    (fun _ => 0) learned 0 0) := ⟨learnedPulseContract parameters_box learned_section⟩

noncomputable def periodicLearnedSchedule : FutureSchedule (15/2) :=
  ⟨fun k => (k : ℝ)*(15/2), by intro k; push_cast; linarith⟩

theorem periodic_complete (T : ℝ) (hT : 0 ≤ T) :
    ∃ (k : ℕ) (last : Snapshot 1)
      (run : Execution parameters (fun _ _ => [])
        (withFuture learned (sourceQueue 0 0 periodicLearnedSchedule.time k)) last),
      CompleteThrough run T ∧ ∀ j, periodicLearnedSchedule.time j ≤ T → j < k := by
  exact learned_complete_at_every_horizon parameters_box learned_section periodicLearnedSchedule learned
    ⟨learned_section, fun i => ⟨rfl, fun p => rfl⟩⟩ (by norm_num [periodicLearnedSchedule, learned])
    T (by simpa [learned] using hT)

theorem ready_error_is_not_frozen : ¬ FrozenModes (setAux learned 0 0 .error) := by
  intro h
  exact (h.1 0 0 rfl) rfl

theorem protected_mark_is_not_frozen :
    ¬ FrozenModes (setMain (setAux learned 0 0 .mark) 0 .fast) := by
  intro h
  have hm := h.2 0 0 rfl
  cases hm

end KernelR.LearnedCycleControls
