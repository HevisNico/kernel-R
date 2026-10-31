import KernelR.LearnedCycleStart
import KernelR.FutureControls

/-! A nonempty reacting prefix in the actual fabrication family, and concrete
counterexamples to applying the frozen-mode constructor in learning modes. -/
namespace KernelR.LearnedCycleControls
open KernelR.Hybrid KernelR.FutureControls

theorem first_mark_exists : Nonempty (FirstMarkPrefix parameters learned 0) :=
  learned_first_mark_prefix learned_section parameters_box

theorem ready_error_is_not_frozen : ¬ FrozenModes (setAux learned 0 0 .error) := by
  intro h
  exact (h.1 0 0 rfl) rfl

theorem protected_mark_is_not_frozen :
    ¬ FrozenModes (setMain (setAux learned 0 0 .mark) 0 .fast) := by
  intro h
  have hm := h.2 0 0 rfl
  cases hm

end KernelR.LearnedCycleControls
