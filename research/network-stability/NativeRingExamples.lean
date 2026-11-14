import NativeRingTarget

namespace NetworkStability.NativeRing

def allStrongParameters (N : Nat) : Parameters N :=
  ⟨fun _ => 8, fun _ => 37 / 20, 1⟩

def stoppingParameters (N : Nat) : Parameters N :=
  { allStrongParameters N with
    forwardAmplitude := fun i => if i.val = 1 then 1 else 37 / 20 }

theorem allStrong_valid (size : 2 ≤ N) : (allStrongParameters N).Valid := by
  refine ⟨size, by norm_num [WeakAmplitude, allStrongParameters], ?_⟩
  intro i
  have amplitude : StrongAmplitude (37 / 20) := by norm_num [StrongAmplitude]
  refine ⟨by norm_num [allStrongParameters], ?_⟩
  split
  · exact amplitude
  · exact Or.inr amplitude

theorem accepts_all_strong_two : (allStrongParameters 2).check = true := by decide +kernel
theorem accepts_all_strong_three : (allStrongParameters 3).check = true := by decide +kernel
theorem accepts_stopping_two : (stoppingParameters 2).check = true := by decide +kernel
theorem accepts_stopping_three : (stoppingParameters 3).check = true := by decide +kernel

theorem rejects_single_cell : (allStrongParameters 1).check = false := by decide +kernel

theorem rejects_short_edge :
    ({ allStrongParameters 2 with delay := fun _ => 1 / 20 } : Parameters 2).check = false := by
  decide +kernel

theorem rejects_long_edge :
    ({ allStrongParameters 2 with delay := fun _ => 10 } : Parameters 2).check = false := by
  decide +kernel

theorem rejects_weak_launch :
    ({ allStrongParameters 2 with
        forwardAmplitude := fun i => if i.val = 0 then 1 else 37 / 20 } : Parameters 2).check = false := by
  decide +kernel

theorem rejects_intermediate_relay :
    ({ allStrongParameters 2 with
        forwardAmplitude := fun i => if i.val = 1 then 3 / 2 else 37 / 20 } : Parameters 2).check = false := by
  decide +kernel

theorem rejects_underpowered_return :
    ({ allStrongParameters 2 with returnAmplitude := 4 / 5 } : Parameters 2).check = false := by
  decide +kernel

theorem rejects_strong_return :
    ({ allStrongParameters 2 with returnAmplitude := 37 / 20 } : Parameters 2).check = false := by
  decide +kernel

end NetworkStability.NativeRing
