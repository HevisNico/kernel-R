import KernelR.HybridSourceProgress
import KernelR.HybridMainBounds

namespace KernelR.Hybrid

theorem sourceTrain_eight_head {n} (i : Fin n) (p : Port) :
    sourceTrain i p 8 8 15 = ⟨i,p,8⟩ :: sourceTrain i p 16 8 14 := by
  simpa only [show (8 : ℝ) + 8 = 16 by norm_num] using sourceTrain_succ i p 8 8 14

theorem sourceTrain_sixteen_head {n} (i : Fin n) (p : Port) :
    sourceTrain i p 16 8 14 = ⟨i,p,16⟩ :: sourceTrain i p 24 8 13 := by
  simpa only [show (16 : ℝ) + 8 = 24 by norm_num] using sourceTrain_succ i p 16 8 13

theorem sourceTrain_twenty_four_head {n} (i : Fin n) (p : Port) :
    sourceTrain i p 24 8 13 = ⟨i,p,24⟩ :: sourceTrain i p 32 8 12 := by
  simpa only [show (24 : ℝ) + 8 = 32 by norm_num] using sourceTrain_succ i p 24 8 12

theorem birth_protocol_tail_eight_head (born : Snapshot 1) :
    (birthProtocolFirstAfter born).pending = ⟨0,0,8⟩ ::
      (sourceTrain 0 0 16 8 14 ++ sourceTrain 0 0 160 8 16) := by
  change sourceTrain 0 0 8 8 15 ++ _ = _
  rw [sourceTrain_eight_head]
  rfl

theorem birth_protocol_first_three_partition :
    sourceTrain (0 : Fin 1) 0 0 8 16 ++ sourceTrain 0 0 160 8 16 =
      [⟨0,0,0⟩,⟨0,0,8⟩,⟨0,0,16⟩] ++
        (sourceTrain 0 0 24 8 13 ++ sourceTrain 0 0 160 8 16) := by
  rw [sourceTrain_succ,show (0 : ℝ) + 8 = 8 by norm_num,
    sourceTrain_eight_head,sourceTrain_sixteen_head]
  rfl

/-- Each weak source uses the cell's own initial memory plus its actual
previous ERROR doses. This covers the three weak inputs before dose three. -/
theorem own_birth_weak_gain_bounds {initial current : ℝ} {stage : ℕ}
    (hi : initial ≤ Real.log (3 / 10) + 1 / 100000) (hk : stage ≤ 2)
    (hcurrent : current = initial + (3 / 5) * (stage : ℝ)) :
    current ≤ Real.log (3 / 10) + 120001 / 100000 ∧
    Real.exp current ≤ 7 / 6 ∧ current ≤ Real.log (6 / 5) + 1 / 1000 := by
  have hstage : (stage : ℝ) ≤ 2 := by exact_mod_cast hk
  have hcurrentUpper : current ≤ Real.log (3 / 10) + 120001 / 100000 := by
    rw [hcurrent]
    linarith
  have hlog : Real.log (6 / 5 : ℝ) = Real.log (3 / 10) + a := by
    rw [show (6 / 5 : ℝ) = (3 / 10) * 4 by norm_num,
      Real.log_mul (by norm_num : (3 / 10 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
    rfl
  refine ⟨hcurrentUpper,low_gain_tail_upper (by linarith),?_⟩
  rw [hlog]
  have ha : (1386 / 1000 : ℝ) < a := by dsimp [a]; linarith [KernelR.log_four_bounds.1]
  linarith

theorem BirthState.own_low_port_weak_gain_bounds {n s} (hs : @BirthState n s)
    (i : Fin n) (p : Port) (hp : p ≠ 1) (stage : ℕ) (hk : stage ≤ 2) :
    Real.exp (s.x i (.z p) + (3 / 5) * (stage : ℝ)) ≤ 7 / 6 ∧
      s.x i (.z p) + (3 / 5) * (stage : ℝ) ≤ Real.log (6 / 5) + 1 / 1000 := by
  have hi : s.x i (.z p) ≤ Real.log (3 / 10) + 1 / 100000 := by
    simpa only [nominalGain,ite_eq_right hp] using ((hs.2.2 i).2.2.2.2 p).1.2
  exact (own_birth_weak_gain_bounds hi hk rfl).2

end KernelR.Hybrid
