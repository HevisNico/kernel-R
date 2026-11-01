import KernelR.Cadence

namespace KernelR.Hybrid

structure CadenceForwardLatencies where
  firstLow : ℝ
  restLow : ℝ
  firstHigh : ℝ
  restHigh : ℝ

structure CadenceForwardLatencyBounds (v : CadenceForwardLatencies) : Prop where
  firstLow_lower : 3 / 10 < v.firstLow
  firstLow_upper : v.firstLow < 9 / 10
  firstLow_le : v.firstLow ≤ v.restLow
  low_lower : 13 / 20 < v.restLow
  low_upper : v.restLow < 33 / 50
  firstHigh_lower : 4 / 25 < v.firstHigh
  firstHigh_le : v.firstHigh ≤ v.restHigh
  high_upper : v.restHigh < 13 / 50

noncomputable def cadenceForwardCDate (v : CadenceForwardLatencies) : ℕ → ℝ
  | 0 => 652 + v.firstLow
  | 1 => 660 + v.restLow
  | 2 => 668 + v.firstHigh
  | k + 3 => 672 + 4 * (k : ℝ) + v.restHigh

noncomputable def cadenceForwardBDate (v : CadenceForwardLatencies)
    (forward : ℝ → ℝ) (k : ℕ) : ℝ :=
  cadenceForwardCDate v k + forward (cadenceForwardCDate v k)

noncomputable def cadenceForwardCCalendar (v : CadenceForwardLatencies) : List ℝ :=
  List.ofFn (fun k : Fin 20 => cadenceForwardCDate v k.val)

noncomputable def cadenceForwardBCalendar (v : CadenceForwardLatencies)
    (forward : ℝ → ℝ) : List ℝ :=
  List.ofFn (fun k : Fin 20 => cadenceForwardBDate v forward k.val)

noncomputable def cadenceForwardSparse (v : CadenceForwardLatencies)
    (forward : ℝ → ℝ) : List ℝ :=
  [cadenceForwardBDate v forward 0,cadenceForwardBDate v forward 1]

noncomputable def cadenceForwardHighTail (v : CadenceForwardLatencies)
    (forward : ℝ → ℝ) : List ℝ :=
  List.ofFn (fun k : Fin 13 => cadenceForwardBDate v forward (k.val + 7))

theorem cadenceForwardCDate_ge_three (v : CadenceForwardLatencies) {k : ℕ} (hk : 3 ≤ k) :
    cadenceForwardCDate v k = 660 + 4 * (k : ℝ) + v.restHigh := by
  rw [show k = (k - 3) + 3 by omega,cadenceForwardCDate]
  push_cast
  ring

private theorem forward_difference {v : CadenceForwardLatencies} {forward : ℝ → ℝ}
    (hf : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5) (i j : ℕ) :
    -(1 / 10 : ℝ) ≤ (cadenceForwardBDate v forward j - cadenceForwardBDate v forward i) -
      (cadenceForwardCDate v j - cadenceForwardCDate v i) ∧
    (cadenceForwardBDate v forward j - cadenceForwardBDate v forward i) -
      (cadenceForwardCDate v j - cadenceForwardCDate v i) ≤ 1 / 10 := by
  dsimp [cadenceForwardBDate]
  constructor <;> linarith [(hf (cadenceForwardCDate v i)).1,(hf (cadenceForwardCDate v i)).2,
    (hf (cadenceForwardCDate v j)).1,(hf (cadenceForwardCDate v j)).2]

theorem cadenceForwardC_step {v : CadenceForwardLatencies} (hv : CadenceForwardLatencyBounds v)
    (k : ℕ) : cadenceForwardCDate v k + 4 ≤ cadenceForwardCDate v (k + 1) := by
  by_cases hk : k < 3
  · interval_cases k <;> norm_num [cadenceForwardCDate] <;>
      linarith [hv.firstLow_le,hv.low_upper,hv.firstHigh_lower,hv.firstHigh_le]
  · rw [cadenceForwardCDate_ge_three v (by omega),cadenceForwardCDate_ge_three v (by omega)]
    push_cast
    linarith

theorem cadenceForwardC_spacing {v : CadenceForwardLatencies} (hv : CadenceForwardLatencyBounds v)
    {i j : ℕ} (hij : i < j) : cadenceForwardCDate v i + 4 ≤ cadenceForwardCDate v j := by
  have hmono : Monotone (cadenceForwardCDate v) := monotone_nat_of_le_succ (fun k => by
    linarith [cadenceForwardC_step hv k])
  exact (cadenceForwardC_step hv i).trans (hmono (Nat.add_one_le_iff.mpr hij))

theorem cadenceForwardB_sparse_spacing {v : CadenceForwardLatencies}
    (hv : CadenceForwardLatencyBounds v) {forward : ℝ → ℝ}
    (hf : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    {i j : ℕ} (hij : i < j) (hj : j ≤ 2) :
    cadenceForwardBDate v forward i + 7 ≤ cadenceForwardBDate v forward j := by
  have hd := (forward_difference (v := v) hf i j).1
  have hi : i ≤ 2 := by omega
  interval_cases i <;> interval_cases j <;> norm_num [cadenceForwardCDate] at hij hd ⊢
  all_goals linarith [hv.firstLow_le,hv.firstLow_upper,hv.low_upper,hv.firstHigh_lower]

theorem cadenceForwardB_dense_gaps {v : CadenceForwardLatencies}
    (hv : CadenceForwardLatencyBounds v) {forward : ℝ → ℝ}
    (hf : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5) (k : Fin 4) :
    cadenceForwardBDate v forward (k.val + 2) + 19 / 5 ≤ cadenceForwardBDate v forward (k.val + 3) ∧
    cadenceForwardBDate v forward (k.val + 3) ≤ cadenceForwardBDate v forward (k.val + 2) + 21 / 5 := by
  have hd := forward_difference (v := v) hf (k.val + 2) (k.val + 3)
  fin_cases k <;> norm_num [cadenceForwardCDate] at hd ⊢
  all_goals constructor <;> linarith [hd.1,hd.2,hv.firstHigh_lower,hv.firstHigh_le,hv.high_upper]

theorem cadenceForwardB_high_spacing {v : CadenceForwardLatencies}
    {forward : ℝ → ℝ} (hf : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    {i j : ℕ} (hi : 3 ≤ i) (hij : i < j) :
    cadenceForwardBDate v forward i + 19 / 5 ≤ cadenceForwardBDate v forward j := by
  have hd := (forward_difference (v := v) hf i j).1
  rw [cadenceForwardCDate_ge_three v hi,cadenceForwardCDate_ge_three v (by omega)] at hd
  have hj : (i : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.add_one_le_iff.mpr hij)
  linarith

theorem cadenceForwardC_gate {v : CadenceForwardLatencies} (hv : CadenceForwardLatencyBounds v)
    {k : ℕ} (hk : k < 20) : 640 ≤ cadenceForwardCDate v k ∧ cadenceForwardCDate v k < 780 := by
  by_cases hsmall : k < 3
  · interval_cases k <;> norm_num [cadenceForwardCDate] <;>
      constructor <;> linarith [hv.firstLow_lower,hv.firstLow_upper,hv.low_lower,hv.low_upper,
        hv.firstHigh_lower,hv.firstHigh_le,hv.high_upper]
  · rw [cadenceForwardCDate_ge_three v (by omega)]
    have hlo : (3 : ℝ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
    have hhi : (k : ℝ) ≤ 19 := by exact_mod_cast (show k ≤ 19 by omega)
    constructor <;> linarith [hv.firstHigh_lower,hv.firstHigh_le,hv.high_upper]

theorem cadenceForwardB_quiet {v : CadenceForwardLatencies} (hv : CadenceForwardLatencyBounds v)
    {forward : ℝ → ℝ} (hf : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    {k : ℕ} (hk : k < 20) : cadenceForwardBDate v forward k + 19 / 5 ≤ 7899 / 10 := by
  have hc := (cadenceForwardC_gate hv hk).2
  have hfupper := (hf (cadenceForwardCDate v k)).2
  dsimp [cadenceForwardBDate]
  linarith

theorem cadenceForwardB_decomposition (v : CadenceForwardLatencies) (forward : ℝ → ℝ) :
    cadenceForwardBCalendar v forward = cadenceForwardSparse v forward ++
      cadenceForwardBDate v forward 2 :: cadenceForwardBDate v forward 3 ::
      cadenceForwardBDate v forward 4 :: cadenceForwardBDate v forward 5 ::
      cadenceForwardBDate v forward 6 :: cadenceForwardHighTail v forward := by
  simp [cadenceForwardBCalendar,cadenceForwardSparse,cadenceForwardHighTail,List.ofFn_succ,Nat.add_assoc]

theorem cadenceForwardC_calendar (v : CadenceForwardLatencies) :
    cadenceForwardCCalendar v =
      (652 + v.firstLow) :: (660 + v.restLow) :: (668 + v.firstHigh) ::
        List.ofFn (fun k : Fin 17 => (672 : ℝ) + 4 * (k.val : ℝ) + v.restHigh) := by
  simp [cadenceForwardCCalendar,cadenceForwardCDate,List.ofFn_succ,Nat.add_assoc]

theorem cadenceForwardB_map (v : CadenceForwardLatencies) (forward : ℝ → ℝ) :
    cadenceForwardBCalendar v forward = (cadenceForwardCCalendar v).map (fun t => t + forward t) := by
  simp only [cadenceForwardBCalendar,cadenceForwardCCalendar,List.map_ofFn,Function.comp_def,
    cadenceForwardBDate]

structure CadenceForwardGeometry (v : CadenceForwardLatencies) (forward : ℝ → ℝ) : Prop where
  decomposition : cadenceForwardBCalendar v forward = cadenceForwardSparse v forward ++
    cadenceForwardBDate v forward 2 :: cadenceForwardBDate v forward 3 ::
    cadenceForwardBDate v forward 4 :: cadenceForwardBDate v forward 5 ::
    cadenceForwardBDate v forward 6 :: cadenceForwardHighTail v forward
  sparse_spacing : (cadenceForwardSparse v forward ++ [cadenceForwardBDate v forward 2]).Pairwise
    (fun t w => t + 7 ≤ w)
  dense_gaps : ∀ k : Fin 4,
    cadenceForwardBDate v forward (k.val + 2) + 19 / 5 ≤ cadenceForwardBDate v forward (k.val + 3) ∧
    cadenceForwardBDate v forward (k.val + 3) ≤ cadenceForwardBDate v forward (k.val + 2) + 21 / 5
  high_spacing : (cadenceForwardBDate v forward 6 :: cadenceForwardHighTail v forward).Pairwise
    (fun t w => t + 19 / 5 ≤ w)
  quiet : ∀ t ∈ cadenceForwardBCalendar v forward, t + 19 / 5 ≤ 7899 / 10
  emissions_order : (cadenceForwardCCalendar v).Pairwise (fun t w => t + 1 / 10 ≤ w)
  gate : ∀ t ∈ cadenceForwardCCalendar v, 640 ≤ t ∧ t < 780

theorem cadenceForward_geometry {v : CadenceForwardLatencies}
    (hv : CadenceForwardLatencyBounds v) {forward : ℝ → ℝ}
    (hf : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5) : CadenceForwardGeometry v forward := by
  refine ⟨cadenceForwardB_decomposition v forward,?_,cadenceForwardB_dense_gaps hv hf,?_,?_,?_,?_⟩
  · change [cadenceForwardBDate v forward 0,cadenceForwardBDate v forward 1,
      cadenceForwardBDate v forward 2].Pairwise _
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) .nil))
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl
      · exact cadenceForwardB_sparse_spacing hv hf (by norm_num) (by norm_num)
      · exact cadenceForwardB_sparse_spacing hv hf (by norm_num) (by norm_num)
    · intro t ht
      have heq := List.mem_singleton.mp ht
      subst t
      exact cadenceForwardB_sparse_spacing hv hf (by norm_num) (by norm_num)
  · have hlist : cadenceForwardBDate v forward 6 :: cadenceForwardHighTail v forward =
        List.ofFn (fun k : Fin 14 => cadenceForwardBDate v forward (k.val + 6)) := by
      rw [List.ofFn_succ]
      simp only [Fin.val_zero,zero_add,Fin.val_succ,cadenceForwardHighTail]
    rw [hlist]
    apply List.pairwise_ofFn.mpr
    intro k l hkl
    exact cadenceForwardB_high_spacing hf (by omega) (by omega)
  · intro t ht
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ht
    exact cadenceForwardB_quiet hv hf k.isLt
  · apply List.pairwise_ofFn.mpr
    intro k l hkl
    have h := cadenceForwardC_spacing hv hkl
    linarith
  · intro t ht
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ht
    exact cadenceForwardC_gate hv k.isLt

end KernelR.Hybrid
