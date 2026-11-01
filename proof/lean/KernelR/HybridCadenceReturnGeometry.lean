import KernelR.HybridCadenceRouter
/-! Geometry of the actual C → B → A cadence dates with independent wire jitter. -/
namespace KernelR.Hybrid

structure CadenceReturnLatencies where
  firstLowC : ℝ
  restLowC : ℝ
  firstHighC : ℝ
  restHighC : ℝ
  restLowB : ℝ
  firstHighB : ℝ
  restHighB : ℝ

structure CadenceReturnLatencyBounds (v : CadenceReturnLatencies) : Prop where
  firstLow_le : v.firstLowC ≤ v.restLowC
  lowC_lower : 13 / 20 < v.restLowC
  lowC_upper : v.restLowC < 33 / 50
  firstHighC_lower : 4 / 25 < v.firstHighC
  firstHighC_le : v.firstHighC ≤ v.restHighC
  highC_upper : v.restHighC < 13 / 50
  lowB_lower : 13 / 20 < v.restLowB
  lowB_upper : v.restLowB < 33 / 50
  firstHighB_lower : 4 / 25 < v.firstHighB
  firstHighB_le : v.firstHighB ≤ v.restHighB
  highB_upper : v.restHighB < 13 / 50

noncomputable def cadenceCOutputDate (v : CadenceReturnLatencies) : ℕ → ℝ
  | 0 => 652 + v.firstLowC
  | 1 => 660 + v.restLowC
  | 2 => 668 + v.firstHighC
  | k + 3 => 672 + 4 * (k : ℝ) + v.restHighC

noncomputable def cadenceBInputDate (v : CadenceReturnLatencies) (forward : ℝ → ℝ) (k : ℕ) : ℝ :=
  cadenceCOutputDate v k + forward (cadenceCOutputDate v k)

/-- These are precisely the C-output indices at which B emits. -/
def cadenceBOutputSourceIndex : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 6
  | k + 5 => k + 7

noncomputable def cadenceBOutputLatency (v : CadenceReturnLatencies) (j : ℕ) : ℝ :=
  if j < 4 then v.restLowB else if j = 4 then v.firstHighB else v.restHighB

noncomputable def cadenceBOutputDate (v : CadenceReturnLatencies) (forward : ℝ → ℝ) (j : ℕ) : ℝ :=
  cadenceBInputDate v forward (cadenceBOutputSourceIndex j) + cadenceBOutputLatency v j

noncomputable def cadenceAInputDate (v : CadenceReturnLatencies) (forward backward : ℝ → ℝ) (j : ℕ) : ℝ :=
  cadenceBOutputDate v forward j + backward (cadenceBOutputDate v forward j)

noncomputable def cadenceAInputCalendar (v : CadenceReturnLatencies) (forward backward : ℝ → ℝ) : List ℝ :=
  List.ofFn (fun j : Fin 18 => cadenceAInputDate v forward backward j.val)

noncomputable def cadenceASparseCalendar (v : CadenceReturnLatencies) (forward backward : ℝ → ℝ) : List ℝ :=
  List.ofFn (fun j : Fin 4 => cadenceAInputDate v forward backward j.val)

noncomputable def cadenceAHighTail (v : CadenceReturnLatencies) (forward backward : ℝ → ℝ) : List ℝ :=
  List.ofFn (fun j : Fin 9 => cadenceAInputDate v forward backward (j.val + 9))

private theorem wire_difference {f : ℝ → ℝ} (hf : ∀ t, 3 / 10 ≤ f t ∧ f t ≤ 2 / 5) (s t : ℝ) :
    -(1 / 10 : ℝ) ≤ f t - f s ∧ f t - f s ≤ 1 / 10 := by
  constructor <;> linarith [(hf s).1,(hf s).2,(hf t).1,(hf t).2]

private theorem return_difference {v : CadenceReturnLatencies} {forward backward : ℝ → ℝ}
    (hf : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hb : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5) (i j : ℕ) :
    -(1 / 5 : ℝ) ≤ (cadenceAInputDate v forward backward j - cadenceAInputDate v forward backward i) -
      ((cadenceCOutputDate v (cadenceBOutputSourceIndex j) + cadenceBOutputLatency v j) -
       (cadenceCOutputDate v (cadenceBOutputSourceIndex i) + cadenceBOutputLatency v i)) ∧
    (cadenceAInputDate v forward backward j - cadenceAInputDate v forward backward i) -
      ((cadenceCOutputDate v (cadenceBOutputSourceIndex j) + cadenceBOutputLatency v j) -
       (cadenceCOutputDate v (cadenceBOutputSourceIndex i) + cadenceBOutputLatency v i)) ≤ 1 / 5 := by
  have h₁ := wire_difference hf (cadenceCOutputDate v (cadenceBOutputSourceIndex i))
    (cadenceCOutputDate v (cadenceBOutputSourceIndex j))
  have h₂ := wire_difference hb (cadenceBOutputDate v forward i) (cadenceBOutputDate v forward j)
  dsimp [cadenceAInputDate,cadenceBOutputDate,cadenceBInputDate] at *
  constructor <;> linarith

/-- The sparse prefix includes the first strong arrival, whose residual latency
is independent of C's reference and of B's earlier low-gain reference. -/
theorem cadenceA_sparse_spacing {v : CadenceReturnLatencies} (hv : CadenceReturnLatencyBounds v)
    {forward backward : ℝ → ℝ}
    (hf : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hb : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5)
    {i j : ℕ} (hi : i < j) (hj : j ≤ 4) :
    cadenceAInputDate v forward backward i + 7 ≤ cadenceAInputDate v forward backward j := by
  have h := (return_difference (v := v) hf hb i j).1
  have hi4 : i ≤ 4 := by omega
  interval_cases i <;> interval_cases j <;> norm_num at hi hj
  all_goals norm_num [cadenceCOutputDate,cadenceBOutputSourceIndex,cadenceBOutputLatency] at h
  all_goals linarith [hv.firstLow_le,hv.lowC_upper,hv.firstHighC_lower,hv.firstHighC_le,
    hv.firstHighB_lower,hv.lowB_upper]

/-- One residual-to-rest transition can widen this first four-unit gap. -/
theorem cadenceA_first_strong_gap {v : CadenceReturnLatencies} (hv : CadenceReturnLatencyBounds v)
    {forward backward : ℝ → ℝ}
    (hf : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hb : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5) :
    cadenceAInputDate v forward backward 4 + 19 / 5 ≤ cadenceAInputDate v forward backward 5 ∧
      cadenceAInputDate v forward backward 5 ≤ cadenceAInputDate v forward backward 4 + 43 / 10 := by
  have h := return_difference (v := v) hf hb 4 5
  norm_num [cadenceCOutputDate,cadenceBOutputSourceIndex,cadenceBOutputLatency] at h
  constructor <;> linarith [hv.firstHighB_le,hv.firstHighB_lower,hv.highB_upper]

/-- All subsequent arrivals retain the same B resting latency, so only the two
fresh forward and two fresh backward evaluations contribute to each gap. -/
theorem cadenceA_rest_pair_gap {v : CadenceReturnLatencies} {forward backward : ℝ → ℝ}
    (hf : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hb : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5) (k : ℕ) :
    cadenceAInputDate v forward backward (k + 5) + 19 / 5 ≤ cadenceAInputDate v forward backward (k + 6) ∧
      cadenceAInputDate v forward backward (k + 6) ≤ cadenceAInputDate v forward backward (k + 5) + 21 / 5 := by
  have h := return_difference (v := v) hf hb (k + 5) (k + 6)
  simp only [cadenceBOutputSourceIndex,cadenceBOutputLatency,show ¬ k + 5 < 4 by omega,
    show ¬ k + 5 = 4 by omega,show ¬ k + 6 < 4 by omega,show ¬ k + 6 = 4 by omega,
    ite_false] at h
  have h₁ : cadenceCOutputDate v (k + 7) = 688 + 4 * (k : ℝ) + v.restHighC := by
    rw [show k + 7 = (k + 4) + 3 by omega,cadenceCOutputDate]
    push_cast
    ring
  have h₂ : cadenceCOutputDate v (k + 8) = 692 + 4 * (k : ℝ) + v.restHighC := by
    rw [show k + 8 = (k + 5) + 3 by omega,cadenceCOutputDate]
    push_cast
    ring
  rw [h₁,h₂] at h
  constructor <;> linarith

private theorem cadence_high_source_base (v : CadenceReturnLatencies) (k : ℕ) :
    cadenceCOutputDate v (cadenceBOutputSourceIndex (k + 5)) = 688 + 4 * (k : ℝ) + v.restHighC := by
  simp only [cadenceBOutputSourceIndex]
  rw [show k + 7 = (k + 4) + 3 by omega,cadenceCOutputDate]
  push_cast
  ring

/-- Pairwise spacing of the first high arrival and its nine successors. -/
theorem cadenceA_high_spacing {v : CadenceReturnLatencies} {forward backward : ℝ → ℝ}
    (hf : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hb : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5) {k l : ℕ} (hkl : k < l) :
    cadenceAInputDate v forward backward (k + 5) + 19 / 5 ≤ cadenceAInputDate v forward backward (l + 5) := by
  have h := (return_difference (v := v) hf hb (k + 5) (l + 5)).1
  rw [cadence_high_source_base,cadence_high_source_base] at h
  simp only [cadenceBOutputLatency,show ¬ k + 5 < 4 by omega,show ¬ k + 5 = 4 by omega,
    show ¬ l + 5 < 4 by omega,show ¬ l + 5 = 4 by omega,ite_false] at h
  have hreal : (k : ℝ) + 1 ≤ l := by exact_mod_cast (Nat.add_one_le_iff.mpr hkl)
  linarith

theorem cadenceA_horizon_quiet {v : CadenceReturnLatencies} (hv : CadenceReturnLatencyBounds v)
    {forward backward : ℝ → ℝ}
    (hf : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hb : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5) {j : ℕ} (hj : j < 18) :
    cadenceAInputDate v forward backward j + 19 / 5 ≤ 7899 / 10 := by
  have h₁ := (hf (cadenceCOutputDate v (cadenceBOutputSourceIndex j))).2
  have h₂ := (hb (cadenceBOutputDate v forward j)).2
  dsimp only [cadenceAInputDate,cadenceBOutputDate,cadenceBInputDate]
  interval_cases j <;> norm_num [cadenceCOutputDate,cadenceBOutputSourceIndex,cadenceBOutputLatency,
    cadenceBOutputDate,cadenceBInputDate] at *
  all_goals linarith [hv.firstLow_le,hv.lowC_upper,hv.firstHighC_le,hv.highC_upper,
    hv.lowB_upper,hv.firstHighB_le,hv.highB_upper]

/-- A reusable geometric summary; it describes dates, independently of the
later execution theorem which establishes B's emission calendar. -/
structure CadenceReturnGeometry (v : CadenceReturnLatencies) (forward backward : ℝ → ℝ) : Prop where
  sparse_spacing : (List.ofFn (fun j : Fin 5 => cadenceAInputDate v forward backward j.val)).Pairwise
    (fun t u => t + 7 ≤ u)
  first_strong_gap : cadenceAInputDate v forward backward 4 + 19 / 5 ≤ cadenceAInputDate v forward backward 5 ∧
    cadenceAInputDate v forward backward 5 ≤ cadenceAInputDate v forward backward 4 + 43 / 10
  rest_gaps : ∀ k, cadenceAInputDate v forward backward (k + 5) + 19 / 5 ≤ cadenceAInputDate v forward backward (k + 6) ∧
    cadenceAInputDate v forward backward (k + 6) ≤ cadenceAInputDate v forward backward (k + 5) + 21 / 5
  high_spacing : (List.ofFn (fun j : Fin 10 => cadenceAInputDate v forward backward (j.val + 8))).Pairwise
    (fun t u => t + 19 / 5 ≤ u)
  quiet : ∀ j : Fin 18, cadenceAInputDate v forward backward j.val + 19 / 5 ≤ 7899 / 10

theorem cadence_return_geometry {v : CadenceReturnLatencies} (hv : CadenceReturnLatencyBounds v)
    {forward backward : ℝ → ℝ}
    (hf : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5)
    (hb : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5) : CadenceReturnGeometry v forward backward := by
  constructor
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    exact cadenceA_sparse_spacing hv hf hb hij (by omega)
  · exact cadenceA_first_strong_gap hv hf hb
  · exact cadenceA_rest_pair_gap hf hb
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    simpa only [Nat.add_assoc,show 3 + 5 = 8 by rfl] using
      (cadenceA_high_spacing (v := v) hf hb (k := i.val + 3) (l := j.val + 3) (by omega))
  · intro j
    exact cadenceA_horizon_quiet hv hf hb j.isLt

theorem cadenceAInputCalendar_decomposition (v : CadenceReturnLatencies) (forward backward : ℝ → ℝ) :
    cadenceAInputCalendar v forward backward = cadenceASparseCalendar v forward backward ++
      [cadenceAInputDate v forward backward 4,cadenceAInputDate v forward backward 5,
       cadenceAInputDate v forward backward 6,cadenceAInputDate v forward backward 7,
       cadenceAInputDate v forward backward 8] ++ cadenceAHighTail v forward backward := by
  simp [cadenceAInputCalendar,cadenceASparseCalendar,cadenceAHighTail,List.ofFn_succ]

noncomputable def cadenceBOutputCalendar (v : CadenceReturnLatencies) (forward : ℝ → ℝ) : List ℝ :=
  [cadenceBInputDate v forward 0 + v.restLowB,cadenceBInputDate v forward 1 + v.restLowB,
   cadenceBInputDate v forward 2 + v.restLowB,cadenceBInputDate v forward 4 + v.restLowB,
   cadenceBInputDate v forward 6 + v.firstHighB] ++
    List.ofFn (fun k : Fin 13 => cadenceBInputDate v forward (k.val + 7) + v.restHighB)

theorem cadenceAInputCalendar_eq_return_map (v : CadenceReturnLatencies) (forward backward : ℝ → ℝ) :
    cadenceAInputCalendar v forward backward =
      (cadenceBOutputCalendar v forward).map (fun t => t + backward t) := by
  simp [cadenceAInputCalendar,cadenceBOutputCalendar,List.ofFn_succ,cadenceAInputDate,
    cadenceBOutputDate,cadenceBOutputSourceIndex,cadenceBOutputLatency]

theorem CadenceReturnGeometry.sparse_calendar_spacing {v forward backward}
    (geometry : CadenceReturnGeometry v forward backward) :
    (cadenceASparseCalendar v forward backward ++ [cadenceAInputDate v forward backward 4]).Pairwise
      (fun t u => t + 7 ≤ u) := by
  simpa [cadenceASparseCalendar,List.ofFn_succ] using geometry.sparse_spacing

theorem CadenceReturnGeometry.high_calendar_spacing {v forward backward}
    (geometry : CadenceReturnGeometry v forward backward) :
    (cadenceAInputDate v forward backward 8 :: cadenceAHighTail v forward backward).Pairwise
      (fun t u => t + 19 / 5 ≤ u) := by
  simpa [cadenceAHighTail,List.ofFn_succ] using geometry.high_spacing

theorem CadenceReturnGeometry.calendar_quiet {v forward backward}
    (geometry : CadenceReturnGeometry v forward backward) :
    ∀ t ∈ cadenceAInputCalendar v forward backward, t + 19 / 5 ≤ 7899 / 10 := by
  intro t ht
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
  exact geometry.quiet j

end KernelR.Hybrid
