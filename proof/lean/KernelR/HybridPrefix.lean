import KernelR.HybridWork

/-! Finite prefixes at actual intermediate dates. A cut reuses the given flow
path and integral equations; it does not construct a future continuation. -/
namespace KernelR.Hybrid

inductive Execution.IsPrefix {n θ route} :
    {s u v : Snapshot n} → Execution θ route s u → Execution θ route s v → Prop
  | nil {s u} (e : Execution θ route s u) : IsPrefix e (.nil s)
  | flowCut {s w u : Snapshot n} (f : Flow θ s w) (rest : Execution θ route w u)
      {t : ℝ} (ht : s.time < t) (hend : t ≤ w.time) :
      (Execution.cons (.flow f) rest).IsPrefix (.cons (.flow (f.prefix ht hend)) (.nil _))
  | step {s w u v : Snapshot n} (move : Move θ route s w) (rest : Execution θ route w u)
      (cut : Execution θ route w v) (hcut : rest.IsPrefix cut) :
      (Execution.cons move rest).IsPrefix (.cons move cut)

theorem Execution.IsPrefix.main_flows {n θ route s u v} {e : @Execution n θ route s u}
    {cut : Execution θ route s v} (hcut : e.IsPrefix cut) (i : Fin n) (mode : MainMode)
    (hm : e.MainFlows i mode) : cut.MainFlows i mode := by
  induction hcut with
  | nil => trivial
  | flowCut f rest ht hend => exact ⟨hm.1, trivial⟩
  | step move rest cut hcut ih =>
    cases move with
    | flow f => exact ⟨hm.1, ih hm.2⟩
    | jump j => exact ih hm

theorem Execution.IsPrefix.aux_flows {n θ route s u v} {e : @Execution n θ route s u}
    {cut : Execution θ route s v} (hcut : e.IsPrefix cut) (i : Fin n) (p : Port) (mode : AuxMode)
    (hm : e.AuxFlows i p mode) : cut.AuxFlows i p mode := by
  induction hcut with
  | nil => trivial
  | flowCut f rest ht hend => exact ⟨hm.1, trivial⟩
  | step move rest cut hcut ih =>
    cases move with
    | flow f => exact ⟨hm.1, ih hm.2⟩
    | jump j => exact ih hm

theorem Execution.prefix_at {n θ route s u} (e : @Execution n θ route s u)
    (t : ℝ) (ht : s.time ≤ t) (hu : t ≤ u.time) :
    ∃ (v : Snapshot n) (cut : Execution θ route s v), e.IsPrefix cut ∧ v.time = t := by
  induction e with
  | nil => exact ⟨_, .nil _, .nil _, le_antisymm ht hu⟩
  | @cons s v u move rest ih =>
    by_cases heq : t = s.time
    · exact ⟨s, .nil s, .nil _, heq.symm⟩
    · have hstart : s.time < t := lt_of_le_of_ne ht (Ne.symm heq)
      by_cases hmid : t ≤ v.time
      · cases move with
        | flow f => exact ⟨_, .cons (.flow (f.prefix hstart hmid)) (.nil _), .flowCut f rest hstart hmid, rfl⟩
        | jump j => exact False.elim (not_lt_of_ge (by simpa only [j.time_unchanged] using hmid) hstart)
      · obtain ⟨w, cut, hcut, hw⟩ := ih (le_of_not_ge hmid) hu
        exact ⟨w, .cons move cut, .step move rest cut hcut, hw⟩

/-- A raw end cannot occur before its actual origin plus one; an arrival cannot
overwrite the occupied port. This remains true across arbitrary other jumps. -/
theorem Jump.raw_persists {n route s u} (j : @Jump n route s u) (i : Fin n) (p : Port)
    (origin : ℝ) (hr : s.raw i p = some origin) (ht : s.time < origin + 1) :
    u.raw i p = some origin := by
  cases j <;> simp_all [setMain, setAux, setRaw, Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]
  all_goals aesop

theorem Execution.raw_persists {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (p : Port) (origin : ℝ) (hr : s.raw i p = some origin)
    (ht : u.time < origin + 1) : u.raw i p = some origin := by
  induction e with
  | nil => exact hr
  | cons move rest ih =>
    apply ih _ ht
    cases move with
    | flow f => simpa only [f.raw_fixed] using hr
    | jump j =>
      exact j.raw_persists i p origin hr (by rw [← j.time_unchanged]; exact rest.time_monotone.trans_lt ht)

end KernelR.Hybrid
