import KernelR.HybridParameterTransport

/-! FIRE labels survive commuting and cancelling zero-time jumps. -/
namespace KernelR.Hybrid

private theorem simultaneous_count {n} (l : List (Fin n × ℝ)) (T : ℝ)
    (h : ∀ e ∈ l, e.2=T) (i : Fin n) :
    l.count (i,T)=(l.filter (fun e => e.1=i)).length := by
  classical
  induction l with
  | nil => simp
  | cons e l ih =>
    rcases e with ⟨j,t⟩
    have ht : t=T := h (j,t) (by simp)
    subst t
    have hr : ∀ e ∈ l, e.2=T := fun e he => h e (by simp [he])
    by_cases hj : j=i
    · subst j
      simp [ih hr]
    · simp [hj,ih hr]

private theorem simultaneous_emissions_perm {n} {l r : List (Fin n × ℝ)} {T : ℝ}
    (hl : ∀ e ∈ l, e.2=T) (hr : ∀ e ∈ r, e.2=T)
    (hcount : ∀ i, (l.filter (fun e => e.1=i)).length=
      (r.filter (fun e => e.1=i)).length) : l.Perm r := by
  classical
  apply List.perm_iff_count.mpr
  rintro ⟨i,t⟩
  by_cases ht : t=T
  · subst t
    rw [simultaneous_count l T hl i,simultaneous_count r T hr i]
    exact hcount i
  · have hnl : (i,t)∉l := fun he => ht (hl _ he)
    have hnr : (i,t)∉r := fun he => ht (hr _ he)
    rw [List.count_eq_zero_of_not_mem hnl,List.count_eq_zero_of_not_mem hnr]

/-- Counts the FAST state at its entry charge. A zero-time FAST exit
is at a different charge. -/
private noncomputable def parameterFastPotential {n} (θ : Fin n → Parameters)
    (s : Snapshot n) (i : Fin n) : ℕ :=
  if s.main i = .fast ∧ s.x i .q = (θ i).thresholds.fire then 1 else 0

private theorem ParameterJump.fast_potential_balance {n θ route s u}
    (j : @ParameterJump n θ route s u) (bounds : ParameterThresholdBounds θ)
    (i : Fin n) :
    parameterFastPotential θ s i + (j.emissions.filter (fun ev => ev.1 = i)).length =
      parameterFastPotential θ u i := by
  classical
  cases j with
  | fire k mode charge =>
    by_cases h : k = i
    · subst k
      simp [ParameterJump.emissions, parameterFastPotential, setMain, mode, charge]
    · simp [ParameterJump.emissions, parameterFastPotential, setMain, Function.update_of_ne (Ne.symm h), h]
  | fastEnd k mode charge =>
    by_cases h : k = i
    · subst k
      simp [ParameterJump.emissions, parameterFastPotential, setMain, charge, mode,
        ne_of_lt (bounds.fastBelowFire i)]
    · simp [ParameterJump.emissions, parameterFastPotential, setMain, Function.update_of_ne (Ne.symm h)]
  | reopen k mode charge =>
    by_cases h : k = i
    · subst k; simp [ParameterJump.emissions, parameterFastPotential, setMain, mode]
    · simp [ParameterJump.emissions, parameterFastPotential, setMain, Function.update_of_ne (Ne.symm h)]
  | _ => rfl

private theorem parameter_potential_observational {n θ} {s u : Snapshot n}
    (h : s.ObservationalEq u) (i : Fin n) :
    parameterFastPotential θ s i = parameterFastPotential θ u i := by
  simp only [parameterFastPotential, h.main, h.values]

def ParameterLabelledJumpDiamond {n θ route s a b}
    (j : @ParameterJump n θ route s a) (k : ParameterJump θ route s b) : Prop :=
  (a.ObservationalEq b ∧ j.emissions.Perm k.emissions) ∨
  ∃ a' b', ∃ j' : ParameterJump θ route a a', ∃ k' : ParameterJump θ route b b',
    a'.ObservationalEq b' ∧ (j.emissions ++ j'.emissions).Perm (k.emissions ++ k'.emissions)

theorem ParameterJump.labelled_local_diamond {n θ route s a b}
    (j : @ParameterJump n θ route s a) (k : ParameterJump θ route s b)
    (bounds : ParameterThresholdBounds θ) : ParameterLabelledJumpDiamond j k := by
  rcases j.local_diamond k with h | ⟨a',b',⟨j'⟩,⟨k'⟩,h⟩
  · left
    refine ⟨h, simultaneous_emissions_perm (T := s.time) j.emission_time k.emission_time ?_⟩
    intro i
    have hj := j.fast_potential_balance bounds i
    have hk := k.fast_potential_balance bounds i
    have he := parameter_potential_observational (θ := θ) h i
    omega
  · right
    refine ⟨a', b', j', k', h, simultaneous_emissions_perm (T := s.time) ?_ ?_ ?_⟩
    · intro ev he
      rcases List.mem_append.mp he with he | he
      · exact j.emission_time ev he
      · exact (j'.emission_time ev he).trans j.time_unchanged
    · intro ev he
      rcases List.mem_append.mp he with he | he
      · exact k.emission_time ev he
      · exact (k'.emission_time ev he).trans k.time_unchanged
    · intro i
      have hj := j.fast_potential_balance bounds i
      have hk := k.fast_potential_balance bounds i
      have hj' := j'.fast_potential_balance bounds i
      have hk' := k'.fast_potential_balance bounds i
      have he := parameter_potential_observational (θ := θ) h i
      simp only [List.filter_append, List.length_append]
      omega

/-- An enabled zero-time jump occurs in every complete trace, modulo commuting
simultaneous events. Its cancellation retains all remaining actual FIREs. -/
theorem ParameterExecution.strip_initial_jump {n θ route}
    (bounds : ParameterThresholdBounds θ)
    {s u a T} (e : @ParameterExecution n θ route s u) (hc : ParameterCompleteThrough e T)
    (j : ParameterJump θ route s a) :
    ∃ b, ∃ tail : ParameterExecution θ route a b,
      u.ObservationalEq b ∧ ParameterCompleteThrough tail T ∧
      (j.emissions++tail.emissions).Perm e.emissions ∧
      tail.moveCount+1=e.moveCount := by
  induction e generalizing a with
  | nil s => exact False.elim ((hc.2.1 a).false j)
  | @cons s mid u move rest ih =>
    have hrest : ParameterCompleteThrough rest T := hc
    cases move with
    | flow f => exact False.elim ((f.no_initial_jump a).false j)
    | jump k =>
      rcases j.labelled_local_diamond k bounds with ⟨h,hlabels⟩ | ⟨a',b',j',k',h,hlabels⟩
      · obtain ⟨v,tail,hv,hem,hcount⟩ := rest.transport_observational_emissions_count h.symm
        refine ⟨v,tail,hv,parameterCompleteThrough_of_observational rest tail hv hrest,?_,?_⟩
        · change (j.emissions++tail.emissions).Perm
            (k.emissions++rest.emissions)
          rw [hem]
          exact hlabels.append_right _
        · simp only [ParameterExecution.moveCount,hcount]
      · obtain ⟨v,tail,hv,hcomplete,hem,hcount⟩ := ih hrest k'
        obtain ⟨w,tail',hw,heq,hsize⟩ := tail.transport_observational_emissions_count h.symm
        let residual : ParameterExecution θ route a w := .cons (.jump j') tail'
        refine ⟨w,residual,hv.trans hw,parameterCompleteThrough_of_observational tail residual hw hcomplete,?_,?_⟩
        · change (j.emissions++(j'.emissions++tail'.emissions)).Perm
            (k.emissions++rest.emissions)
          rw [heq,←List.append_assoc]
          exact (hlabels.append_right _).trans (by
            rw [List.append_assoc]
            exact hem.append_left _)
        · change tail'.moveCount+1+1=rest.moveCount+1
          omega


end KernelR.Hybrid
