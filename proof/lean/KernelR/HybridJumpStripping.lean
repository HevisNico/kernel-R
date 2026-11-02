import KernelR.HybridRawJumpConfluence
import KernelR.HybridObservationalTransport
import KernelR.HybridUrgentMoves
import KernelR.HybridEvents

/-! Cancellation of an enabled jump from a complete execution. Labels are
retained up to permutation of simultaneous FIREs; no target calendar or
endpoint property is assumed. -/
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

private theorem observational_fastPotential {n} {s t : Snapshot n}
    (h : s.ObservationalEq t) (i : Fin n) : fastPotential s i=fastPotential t i := by
  simp only [fastPotential,h.main,h.values]

/-- Local confluence with the exact observable FIRE label cost retained. -/
def LabelledJumpDiamond {n route s a b}
    (j : @Jump n route s a) (k : Jump route s b) : Prop :=
  (a.ObservationalEq b ∧ j.ledger.emissions.Perm k.ledger.emissions) ∨
  ∃ a' b', ∃ j' : Jump route a a', ∃ k' : Jump route b b',
    a'.ObservationalEq b' ∧
    (j.ledger.emissions++j'.ledger.emissions).Perm
      (k.ledger.emissions++k'.ledger.emissions)

/-- At equal physical observations the FAST potential determines every
zero-time FIRE count. This derives labelled confluence from physical confluence. -/
theorem labelled_diamond_of_diamond {n} (θ : Fin n → Parameters) {route s a b}
    (j : @Jump n route s a) (k : Jump route s b) (h : JumpDiamond route a b) :
    LabelledJumpDiamond j k := by
  rcases h with h | ⟨a',b',⟨j'⟩,⟨k'⟩,h⟩
  · left
    refine ⟨h,simultaneous_emissions_perm (T:=s.time) ?_ ?_ ?_⟩
    · intro ev he
      exact (Move.jump (θ:=θ) j).emission_time ev he
    · intro ev he
      exact (Move.jump (θ:=θ) k).emission_time ev he
    · intro i
      have hj := j.fast_potential_balance (θ:=θ) i
      have hk := k.fast_potential_balance (θ:=θ) i
      have he := observational_fastPotential h i
      simp only [Move.fireCount,Move.ledger] at hj hk
      exact_mod_cast (show
        (((j.ledger.emissions.filter (fun ev => ev.1=i)).length : ℕ) : ℝ)=
        (((k.ledger.emissions.filter (fun ev => ev.1=i)).length : ℕ) : ℝ) by linarith)
  · right
    refine ⟨a',b',j',k',h,simultaneous_emissions_perm (T:=s.time) ?_ ?_ ?_⟩
    · intro ev he
      rcases List.mem_append.mp he with he | he
      · exact (Move.jump (θ:=θ) j).emission_time ev he
      · exact ((Move.jump (θ:=θ) j').emission_time ev he).trans j.time_unchanged
    · intro ev he
      rcases List.mem_append.mp he with he | he
      · exact (Move.jump (θ:=θ) k).emission_time ev he
      · exact ((Move.jump (θ:=θ) k').emission_time ev he).trans k.time_unchanged
    · intro i
      have hj := j.fast_potential_balance (θ:=θ) i
      have hk := k.fast_potential_balance (θ:=θ) i
      have hj' := j'.fast_potential_balance (θ:=θ) i
      have hk' := k'.fast_potential_balance (θ:=θ) i
      have he := observational_fastPotential h i
      simp only [Move.fireCount,Move.ledger] at hj hk hj' hk'
      simp only [List.filter_append,List.length_append]
      exact_mod_cast (show
        (((j.ledger.emissions.filter (fun ev => ev.1=i)).length+
          (j'.ledger.emissions.filter (fun ev => ev.1=i)).length : ℕ) : ℝ)=
        (((k.ledger.emissions.filter (fun ev => ev.1=i)).length+
          (k'.ledger.emissions.filter (fun ev => ev.1=i)).length : ℕ) : ℝ) by
        push_cast
        linarith)

/-- An enabled zero-time jump occurs in every complete trace, modulo commuting
simultaneous events. Its cancellation retains all remaining actual FIREs. -/
theorem Execution.strip_initial_jump_of_diamond {n θ route}
    (hdiamond : ∀ {s a b} (j : @Jump n route s a) (k : Jump route s b),
      LabelledJumpDiamond j k)
    {s u a T} (e : @Execution n θ route s u) (hc : CompleteThrough e T)
    (j : Jump route s a) :
    ∃ b, ∃ tail : Execution θ route a b,
      u.ObservationalEq b ∧ CompleteThrough tail T ∧
      (j.ledger.emissions++tail.ledger.emissions).Perm e.ledger.emissions ∧
      tail.moveCount+1=e.moveCount := by
  induction e generalizing a with
  | nil s => exact False.elim ((hc.2.1 a).false j)
  | @cons s mid u move rest ih =>
    have hrest : CompleteThrough rest T := hc
    cases move with
    | flow f => exact False.elim ((f.no_initial_jump a).false j)
    | jump k =>
      rcases hdiamond j k with ⟨h,hlabels⟩ | ⟨a',b',j',k',h,hlabels⟩
      · obtain ⟨v,tail,hv,hem,hcount⟩ := rest.transport_observational_emissions_count h.symm
        refine ⟨v,tail,hv,completeThrough_of_observational rest tail hv hrest,?_,?_⟩
        · change (j.ledger.emissions++tail.ledger.emissions).Perm
            (k.ledger.emissions++rest.ledger.emissions)
          rw [hem]
          exact hlabels.append_right _
        · simp only [Execution.moveCount,hcount]
      · obtain ⟨v,tail,hv,hcomplete,hem,hcount⟩ := ih hrest k'
        obtain ⟨w,tail',hw,heq,hsize⟩ := tail.transport_observational_emissions_count h.symm
        let residual : Execution θ route a w := .cons (.jump j') tail'
        refine ⟨w,residual,hv.trans hw,completeThrough_of_observational tail residual hw hcomplete,?_,?_⟩
        · change (j.ledger.emissions++(j'.ledger.emissions++tail'.ledger.emissions)).Perm
            (k.ledger.emissions++rest.ledger.emissions)
          rw [heq,←List.append_assoc]
          exact (hlabels.append_right _).trans (by
            rw [List.append_assoc]
            exact hem.append_left _)
        · change tail'.moveCount+1+1=rest.moveCount+1
          omega

end KernelR.Hybrid
