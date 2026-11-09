import KernelR.HybridParameterFlowUniqueness
import KernelR.HybridParameterJumpStripping

/-! Complete finite operational executions with realized guard levels.
Positive flow heads are compared on their common interval; labelled
jump stripping handles every legal zero-time ordering. -/
namespace KernelR.Hybrid
open Set

private theorem compare_flow_heads_of_le {n θ ε route s a b u v T}
    (f : @ParameterFlow n θ s a) (g : ParameterFlow θ s b)
    (r : ParameterExecution θ route a u) (q : ParameterExecution θ route b v)
    (hb : PhysicalBox θ ε) (bounds : ParameterThresholdBounds θ) (hs : ParameterPhysicalInvariant θ s)
    (hdate : a.time≤b.time)
    (hr : ParameterCompleteThrough r T) (hq : ParameterCompleteThrough q T)
    (recur : ∀ {s' u' v'} (e : ParameterExecution θ route s' u') (f : ParameterExecution θ route s' v'),
      e.moveCount+f.moveCount<(r.moveCount+1)+(q.moveCount+1) →
      ParameterPhysicalInvariant θ s' → ParameterCompleteThrough e T → ParameterCompleteThrough f T →
      u'.ObservationalEq v' ∧ e.emissions.Perm f.emissions) :
    u.ObservationalEq v ∧ r.emissions.Perm q.emissions := by
  by_cases hlt : a.time<b.time
  · have hm : a.ObservationalEq (g.at a.time) := by
      have h := f.at_observational_unique g hb bounds hs ⟨f.positive.le,le_rfl⟩ ⟨f.positive.le,hdate⟩
      rwa [f.at_final] at h
    obtain ⟨w,r',hw,he,hcount⟩ := r.transport_observational_emissions_count hm
    let tail : ParameterExecution θ route (g.at a.time) v :=
      .cons (.flow (g.suffix f.positive.le hlt)) q
    have hsA := f.invariant_at bounds hb hs ⟨f.positive.le, le_rfl⟩
    rw [f.at_final] at hsA
    have hs' := hm.parameter_physical_invariant hsA
    have hr' := parameterCompleteThrough_of_observational r r' hw hr
    have htail : ParameterCompleteThrough tail T := hq
    obtain ⟨hf,hp⟩ := recur r' tail (by simp only [tail,ParameterExecution.moveCount]; omega) hs' hr' htail
    refine ⟨hw.trans hf,?_⟩
    simpa only [tail,ParameterExecution.emissions_cons,ParameterMove.emissions,List.nil_append,he] using hp
  · have heq : a.time=b.time := le_antisymm hdate (le_of_not_gt hlt)
    have hm := f.final_observational_unique g hb bounds hs heq
    obtain ⟨w,r',hw,he,hcount⟩ := r.transport_observational_emissions_count hm
    have hsB := g.invariant_at bounds hb hs ⟨g.positive.le, le_rfl⟩
    rw [g.at_final] at hsB
    have hr' := parameterCompleteThrough_of_observational r r' hw hr
    obtain ⟨hf,hp⟩ := recur r' q (by omega) hsB hr' hq
    exact ⟨hw.trans hf,by simpa only [he] using hp⟩

/-- For each fixed parameter choice, complete operational runs agree
at a common horizon, including the FIRE labels up to interleaving. -/
theorem ParameterExecution.observational_unique {n θ ε route T}
    (hb : @PhysicalBox n θ ε) (bounds : ParameterThresholdBounds θ)
    {s u v} (e : ParameterExecution θ route s u) (f : ParameterExecution θ route s v)
    (hs : ParameterPhysicalInvariant θ s) (he : ParameterCompleteThrough e T) (hf : ParameterCompleteThrough f T) :
    u.ObservationalEq v ∧ e.emissions.Perm f.emissions := by
  have all : ∀ k, ∀ {s u v} (e : ParameterExecution θ route s u) (f : ParameterExecution θ route s v),
      e.moveCount+f.moveCount=k → ParameterPhysicalInvariant θ s →
      ParameterCompleteThrough e T → ParameterCompleteThrough f T →
      u.ObservationalEq v ∧ e.emissions.Perm f.emissions := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro s u v e f hcount hs he hf
      cases e with
      | nil s =>
        cases f with
        | nil => exact ⟨.refl s,List.Perm.refl _⟩
        | @cons s b v move rest =>
          cases move with
          | flow g =>
            have ht := rest.time_monotone
            have h₁ := he.1
            have h₂ := hf.1
            exact False.elim (by linarith [g.positive])
          | jump j => exact False.elim ((he.2.1 b).false j)
      | @cons s a u move r =>
        cases move with
        | jump j =>
          obtain ⟨b,tail,hv,hcomplete,hperm,htail⟩ := f.strip_initial_jump bounds hf j
          have hsA := j.physical_invariant hs
          have hsmall : r.moveCount+tail.moveCount<k := by
            simp only [ParameterExecution.moveCount] at hcount
            omega
          obtain ⟨hobs,hp⟩ := ih _ hsmall r tail rfl hsA he hcomplete
          refine ⟨hobs.trans hv.symm,?_⟩
          have h := (hp.append_left j.emissions).trans hperm
          simpa only [ParameterExecution.emissions_cons,ParameterMove.emissions] using h
        | flow g =>
          cases f with
          | nil =>
            have ht := r.time_monotone
            have h₁ := he.1
            have h₂ := hf.1
            exact False.elim (by linarith [g.positive])
          | @cons s b v move q =>
            cases move with
            | jump j => exact False.elim ((g.no_initial_jump b).false j)
            | flow h =>
              have recur : ∀ {s' u' v'} (e' : ParameterExecution θ route s' u') (f' : ParameterExecution θ route s' v'),
                  e'.moveCount+f'.moveCount<(r.moveCount+1)+(q.moveCount+1) →
                  ParameterPhysicalInvariant θ s' → ParameterCompleteThrough e' T → ParameterCompleteThrough f' T →
                  u'.ObservationalEq v' ∧ e'.emissions.Perm f'.emissions := by
                intro s' u' v' e' f' hsmall hs' he' hf'
                apply ih _ (by simp only [ParameterExecution.moveCount] at hcount; omega) e' f' rfl hs' he' hf'
              by_cases hdate : a.time≤b.time
              · obtain ⟨hobs,hp⟩ := compare_flow_heads_of_le g h r q hb bounds hs hdate he hf recur
                exact ⟨hobs,by simpa only [ParameterExecution.emissions_cons,ParameterMove.emissions,List.nil_append] using hp⟩
              · have recur' : ∀ {s' u' v'} (e' : ParameterExecution θ route s' u') (f' : ParameterExecution θ route s' v'),
                    e'.moveCount+f'.moveCount<(q.moveCount+1)+(r.moveCount+1) →
                    ParameterPhysicalInvariant θ s' → ParameterCompleteThrough e' T → ParameterCompleteThrough f' T →
                    u'.ObservationalEq v' ∧ e'.emissions.Perm f'.emissions := by
                  intro s' u' v' e' f' hsmall hs' he' hf'
                  exact recur e' f' (by omega) hs' he' hf'
                obtain ⟨hobs,hp⟩ := compare_flow_heads_of_le h g q r hb bounds hs (le_of_not_ge hdate) hf he recur'
                exact ⟨hobs.symm,by simpa only [ParameterExecution.emissions_cons,ParameterMove.emissions,List.nil_append] using hp.symm⟩
  exact all _ e f rfl hs he hf

/-- Each cell's FIRE dates agree as an ordered list. -/
theorem ParameterExecution.emissionTimes_unique {n θ ε route s u v T}
    (e : @ParameterExecution n θ route s u) (f : ParameterExecution θ route s v)
    (hb : PhysicalBox θ ε) (bounds : ParameterThresholdBounds θ)
    (hs : ParameterPhysicalInvariant θ s)
    (he : ParameterCompleteThrough e T) (hf : ParameterCompleteThrough f T) (i : Fin n) :
    e.emissionTimes i = f.emissionTimes i := by
  have hp := (ParameterExecution.observational_unique hb bounds e f hs he hf).2
  exact List.Perm.eq_of_pairwise (le := fun a b : ℝ => a ≤ b)
    (fun _ _ _ _ h h' => le_antisymm h h')
    (e.emissionTimes_chronological i) (f.emissionTimes_chronological i)
    ((hp.filter _).map _)

end KernelR.Hybrid
