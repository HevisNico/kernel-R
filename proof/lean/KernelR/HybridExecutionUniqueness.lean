import KernelR.HybridFlowUniqueness
import KernelR.HybridObservationalTransport
import KernelR.HybridFlowCuts
import KernelR.HybridUrgentMoves

/-! Observational comparison of complete finite executions. Positive flows are
aligned by their actual overlap; simultaneous jumps are handled by the proved
initial-jump stripping property, independently of a chosen event ordering. -/
namespace KernelR.Hybrid
open Set

private theorem compare_flow_heads_of_le {n θ ε route s a b u v T}
    (f : @Flow n θ s a) (g : Flow θ s b)
    (r : Execution θ route a u) (q : Execution θ route b v)
    (hb : PhysicalBox θ ε) (hs : PhysicalInvariant θ s)
    (hdate : a.time≤b.time)
    (hr : CompleteThrough r T) (hq : CompleteThrough q T)
    (recur : ∀ {s' u' v'} (e : Execution θ route s' u') (f : Execution θ route s' v'),
      e.moveCount+f.moveCount<(r.moveCount+1)+(q.moveCount+1) →
      PhysicalInvariant θ s' → CompleteThrough e T → CompleteThrough f T →
      u'.ObservationalEq v' ∧ e.ledger.emissions.Perm f.ledger.emissions) :
    u.ObservationalEq v ∧ r.ledger.emissions.Perm q.ledger.emissions := by
  by_cases hlt : a.time<b.time
  · have hm : a.ObservationalEq (g.at a.time) := by
      have h := f.at_observational_unique g hb hs ⟨f.positive.le,le_rfl⟩ ⟨f.positive.le,hdate⟩
      rwa [f.at_final] at h
    obtain ⟨w,r',hw,he,hcount⟩ := r.transport_observational_emissions_count hm
    let tail : Execution θ route (g.at a.time) v :=
      .cons (.flow (g.suffix f.positive.le hlt)) q
    have hsA : PhysicalInvariant θ a :=
      (Execution.cons (.flow f) (.nil a) : Execution θ route s a).physical_invariant hb hs
    have hs' := hm.physical_invariant hsA
    have hr' := completeThrough_of_observational r r' hw hr
    have htail : CompleteThrough tail T := hq
    obtain ⟨hf,hp⟩ := recur r' tail (by simp only [tail,Execution.moveCount]; omega) hs' hr' htail
    refine ⟨hw.trans hf,?_⟩
    simpa only [tail,Execution.ledger,Move.ledger,Flow.ledger,Ledger.add,Ledger.zero,List.nil_append,he] using hp
  · have heq : a.time=b.time := le_antisymm hdate (le_of_not_gt hlt)
    have hm := f.final_observational_unique g hb hs heq
    obtain ⟨w,r',hw,he,hcount⟩ := r.transport_observational_emissions_count hm
    have hsB : PhysicalInvariant θ b :=
      (Execution.cons (.flow g) (.nil b) : Execution θ route s b).physical_invariant hb hs
    have hr' := completeThrough_of_observational r r' hw hr
    obtain ⟨hf,hp⟩ := recur r' q (by omega) hsB hr' hq
    exact ⟨hw.trans hf,by simpa only [he] using hp⟩

/-- Complete finite traces have one physical endpoint and the same FIRE multiset
once each enabled initial jump can be stripped through a competing trace.
The stripping argument is instantiated from the operational jump confluence
lemmas, rather than assumed by the final protocol headline. -/
theorem Execution.observational_unique_of_strip {n θ ε route T}
    (hb : @PhysicalBox n θ ε)
    (strip : ∀ {s u a} (e : Execution θ route s u) (_hc : CompleteThrough e T)
      (j : Jump route s a),
      ∃ b, ∃ tail : Execution θ route a b,
        u.ObservationalEq b ∧ CompleteThrough tail T ∧
        (j.ledger.emissions++tail.ledger.emissions).Perm e.ledger.emissions ∧
        tail.moveCount+1=e.moveCount)
    {s u v} (e : Execution θ route s u) (f : Execution θ route s v)
    (hs : PhysicalInvariant θ s) (he : CompleteThrough e T) (hf : CompleteThrough f T) :
    u.ObservationalEq v ∧ e.ledger.emissions.Perm f.ledger.emissions := by
  have all : ∀ k, ∀ {s u v} (e : Execution θ route s u) (f : Execution θ route s v),
      e.moveCount+f.moveCount=k → PhysicalInvariant θ s →
      CompleteThrough e T → CompleteThrough f T →
      u.ObservationalEq v ∧ e.ledger.emissions.Perm f.ledger.emissions := by
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
          obtain ⟨b,tail,hv,hcomplete,hperm,htail⟩ := strip f hf j
          have hsA : PhysicalInvariant θ a :=
            (Execution.cons (.jump j) (.nil a) : Execution θ route s a).physical_invariant hb hs
          have hsmall : r.moveCount+tail.moveCount<k := by
            simp only [Execution.moveCount] at hcount
            omega
          obtain ⟨hobs,hp⟩ := ih _ hsmall r tail rfl hsA he hcomplete
          refine ⟨hobs.trans hv.symm,?_⟩
          have h := (hp.append_left j.ledger.emissions).trans hperm
          simpa only [Execution.ledger,Move.ledger,Flow.ledger,Ledger.add] using h
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
              have recur : ∀ {s' u' v'} (e' : Execution θ route s' u') (f' : Execution θ route s' v'),
                  e'.moveCount+f'.moveCount<(r.moveCount+1)+(q.moveCount+1) →
                  PhysicalInvariant θ s' → CompleteThrough e' T → CompleteThrough f' T →
                  u'.ObservationalEq v' ∧ e'.ledger.emissions.Perm f'.ledger.emissions := by
                intro s' u' v' e' f' hsmall hs' he' hf'
                apply ih _ (by simp only [Execution.moveCount] at hcount; omega) e' f' rfl hs' he' hf'
              by_cases hdate : a.time≤b.time
              · obtain ⟨hobs,hp⟩ := compare_flow_heads_of_le g h r q hb hs hdate he hf recur
                exact ⟨hobs,by simpa only [Execution.ledger,Move.ledger,Flow.ledger,Ledger.add,Ledger.zero,List.nil_append] using hp⟩
              · have recur' : ∀ {s' u' v'} (e' : Execution θ route s' u') (f' : Execution θ route s' v'),
                    e'.moveCount+f'.moveCount<(q.moveCount+1)+(r.moveCount+1) →
                    PhysicalInvariant θ s' → CompleteThrough e' T → CompleteThrough f' T →
                    u'.ObservationalEq v' ∧ e'.ledger.emissions.Perm f'.ledger.emissions := by
                  intro s' u' v' e' f' hsmall hs' he' hf'
                  exact recur e' f' (by omega) hs' he' hf'
                obtain ⟨hobs,hp⟩ := compare_flow_heads_of_le h g q r hb hs (le_of_not_ge hdate) hf he recur'
                exact ⟨hobs.symm,by simpa only [Execution.ledger,Move.ledger,Flow.ledger,Ledger.add,Ledger.zero,List.nil_append] using hp.symm⟩
  exact all _ e f rfl hs he hf

#print axioms Execution.observational_unique_of_strip
end KernelR.Hybrid
