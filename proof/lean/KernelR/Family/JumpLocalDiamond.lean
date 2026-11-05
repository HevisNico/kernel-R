import KernelR.Family.JumpConfluence
import KernelR.Family.JumpDepartures

/-! Every pair of enabled operational jumps has a local observational diamond.
All nine constructors are covered, including simultaneous deliveries and
RAW expiries; no event-priority or causal-router hypothesis is introduced. -/
namespace KernelR.Family
open KernelR.Hybrid

theorem JumpDiamond.symm {n c route} {u v : Snapshot n}
    (h : @JumpDiamond n c route u v) : JumpDiamond c route v u := by
  rcases h with h | ⟨u',v',hu,hv,h⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨v',u',hv,hu,h.symm⟩

/-- Legal simultaneous operational choices commute up to token-list order.
The two branches may already agree, or each can take one further real jump
to physically identical observations with permutation-equivalent queues. -/
theorem Jump.local_diamond {n c route s a b} (j : @Jump n c route s a)
    (k : Jump c route s b) : JumpDiamond c route a b := by
  cases j with
  | fire i hm hg =>
    by_cases h : b.main i=s.main i
    · exact k.fire_diamond_of_unchanged i hm hg h
    · rw [k.eq_fire_of_main_changed i hm h]
      exact Or.inl (.refl _)
  | fastEnd i hm hg =>
    by_cases h : b.main i=s.main i
    · exact k.fastEnd_diamond_of_unchanged i hm hg h
    · rw [k.eq_fastEnd_of_main_changed i hm h]
      exact Or.inl (.refl _)
  | reopen i hm hg =>
    by_cases h : b.main i=s.main i
    · exact k.reopen_diamond_of_unchanged i hm hg h
    · rw [k.eq_reopen_of_main_changed i hm h]
      exact Or.inl (.refl _)
  | mark i p hm hg =>
    by_cases h : b.aux i p=s.aux i p
    · exact k.mark_diamond_of_unchanged i p hm hg h
    · rw [k.eq_mark_of_aux_changed i p hm h]
      exact Or.inl (.refl _)
  | silent i p hm hg =>
    by_cases h : b.aux i p=s.aux i p
    · exact k.silent_diamond_of_unchanged i p hm hg h
    · rw [k.eq_silent_of_aux_changed i p hm h]
      exact Or.inl (.refl _)
  | error i p hm hg =>
    by_cases h : b.aux i p=s.aux i p
    · exact k.error_diamond_of_unchanged i p hm hg h
    · rw [k.eq_error_of_aux_changed i p hm h]
      exact Or.inl (.refl _)
  | auxReady i p hm hg =>
    by_cases h : b.aux i p=s.aux i p
    · exact k.auxReady_diamond_of_unchanged i p hm hg h
    · rw [k.eq_auxReady_of_aux_changed i p hm h]
      exact Or.inl (.refl _)
  | arrive d before after queue due free =>
    let ja := Jump.arrive (c:=c) (route:=route) s d before after queue due free
    cases k with
    | fire i hm hg =>
      exact (ja.fire_diamond_of_unchanged i hm hg rfl).symm
    | fastEnd i hm hg =>
      exact (ja.fastEnd_diamond_of_unchanged i hm hg rfl).symm
    | reopen i hm hg =>
      exact (ja.reopen_diamond_of_unchanged i hm hg rfl).symm
    | mark i p hm hg =>
      exact (ja.mark_diamond_of_unchanged i p hm hg rfl).symm
    | silent i p hm hg =>
      exact (ja.silent_diamond_of_unchanged i p hm hg rfl).symm
    | error i p hm hg =>
      exact (ja.error_diamond_of_unchanged i p hm hg rfl).symm
    | auxReady i p hm hg =>
      exact (ja.auxReady_diamond_of_unchanged i p hm hg rfl).symm
    | arrive e before' after' queue' due' free' =>
      exact arrive_arrive_diamond s d e before after before' after'
        queue queue' due due' free free'
    | rawEnd i p o active expiry =>
      exact arrive_rawEnd_diamond s d before after queue due free i p o active expiry
  | rawEnd i p o active expiry =>
    let jr := Jump.rawEnd (c:=c) (route:=route) s i p o active expiry
    cases k with
    | fire k hm hg =>
      exact (jr.fire_diamond_of_unchanged k hm hg rfl).symm
    | fastEnd k hm hg =>
      exact (jr.fastEnd_diamond_of_unchanged k hm hg rfl).symm
    | reopen k hm hg =>
      exact (jr.reopen_diamond_of_unchanged k hm hg rfl).symm
    | mark k q hm hg =>
      exact (jr.mark_diamond_of_unchanged k q hm hg rfl).symm
    | silent k q hm hg =>
      exact (jr.silent_diamond_of_unchanged k q hm hg rfl).symm
    | error k q hm hg =>
      exact (jr.error_diamond_of_unchanged k q hm hg rfl).symm
    | auxReady k q hm hg =>
      exact (jr.auxReady_diamond_of_unchanged k q hm hg rfl).symm
    | arrive d before after queue due free =>
      exact (arrive_rawEnd_diamond s d before after queue due free i p o active expiry).symm
    | rawEnd k q r active' expiry' =>
      exact rawEnd_rawEnd_diamond s i k p q o r active active' expiry expiry'

#print axioms Jump.local_diamond

end KernelR.Family
