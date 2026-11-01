import KernelR.HybridTeachingQueueClosure
import KernelR.HybridFeedbackInitialSource
/-! Actual feedback queue closure, preserving the later B sources needed for C. -/
namespace KernelR.Hybrid

structure FeedbackQueueClosure {θ route s u} (e : @Execution 2 θ route s u)
    (later : List (Delivery 2)) : Prop where
  a_empty : u.pending.filter (fun d => d.cell = 0) = []
  b_sources : (u.pending.filter (fun d => d.cell = 1)).Perm later

/-- The real feedback sender bounds every token routed to A strictly before
459.9. B consumes exactly its first source train and retains all later sources
with multiplicity. No received calendar or output count is assumed here. -/
theorem Execution.feedback_queue_closure {θ s u} (forward backward : ℝ → ℝ)
    (e : @Execution 2 θ (reciprocalEntryRouter forward backward) s u)
    (sender : FeedbackSender e) (later : List (Delivery 2))
    (hAempty : s.pending.filter (fun d => d.cell = 0) = [])
    (hBqueue : (s.pending.filter (fun d => d.cell = 1)).Perm (sourceTrain 1 2 320 8 16 ++ later))
    (hlater : ∀ d ∈ later, u.time < d.due)
    (ht : s.time = 3199 / 10) (hu : u.time = 4599 / 10) (hpf : PendingFuture u)
    (hrestUpper : restLatency (Real.exp (s.x 1 (.z 2) + 9 / 5)) < 9 / 10)
    (hbackward : ∀ t, backward t ≤ 2 / 5) : FeedbackQueueClosure e later := by
  have htime : ∀ event ∈ e.ledger.emissions, 310 ≤ event.2 := by
    intro event he
    have h := (e.emission_time_bounds event he).1
    rw [ht] at h
    linarith
  have hclosedB : ∀ event ∈ e.ledger.emissions,
      ∀ d ∈ reciprocalEntryRouter forward backward event.1 event.2, d.cell ≠ 1 := by
    intro event he
    exact reciprocalEntryRouter.closed_to_b forward backward event.1 (htime event he)
  have hpast : ∀ d ∈ sourceTrain (1 : Fin 2) 2 320 8 16, d.due < u.time := by
    intro d hd
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hd
    have hk : (k.val : ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
    rw [hu]
    change 320 + 8 * (k.val : ℝ) < 4599 / 10
    linarith
  have hdelB := e.cell_deliveries_due_prefix 1 (sourceTrain 1 2 320 8 16) later hBqueue hpast hlater hpf hclosedB
  have hremainB := e.cell_pending_perm_of_prefix 1 (sourceTrain 1 2 320 8 16) later hBqueue hdelB hclosedB
  have hsourceA : ∀ d ∈ s.pending, d.cell = 0 → d.due < u.time := by
    intro d hd hc
    have hm : d ∈ s.pending.filter (fun d => d.cell = 0) := by
      simp only [List.mem_filter,decide_eq_true_eq]
      exact ⟨hd,hc⟩
    rw [hAempty] at hm
    contradiction
  have hroutedA : ∀ event ∈ e.ledger.emissions,
      ∀ d ∈ reciprocalEntryRouter forward backward event.1 event.2, d.cell = 0 → d.due < u.time := by
    intro event he d hd _
    rw [reciprocalEntryRouter.after_forward forward backward event.1 (htime event he)] at hd
    unfold Contact.route at hd
    split_ifs at hd with h
    · simp only [List.mem_singleton] at hd
      subst d
      have hcell : event.1 = (1 : Fin 2) := h.1
      have hm : event.2 ∈ e.emissionTimes 1 := by
        apply List.mem_map.mpr
        exact ⟨event,by simp [List.mem_filter,he,hcell],rfl⟩
      rw [sender.emissions] at hm
      have hbound : event.2 < 4409 / 10 := by
        rcases List.mem_cons.mp hm with hm | hm
        · rw [hm]
          linarith [sender.first_upper]
        · obtain ⟨k,hk⟩ := List.mem_ofFn.mp hm
          rw [← hk]
          have hval : (k.val : ℝ) ≤ 11 := by exact_mod_cast (show k.val ≤ 11 by omega)
          linarith
      change event.2 + backward event.2 < u.time
      rw [hu]
      linarith [hbackward event.2]
    · contradiction
  exact ⟨e.cell_pending_empty_strict 0 hpf hsourceA hroutedA,hremainB⟩

end KernelR.Hybrid
