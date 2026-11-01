import KernelR.HybridTeachingQueueClosure
import KernelR.HybridCTeachingRouter
/-! Preserve C's external sources after its actual B-to-C teaching epoch. -/
namespace KernelR.Hybrid

structure CIntroductionQueueClosure {θ route s u} (e : @Execution 3 θ route s u) : Prop where
  a_empty : u.pending.filter (fun d => d.cell = 0) = []
  b_empty : u.pending.filter (fun d => d.cell = 1) = []
  c_sources : (u.pending.filter (fun d => d.cell = 2)).Perm
    (s.pending.filter (fun d => d.cell = 2))

/-- All source tokens on B and all routed teaching tokens are strictly past
the endpoint. C's future sources remain with their complete multiplicities. -/
theorem Execution.c_introduction_queue_closure {θ s u} (delay : ℝ → ℝ)
    (e : @Execution 3 θ (cTeachingRouter delay) s u)
    (hpf : PendingFuture u) (hu : u.time = 6399 / 10)
    (hAempty : s.pending.filter (fun d => d.cell = 0) = [])
    (hBpast : ∀ d ∈ s.pending, d.cell = 1 → d.due < u.time)
    (hCfuture : ∀ d ∈ s.pending, d.cell = 2 → u.time < d.due)
    (hd : ∀ t, delay t ≤ 2 / 5) : CIntroductionQueueClosure e := by
  have hApast : ∀ d ∈ s.pending, d.cell = 0 → d.due < u.time := by
    intro d hm hc
    have h : d ∈ s.pending.filter (fun d => d.cell = 0) := by
      simp only [List.mem_filter,decide_eq_true_eq]
      exact ⟨hm,hc⟩
    rw [hAempty] at h
    contradiction
  have hroute : ∀ event ∈ e.ledger.emissions, ∀ d ∈ cTeachingRouter delay event.1 event.2,
      d.cell = 2 → d.due < u.time := by
    intro event _ d hm _
    change d ∈ (cTeachingContact delay).route event.1 event.2 at hm
    unfold Contact.route at hm
    split_ifs at hm with h
    · simp only [List.mem_singleton] at hm
      subst d
      have ht : event.2 < (630 : ℝ) := h.2.2
      change event.2 + delay event.2 < u.time
      rw [hu]
      linarith [hd event.2]
    · contradiction
  have hA := e.cell_pending_empty_strict 0 hpf hApast
    (fun event _ d hm hc => False.elim (cTeachingRouter.closed_to_a delay event.1 event.2 d hm hc))
  have hB := e.cell_pending_empty_strict 1 hpf hBpast
    (fun event _ d hm hc => False.elim (cTeachingRouter.closed_to_b delay event.1 event.2 d hm hc))
  have hdel := e.cell_deliveries_perm_issued 2 hpf hCfuture hroute
  exact ⟨hA,hB,e.cell_pending_perm_of_routed_balance 2 hdel⟩

end KernelR.Hybrid
