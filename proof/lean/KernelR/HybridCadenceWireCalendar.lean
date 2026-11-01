import KernelR.HybridCadenceRouter
/-! Derive actual cadence receiving calendars from actual sending emissions. -/
namespace KernelR.Hybrid

theorem Contact.jittered_order {n} (c : Contact n) (times : List ℝ)
    (hs : times.Pairwise (fun t v => t + 1 / 10 ≤ v))
    (hd : ∀ t, 3 / 10 ≤ c.delay t ∧ c.delay t ≤ 2 / 5) :
    (times.map c.token).Pairwise (fun d f => d.due ≤ f.due) := by
  apply List.pairwise_map.mpr
  apply hs.imp
  intro t v hgap
  dsimp [Contact.token]
  linarith [(hd t).2,(hd v).1]

/-- A contact's receiving list follows from real emissions, with fresh jitter
and empty initial target queue. Its local order is proved from separated
sending dates rather than presumed from the source's or receiver's clock. -/
theorem Execution.cadence_contact_calendar {θ route s u} (e : @Execution 3 θ route s u)
    (c : Contact 3) (times : List ℝ)
    (hs : e.emissionTimes c.source = times)
    (hspace : times.Pairwise (fun t v => t + 1 / 10 ≤ v))
    (hgate : ∀ t ∈ times, c.opens ≤ t ∧ t < c.closes)
    (hclose : c.closes ≤ 780) (hu : u.time = 7899 / 10) (hpf : PendingFuture u)
    (hqueue : s.pending.filter (fun d => d.cell = c.target) = [])
    (hwire : ∀ event ∈ e.ledger.emissions,
      (route event.1 event.2).filter (fun d => d.cell = c.target) = c.route event.1 event.2)
    (hdelay : ∀ t, 3 / 10 ≤ c.delay t ∧ c.delay t ≤ 2 / 5) :
    e.cellDeliveries c.target = times.map c.token := by
  have hselected : (e.emissionTimes c.source).filter (fun t => c.opens ≤ t ∧ t < c.closes) = times := by
    rw [hs]
    apply List.filter_eq_self.mpr
    intro t ht
    exact decide_eq_true (hgate t ht)
  have hfuture : ∀ d ∈ s.pending, d.cell = c.target → u.time < d.due := by
    intro d hd hc
    have hm : d ∈ s.pending.filter (fun d => d.cell = c.target) := by
      simp only [List.mem_filter,decide_eq_true_eq]
      exact ⟨hd,hc⟩
    rw [hqueue] at hm
    contradiction
  have hdue : ∀ t ∈ e.emissionTimes c.source,
      c.opens ≤ t → t < c.closes → (c.token t).due < u.time := by
    intro t _ _ ht
    dsimp [Contact.token]
    rw [hu]
    linarith [(hdelay t).2]
  have horder : (((e.emissionTimes c.source).filter
      (fun t => c.opens ≤ t ∧ t < c.closes)).map c.token).Pairwise (fun d f => d.due ≤ f.due) := by
    rw [hselected]
    exact c.jittered_order times hspace hdelay
  rw [e.contact_deliveries c hpf hfuture hwire hdue horder,hselected]

theorem Execution.cadence_forward_calendar {θ s u} (forward backward : ℝ → ℝ)
    (e : @Execution 3 θ (cadenceRouter forward backward) s u) (times : List ℝ)
    (hs : e.emissionTimes 2 = times)
    (hspace : times.Pairwise (fun t v => t + 1 / 10 ≤ v))
    (hgate : ∀ t ∈ times, 640 ≤ t ∧ t < 780)
    (hu : u.time = 7899 / 10) (hpf : PendingFuture u)
    (hqueue : s.pending.filter (fun d => d.cell = 1) = [])
    (hdelay : ∀ t, 3 / 10 ≤ forward t ∧ forward t ≤ 2 / 5) :
    e.cellDeliveries 1 = times.map (cadenceForwardContact forward).token := by
  exact e.cadence_contact_calendar (cadenceForwardContact forward) times hs hspace hgate
    (by norm_num [cadenceForwardContact]) hu hpf hqueue
    (fun event _ => cadenceRouter.to_b forward backward event.1 event.2) hdelay

theorem Execution.cadence_return_calendar {θ s u} (forward backward : ℝ → ℝ)
    (e : @Execution 3 θ (cadenceRouter forward backward) s u) (times : List ℝ)
    (hs : e.emissionTimes 1 = times)
    (hspace : times.Pairwise (fun t v => t + 1 / 10 ≤ v))
    (hgate : ∀ t ∈ times, 640 ≤ t ∧ t < 780)
    (hu : u.time = 7899 / 10) (hpf : PendingFuture u)
    (hqueue : s.pending.filter (fun d => d.cell = 0) = [])
    (hdelay : ∀ t, 3 / 10 ≤ backward t ∧ backward t ≤ 2 / 5) :
    e.cellDeliveries 0 = times.map (cadenceReturnContact backward).token := by
  exact e.cadence_contact_calendar (cadenceReturnContact backward) times hs hspace hgate
    (by norm_num [cadenceReturnContact]) hu hpf hqueue
    (fun event _ => cadenceRouter.to_a forward backward event.1 event.2) hdelay

end KernelR.Hybrid
